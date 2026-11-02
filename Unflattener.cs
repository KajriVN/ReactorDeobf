// Control-flow unflattening for .NET Reactor state-machine dispatchers (part of ReactorDeobf).
//
// Reactor flattens methods into a switch dispatcher. Each real block pushes the next state on the
// EVALUATION STACK (often through an opaque `brfalse` that keeps or replaces it) and jumps straight
// into the `switch`, or stores it in a local and jumps to `ldloc; switch`.
//
// Approach: jump threading over a CFG.
//   1. Basic blocks, entry stack depths, forward constant propagation over primitive locals,
//      backward liveness over all locals (handlers count as successors of their try blocks).
//   2. For each edge B -> D: take B's exit state (locals + evaluation stack) and simulate the "pure"
//      dispatcher blocks from D. A pure block only does constant arithmetic, loads/stores of KNOWN values,
//      pops, and branches whose outcome is decided. Stop at the first non-pure block T.
//   3. The path is accepted if, at T, the stack is: B's untouched items (bottom) + known constants (top).
//      The edge is redirected to T with a replay: pop x consumed, ldc each new constant, ldc/stloc each
//      local the dispatcher changed that is live at T, br T. Conditional/switch edges that need a replay go
//      through a trampoline placed after an unconditional instruction in the same EH region.
//   4. Iterate to a fixpoint, then remove unreachable blocks, dead stores and `ldc/ldloc; pop` pairs.
// Every edit is semantics-preserving: the skipped instructions are side-effect free and fully determined.
using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

static class Unflattener
{
    sealed class Block
    {
        public Instruction First, Last;
        public int S, E;
        public List<Block> Succ = new List<Block>();
        public List<Block> LiveSucc = new List<Block>();
        public string Region;
        public bool Reachable;
        public int DepthIn = -1;
        public int?[] In;
        public HashSet<int> LiveIn = new HashSet<int>(), LiveOut = new HashSet<int>();
    }

    sealed class Cfg
    {
        public List<Block> Blocks = new List<Block>();
        public Dictionary<Instruction, Block> ByFirst = new Dictionary<Instruction, Block>();
        public Block[] ByIndex;
        public string[] RegionOf;
        public Dictionary<Instruction, int> Index = new Dictionary<Instruction, int>();
        public HashSet<Instruction> EhRefs = new HashSet<Instruction>();
        public bool[] Tracked;
    }

    struct SItem { public int? V; public bool FromB; }   // FromB = item already on the stack when B ended

    public static int Edges, Removed, DeadStores;

    public static void Run(MethodDef m)
    {
        var body = m.Body;
        if (body == null || body.Instructions.Count < 4) return;
        for (int iter = 0; iter < 80; iter++)
        {
            var g = Build(body);
            Analyse(g, body);
            int edits = Thread(g, body);
            Edges += edits;
            if (edits == 0)
            {
                int r = RemoveUnreachable(g, body);
                g = Build(body); Analyse(g, body);
                int d = DeadStoreElim(g, body) + Peephole(g, body);
                Removed += r; DeadStores += d;
                if (r == 0 && d == 0) return;
            }
        }
        // iteration cap reached: still clean up so no unreachable junk is left behind
        for (int k = 0; k < 4; k++)
        {
            var g = Build(body); Analyse(g, body);
            int r = RemoveUnreachable(g, body);
            g = Build(body); Analyse(g, body);
            int d = DeadStoreElim(g, body) + Peephole(g, body);
            Removed += r; DeadStores += d;
            if (r == 0 && d == 0) break;
        }
    }

    // ------------------------------------------------------------------ CFG
    static bool EndsBlock(Instruction i)
    {
        var fc = i.OpCode.FlowControl;
        return fc == FlowControl.Branch || fc == FlowControl.Cond_Branch || fc == FlowControl.Return || fc == FlowControl.Throw
            || i.OpCode.Code == Code.Leave || i.OpCode.Code == Code.Endfinally || i.OpCode.Code == Code.Rethrow || i.OpCode.Code == Code.Endfilter;
    }
    static bool Unconditional(Instruction i)
    {
        var c = i.OpCode.Code;
        return c == Code.Br || c == Code.Leave || c == Code.Ret || c == Code.Throw || c == Code.Rethrow || c == Code.Endfinally;
    }

    static Cfg Build(CilBody body)
    {
        var g = new Cfg(); var ins = body.Instructions; int n = ins.Count;
        for (int i = 0; i < n; i++) g.Index[ins[i]] = i;
        var lead = new bool[n]; lead[0] = true;
        for (int i = 0; i < n; i++)
        {
            var x = ins[i];
            if (x.Operand is Instruction) lead[g.Index[(Instruction)x.Operand]] = true;
            if (x.Operand is Instruction[]) foreach (var t in (Instruction[])x.Operand) lead[g.Index[t]] = true;
            if (EndsBlock(x) && i + 1 < n) lead[i + 1] = true;
        }
        foreach (var eh in body.ExceptionHandlers)
            foreach (var t in new[] { eh.TryStart, eh.TryEnd, eh.HandlerStart, eh.HandlerEnd, eh.FilterStart })
                if (t != null) { g.EhRefs.Add(t); int k; if (g.Index.TryGetValue(t, out k)) lead[k] = true; }

        g.RegionOf = new string[n];
        for (int i = 0; i < n; i++) g.RegionOf[i] = "";
        int ehi = 0;
        foreach (var eh in body.ExceptionHandlers)
        {
            int ts = Idx(g, eh.TryStart, n), te = Idx(g, eh.TryEnd, n), hs = Idx(g, eh.HandlerStart, n), he = Idx(g, eh.HandlerEnd, n);
            int fs = eh.FilterStart == null ? -1 : Idx(g, eh.FilterStart, n);
            for (int i = ts; i < te; i++) g.RegionOf[i] += "t" + ehi + ";";
            for (int i = hs; i < he; i++) g.RegionOf[i] += "h" + ehi + ";";
            if (fs >= 0) for (int i = fs; i < hs; i++) g.RegionOf[i] += "f" + ehi + ";";
            ehi++;
        }

        g.ByIndex = new Block[n];
        for (int i = 0; i < n; )
        {
            int j = i + 1; while (j < n && !lead[j]) j++;
            var b = new Block { S = i, E = j - 1, First = ins[i], Last = ins[j - 1], Region = g.RegionOf[i] };
            g.Blocks.Add(b); g.ByFirst[b.First] = b;
            for (int k = i; k < j; k++) g.ByIndex[k] = b;
            i = j;
        }
        foreach (var b in g.Blocks)
        {
            var l = b.Last; var c = l.OpCode.Code;
            Block next = b.E + 1 < n ? g.ByIndex[b.E + 1] : null;
            if (l.OpCode.FlowControl == FlowControl.Branch || c == Code.Leave) b.Succ.Add(g.ByFirst[(Instruction)l.Operand]);
            else if (l.OpCode.FlowControl == FlowControl.Cond_Branch)
            {
                if (l.Operand is Instruction[]) foreach (var t in (Instruction[])l.Operand) b.Succ.Add(g.ByFirst[t]);
                else b.Succ.Add(g.ByFirst[(Instruction)l.Operand]);
                if (next != null) b.Succ.Add(next);
            }
            else if (!(l.OpCode.FlowControl == FlowControl.Return || l.OpCode.FlowControl == FlowControl.Throw
                    || c == Code.Endfinally || c == Code.Rethrow || c == Code.Endfilter) && next != null) b.Succ.Add(next);
            b.LiveSucc.AddRange(b.Succ);
        }
        foreach (var eh in body.ExceptionHandlers)
        {
            int ts = Idx(g, eh.TryStart, n), te = Idx(g, eh.TryEnd, n);
            var hb = g.ByFirst.ContainsKey(eh.HandlerStart) ? g.ByFirst[eh.HandlerStart] : null;
            var fb = eh.FilterStart != null && g.ByFirst.ContainsKey(eh.FilterStart) ? g.ByFirst[eh.FilterStart] : null;
            foreach (var b in g.Blocks.Where(b => b.S >= ts && b.S < te)) { if (hb != null) b.LiveSucc.Add(hb); if (fb != null) b.LiveSucc.Add(fb); }
        }

        // reachability + entry stack depths
        var work = new Stack<Block>();
        g.Blocks[0].DepthIn = 0; work.Push(g.Blocks[0]);
        foreach (var eh in body.ExceptionHandlers)
        {
            if (g.ByFirst.ContainsKey(eh.HandlerStart))
            {
                var hb = g.ByFirst[eh.HandlerStart];
                hb.DepthIn = eh.HandlerType == ExceptionHandlerType.Catch || eh.HandlerType == ExceptionHandlerType.Filter ? 1 : 0;
                work.Push(hb);
            }
            if (eh.FilterStart != null && g.ByFirst.ContainsKey(eh.FilterStart)) { var fb = g.ByFirst[eh.FilterStart]; fb.DepthIn = 1; work.Push(fb); }
        }
        while (work.Count > 0)
        {
            var b = work.Pop(); if (b.Reachable) continue; b.Reachable = true;
            int d = b.DepthIn < 0 ? 0 : b.DepthIn;
            for (int k = b.S; k <= b.E; k++)
            {
                int pushes, pops; ins[k].CalculateStackUsage(false, out pushes, out pops);
                if (pops < 0) d = 0; else d = Math.Max(0, d - pops) + pushes;
            }
            foreach (var s in b.Succ) { if (s.DepthIn < 0) s.DepthIn = b.Last.OpCode.Code == Code.Leave ? 0 : d; work.Push(s); }
            foreach (var s in b.LiveSucc) if (!b.Succ.Contains(s)) work.Push(s);
        }

        var vars = body.Variables; g.Tracked = new bool[vars.Count];
        for (int v = 0; v < vars.Count; v++)
        {
            var et = vars[v].Type.RemovePinnedAndModifiers().ElementType;
            g.Tracked[v] = et == ElementType.I4 || et == ElementType.U4 || et == ElementType.Boolean || et == ElementType.I2 || et == ElementType.U2
                        || et == ElementType.I1 || et == ElementType.U1 || et == ElementType.Char;
        }
        foreach (var x in body.Instructions)
            if (x.OpCode.Code == Code.Ldloca || x.OpCode.Code == Code.Ldloca_S) { var lv = x.Operand as Local; if (lv != null) g.Tracked[lv.Index] = false; }
        return g;
    }

    static int Idx(Cfg g, Instruction i, int n) { int k; return i == null ? n : g.Index.TryGetValue(i, out k) ? k : n; }

    // ------------------------------------------------------------------ simulation
    // Simulates block b on (locals st, stack). pureMode demands only side-effect-free, fully determined work.
    // Returns the decided successor instruction (null = not decided / no successor).
    static Instruction Sim(Cfg g, CilBody body, Block b, int?[] st, List<SItem> stack, bool pureMode, out bool pure)
    {
        pure = true; var ins = body.Instructions; bool ok = true;
        Func<SItem> pop = () =>
        {
            if (stack.Count == 0) { ok = false; return new SItem(); }
            var v = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1); return v;
        };
        Action<int?> push = v => stack.Add(new SItem { V = v });
        Instruction result = null; bool decided = false;
        for (int k = b.S; k <= b.E; k++)
        {
            var x = ins[k]; var c = x.OpCode.Code;
            if (x.IsLdcI4()) { push(x.GetLdcI4Value()); continue; }
            if (x.IsLdloc())
            {
                var lv = x.GetLocal(body.Variables);
                bool tr = lv != null && g.Tracked[lv.Index];
                push(tr ? st[lv.Index] : null);
                if (!tr) pure = false;
                continue;
            }
            if (x.IsStloc())
            {
                var lv = x.GetLocal(body.Variables); var v = pop();
                bool tr = lv != null && g.Tracked[lv.Index];
                if (tr) st[lv.Index] = v.V;
                if (!tr || !v.V.HasValue) pure = false;
                continue;
            }
            switch (c)
            {
                case Code.Nop: continue;
                case Code.Pop: pop(); continue;
                case Code.Add: case Code.Sub: case Code.Mul: case Code.And: case Code.Or: case Code.Xor:
                case Code.Shl: case Code.Shr: case Code.Shr_Un: case Code.Div: case Code.Div_Un: case Code.Rem: case Code.Rem_Un:
                case Code.Ceq: case Code.Cgt: case Code.Cgt_Un: case Code.Clt: case Code.Clt_Un:
                {
                    var bb = pop(); var aa = pop(); int? r = null;
                    if (aa.V.HasValue && bb.V.HasValue) r = Bin(c, aa.V.Value, bb.V.Value);
                    if (!r.HasValue) pure = false;
                    push(r); continue;
                }
                case Code.Not: case Code.Neg:
                {
                    var aa = pop();
                    push(aa.V.HasValue ? (int?)(c == Code.Not ? ~aa.V.Value : unchecked(-aa.V.Value)) : null);
                    if (!aa.V.HasValue) pure = false; continue;
                }
                case Code.Conv_I4: case Code.Conv_U4: { var aa = pop(); push(aa.V); continue; }
                case Code.Br: result = (Instruction)x.Operand; decided = true; break;
                case Code.Brtrue: case Code.Brfalse:
                {
                    var aa = pop();
                    if (!aa.V.HasValue) { pure = false; break; }
                    bool taken = (aa.V.Value != 0) == (c == Code.Brtrue);
                    result = taken ? (Instruction)x.Operand : (k + 1 < ins.Count ? ins[k + 1] : null); decided = true; break;
                }
                case Code.Beq: case Code.Bne_Un: case Code.Blt: case Code.Blt_Un: case Code.Bgt: case Code.Bgt_Un:
                case Code.Ble: case Code.Ble_Un: case Code.Bge: case Code.Bge_Un:
                {
                    var bb = pop(); var aa = pop();
                    if (!aa.V.HasValue || !bb.V.HasValue) { pure = false; break; }
                    result = Cmp(c, aa.V.Value, bb.V.Value) ? (Instruction)x.Operand : (k + 1 < ins.Count ? ins[k + 1] : null); decided = true; break;
                }
                case Code.Switch:
                {
                    var aa = pop(); var tg = (Instruction[])x.Operand;
                    if (!aa.V.HasValue) { pure = false; break; }
                    result = aa.V.Value >= 0 && aa.V.Value < tg.Length ? tg[aa.V.Value] : (k + 1 < ins.Count ? ins[k + 1] : null); decided = true; break;
                }
                default:
                {
                    pure = false;
                    int pushes, pops; x.CalculateStackUsage(false, out pushes, out pops);
                    if (pops < 0) stack.Clear(); else for (int q = 0; q < pops; q++) pop();
                    for (int q = 0; q < pushes; q++) push(null);
                    continue;
                }
            }
            if (EndsBlock(x)) break;
        }
        if (!ok) pure = false;
        if (!pureMode) return null;
        if (!pure) return null;
        if (decided) return result;
        var last = ins[b.E];
        if (EndsBlock(last)) { pure = false; return null; }
        return b.E + 1 < ins.Count ? ins[b.E + 1] : null;   // fallthrough
    }

    static int? Bin(Code c, int x, int y)
    {
        switch (c)
        {
            case Code.Add: return unchecked(x + y); case Code.Sub: return unchecked(x - y); case Code.Mul: return unchecked(x * y);
            case Code.And: return x & y; case Code.Or: return x | y; case Code.Xor: return x ^ y;
            case Code.Shl: return x << (y & 31); case Code.Shr: return x >> (y & 31); case Code.Shr_Un: return (int)((uint)x >> (y & 31));
            case Code.Div: return y == 0 || (x == int.MinValue && y == -1) ? (int?)null : x / y;
            case Code.Div_Un: return y == 0 ? (int?)null : (int)((uint)x / (uint)y);
            case Code.Rem: return y == 0 || (x == int.MinValue && y == -1) ? (int?)null : x % y;
            case Code.Rem_Un: return y == 0 ? (int?)null : (int)((uint)x % (uint)y);
            case Code.Ceq: return x == y ? 1 : 0; case Code.Cgt: return x > y ? 1 : 0; case Code.Cgt_Un: return (uint)x > (uint)y ? 1 : 0;
            case Code.Clt: return x < y ? 1 : 0; case Code.Clt_Un: return (uint)x < (uint)y ? 1 : 0;
        }
        return null;
    }
    static bool Cmp(Code c, int x, int y)
    {
        uint a = (uint)x, b = (uint)y;
        switch (c)
        {
            case Code.Beq: return x == y; case Code.Bne_Un: return x != y; case Code.Blt: return x < y; case Code.Blt_Un: return a < b;
            case Code.Bgt: return x > y; case Code.Bgt_Un: return a > b; case Code.Ble: return x <= y; case Code.Ble_Un: return a <= b;
            case Code.Bge: return x >= y; default: return a >= b;
        }
    }

    // Simulates b up to (but excluding) its terminator, returning the exit locals and the stack the
    // terminator sees *after* it consumed its condition operands (i.e. the stack carried along the edge).
    static List<SItem> ExitStack(Cfg g, CilBody body, Block b, int?[] st)
    {
        var stack = new List<SItem>();
        for (int q = 0; q < Math.Max(0, b.DepthIn); q++) stack.Add(new SItem { V = null });
        bool p; Sim(g, body, b, st, stack, false, out p);   // non-pure: terminator operands popped, nothing pushed after
        return stack;
    }

    // ------------------------------------------------------------------ analyses
    static void Analyse(Cfg g, CilBody body)
    {
        int nv = body.Variables.Count;
        var entry = new int?[nv];
        for (int v = 0; v < nv; v++) entry[v] = body.InitLocals ? (int?)0 : null;
        g.Blocks[0].In = entry;
        var work = new Queue<Block>(); work.Enqueue(g.Blocks[0]);
        foreach (var b in g.Blocks.Where(b => b.Reachable && b != g.Blocks[0] && b.Region.Contains("h") && g.EhRefs.Contains(b.First)))
        { b.In = new int?[nv]; work.Enqueue(b); }
        int guard = 0;
        while (work.Count > 0 && guard++ < 200000)
        {
            var b = work.Dequeue();
            var st = (int?[])b.In.Clone(); bool p;
            var stk = new List<SItem>(); for (int q = 0; q < Math.Max(0, b.DepthIn); q++) stk.Add(new SItem());
            Sim(g, body, b, st, stk, false, out p);
            foreach (var s in b.LiveSucc)
            {
                bool exc = !b.Succ.Contains(s);
                var flow = exc ? new int?[nv] : st;
                if (s.In == null) { s.In = (int?[])flow.Clone(); work.Enqueue(s); continue; }
                bool ch = false;
                for (int v = 0; v < nv; v++) if (s.In[v].HasValue && s.In[v] != flow[v]) { s.In[v] = null; ch = true; }
                if (ch) work.Enqueue(s);
            }
        }
        var use = new Dictionary<Block, HashSet<int>>(); var def = new Dictionary<Block, HashSet<int>>();
        foreach (var b in g.Blocks)
        {
            var u = new HashSet<int>(); var d = new HashSet<int>();
            for (int k = b.S; k <= b.E; k++)
            {
                var x = body.Instructions[k];
                if (x.IsLdloc() || x.OpCode.Code == Code.Ldloca || x.OpCode.Code == Code.Ldloca_S)
                {
                    var lv = x.OpCode.Code == Code.Ldloca || x.OpCode.Code == Code.Ldloca_S ? x.Operand as Local : x.GetLocal(body.Variables);
                    if (lv != null && !d.Contains(lv.Index)) u.Add(lv.Index);
                }
                else if (x.IsStloc()) { var lv = x.GetLocal(body.Variables); if (lv != null) d.Add(lv.Index); }
            }
            use[b] = u; def[b] = d;
        }
        bool changed = true; int rounds = 0;
        while (changed && rounds++ < 1000)
        {
            changed = false;
            for (int i = g.Blocks.Count - 1; i >= 0; i--)
            {
                var b = g.Blocks[i];
                var outS = new HashSet<int>(); foreach (var s in b.LiveSucc) outS.UnionWith(s.LiveIn);
                var inS = new HashSet<int>(outS); inS.ExceptWith(def[b]); inS.UnionWith(use[b]);
                if (!inS.SetEquals(b.LiveIn) || !outS.SetEquals(b.LiveOut)) { b.LiveIn = inS; b.LiveOut = outS; changed = true; }
            }
        }
    }

    // ------------------------------------------------------------------ threading
    sealed class Edit
    {
        public Block B; public Instruction BranchInsn; public int CaseIdx = -1; public bool Fallthrough; public Block T;
        public List<Instruction> Seq;   // replay (without the final br)
    }

    static int Thread(Cfg g, CilBody body)
    {
        var edits = new List<Edit>(); var ins = body.Instructions;

        foreach (var b in g.Blocks)
        {
            if (!b.Reachable || b.In == null || b.DepthIn < 0) continue;
            var l = b.Last; var c = l.OpCode.Code;
            if (c == Code.Leave || c == Code.Ret || c == Code.Throw || c == Code.Rethrow || c == Code.Endfinally || c == Code.Endfilter) continue;

            var exitSt = (int?[])b.In.Clone();
            var exitStack = ExitStack(g, body, b, exitSt);
            for (int q = 0; q < exitStack.Count; q++) { var it = exitStack[q]; it.FromB = true; exitStack[q] = it; }

            var edgeList = new List<Tuple<Block, int, bool>>();
            Block next = b.E + 1 < ins.Count ? g.ByIndex[b.E + 1] : null;
            if (c == Code.Br) edgeList.Add(Tuple.Create(g.ByFirst[(Instruction)l.Operand], -2, false));
            else if (l.OpCode.FlowControl == FlowControl.Cond_Branch)
            {
                if (l.Operand is Instruction[]) { var tg = (Instruction[])l.Operand; for (int q = 0; q < tg.Length; q++) edgeList.Add(Tuple.Create(g.ByFirst[tg[q]], q, false)); }
                else edgeList.Add(Tuple.Create(g.ByFirst[(Instruction)l.Operand], -2, false));
                if (next != null) edgeList.Add(Tuple.Create(next, -1, true));
            }
            else if (!EndsBlock(l) && next != null) edgeList.Add(Tuple.Create(next, -1, true));

            var doneTargets = new HashSet<Block>();
            foreach (var e in edgeList)
            {
                var d = e.Item1;
                if (d.Region != b.Region) continue;
                var st = (int?[])exitSt.Clone();
                var stack = new List<SItem>(exitStack);
                var cur = d; int steps = 0; var seen = new HashSet<string>(); bool loop = false;
                bool enteredTry = false, decision = false;
                while (steps < 400)
                {
                    if (cur.Region != b.Region)
                    {
                        // a plain branch may enter a protected region at its first instruction
                        enteredTry = steps > 0 && EntersTryAtStart(body, b.Region, cur);
                        break;
                    }
                    if (g.EhRefs.Contains(cur.First) && cur != d) break;
                    var tst = (int?[])st.Clone(); var tstack = new List<SItem>(stack); bool pure;
                    var nx = Sim(g, body, cur, tst, tstack, true, out pure);
                    if (!pure || nx == null) break;
                    string key = cur.S + "|" + string.Join(",", tst.Select(v => v.HasValue ? v.Value.ToString() : "?")) + "|" + string.Join(",", tstack.Select(v => (v.FromB ? "b" : "") + (v.V.HasValue ? v.V.Value.ToString() : "?")));
                    if (!seen.Add(key)) { loop = true; break; }
                    if (cur.Last.OpCode.FlowControl == FlowControl.Cond_Branch) decision = true;
                    st = tst; stack = tstack; cur = g.ByFirst[nx]; steps++;
                }
                // only worth it (and only terminating) if a dispatcher decision is bypassed
                if (loop || steps == 0 || !decision || cur == d || (cur.Region != b.Region && !enteredTry)) continue;
                if (enteredTry && stack.Count != 0) continue;   // the stack must be empty when entering a try

                // stack at T must be: B items (untouched prefix) + known constants
                int keepB = 0; while (keepB < stack.Count && stack[keepB].FromB) keepB++;
                bool bad = false;
                for (int q = keepB; q < stack.Count; q++) if (stack[q].FromB || !stack[q].V.HasValue) { bad = true; break; }
                if (bad) continue;
                int consumed = exitStack.Count - keepB;
                if (consumed < 0) continue;
                if (cur.DepthIn >= 0 && cur.DepthIn != stack.Count) continue;   // must match T's expected depth

                var seq = new List<Instruction>();
                for (int q = 0; q < consumed; q++) seq.Add(Instruction.Create(OpCodes.Pop));
                for (int q = keepB; q < stack.Count; q++) seq.Add(Instruction.CreateLdcI4(stack[q].V.Value));
                for (int v = 0; v < st.Length && !bad; v++)
                {
                    if (st[v] == exitSt[v] || !cur.LiveIn.Contains(v)) continue;
                    if (!st[v].HasValue) { bad = true; break; }
                    seq.Add(Instruction.CreateLdcI4(st[v].Value)); seq.Add(Instruction.Create(OpCodes.Stloc, body.Variables[v]));
                }
                if (bad) continue;
                // for conditional edges, the operand-free stack carried along the edge equals exitStack: fine.
                bool branchEdge = !e.Item3;
                if (branchEdge && c == Code.Br && doneTargets.Count > 0) continue;
                edits.Add(new Edit { B = b, BranchInsn = l, CaseIdx = e.Item2, Fallthrough = e.Item3, T = cur, Seq = seq });
                doneTargets.Add(cur);
            }
        }
        if (edits.Count == 0) return 0;

        // apply (instruction references stay valid across inserts)
        foreach (var ed in edits)
        {
            var target = ed.T.First;
            var full = new List<Instruction>(ed.Seq); full.Add(Instruction.Create(OpCodes.Br, target));
            if (ed.Fallthrough)
            {
                int at = ins.IndexOf(ed.B.Last) + 1;
                for (int q = 0; q < full.Count; q++) ins.Insert(at + q, full[q]);
            }
            else if (ed.BranchInsn.OpCode.Code == Code.Br)
            {
                if (ed.Seq.Count == 0) ed.BranchInsn.Operand = target;
                else
                {
                    ed.BranchInsn.OpCode = full[0].OpCode; ed.BranchInsn.Operand = full[0].Operand;   // keep branch-target identity
                    int at = ins.IndexOf(ed.BranchInsn) + 1;
                    for (int q = 1; q < full.Count; q++) ins.Insert(at + q - 1, full[q]);
                }
            }
            else
            {
                Instruction dest = target;
                if (ed.Seq.Count > 0)
                {
                    var anchor = FindAnchor(g, ins, ed.B);
                    if (anchor == null) continue;
                    int at = ins.IndexOf(anchor) + 1;
                    for (int q = 0; q < full.Count; q++) ins.Insert(at + q, full[q]);
                    dest = full[0];
                }
                if (ed.CaseIdx >= 0) ((Instruction[])ed.BranchInsn.Operand)[ed.CaseIdx] = dest;
                else ed.BranchInsn.Operand = dest;
            }
        }
        return edits.Count;
    }

    // true if `t` starts one or more try blocks and its region is exactly B's region plus those try regions
    static bool EntersTryAtStart(CilBody body, string fromRegion, Block t)
    {
        var from = new HashSet<string>(fromRegion.Split(new[] { ';' }, StringSplitOptions.RemoveEmptyEntries));
        var to = new HashSet<string>(t.Region.Split(new[] { ';' }, StringSplitOptions.RemoveEmptyEntries));
        if (!from.IsSubsetOf(to)) return false;
        to.ExceptWith(from);
        if (to.Count == 0) return false;
        for (int k = 0; k < body.ExceptionHandlers.Count; k++)
            if (to.Contains("t" + k)) { if (body.ExceptionHandlers[k].TryStart != t.First) return false; to.Remove("t" + k); }
        return to.Count == 0;
    }

    // an unconditional instruction in exactly B's EH region, after which a trampoline can live unreached
    static Instruction FindAnchor(Cfg g, IList<Instruction> ins, Block b)
    {
        for (int i = g.Blocks.Count - 1; i >= 0; i--)
        {
            var blk = g.Blocks[i];
            if (blk.Region == b.Region && Unconditional(blk.Last) && g.RegionOf[blk.E] == b.Region
                && (blk.E + 1 >= g.RegionOf.Length || g.RegionOf[blk.E + 1] == b.Region || true))
                return blk.Last;
        }
        return null;
    }

    // ------------------------------------------------------------------ cleanup
    static int RemoveUnreachable(Cfg g, CilBody body)
    {
        var ins = body.Instructions; int n = 0;
        foreach (var b in g.Blocks.Where(b => !b.Reachable))
            for (int k = b.S; k <= b.E; k++)
            {
                var x = g.Blocks.Count > 0 ? body.Instructions[k - n] : null;   // indices shift as we remove
                if (g.EhRefs.Contains(x)) { if (x.OpCode.Code != Code.Nop) { x.OpCode = OpCodes.Nop; x.Operand = null; } continue; }
                ins.RemoveAt(k - n); n++;
            }
        return n;
    }

    static int DeadStoreElim(Cfg g, CilBody body)
    {
        int n = 0; var ins = body.Instructions;
        foreach (var b in g.Blocks)
        {
            if (!b.Reachable) continue;
            var live = new HashSet<int>(b.LiveOut);
            for (int k = b.E; k >= b.S; k--)
            {
                var x = ins[k];
                if (x.IsStloc())
                {
                    var lv = x.GetLocal(body.Variables);
                    if (lv != null && !live.Contains(lv.Index)) { x.OpCode = OpCodes.Pop; x.Operand = null; n++; }
                    else if (lv != null) live.Remove(lv.Index);
                }
                else if (x.IsLdloc()) { var lv = x.GetLocal(body.Variables); if (lv != null) live.Add(lv.Index); }
                else if (x.OpCode.Code == Code.Ldloca || x.OpCode.Code == Code.Ldloca_S) { var lv = x.Operand as Local; if (lv != null) live.Add(lv.Index); }
            }
        }
        return n;
    }

    // ldc/ldloc/ldnull/ldstr immediately followed by pop inside one block -> nop nop
    static int Peephole(Cfg g, CilBody body)
    {
        int n = 0; var ins = body.Instructions;
        foreach (var b in g.Blocks)
        {
            if (!b.Reachable) continue;
            for (int k = b.S; k < b.E; k++)
            {
                var a = ins[k];
                int j = k + 1; while (j <= b.E && ins[j].OpCode.Code == Code.Nop) j++;
                if (j > b.E) break;
                var p = ins[j];
                if (p.OpCode.Code != Code.Pop) continue;
                var ac = a.OpCode.Code;
                if (a.IsLdcI4() || a.IsLdloc() || ac == Code.Ldnull || ac == Code.Ldstr || ac == Code.Dup)
                { a.OpCode = OpCodes.Nop; a.Operand = null; p.OpCode = OpCodes.Nop; p.Operand = null; n++; }
            }
        }
        return n;
    }
}
