// ReactorDeobf - deobfuscator for the .NET Reactor protection used by UACRT-0009 (stage 1 loader + stage 2 PureRAT).
//
// STATIC passes (safe anywhere; the input is only parsed by dnlib):
//   * proxy calls     : decrypts Reactor's delegate map resource (keyless word-keystream cipher) and rewrites
//                       "ldsfld <proxyField>; call <Delegate>::Invoker" into a direct call/callvirt to the real target
//   * predicates      : inlines constant helper methods (return null==null, return <never-assigned field>==null, ...)
//   * folding         : constant-folds integer expressions, brtrue/brfalse/bcc/switch on constants -> br/nop
//   * rename          : readable names for obfuscated identifiers (semantic names for known UACRT-0009 classes)
//
// DYNAMIC passes (--dynamic, ISOLATED LAB VM ONLY - executes the protector's runtime code via reflection):
//   * opaque constants: reads <Module>{GUID} opaque-predicate struct fields and folds them
//   * strings         : calls Reactor's string decryptor  string(int)  for every constant call site -> ldstr
//   * const tables    : calls pure int(int) helpers (Reactor constant tables / CF helpers) -> ldc.i4
//   * string helpers  : calls string(string,int) XOR helpers when both args are constant -> ldstr
//   The sample's entry point is never invoked and no networking code is called.
//
// Usage: ReactorDeobf.exe <in.exe|dll> [-o out] [--dynamic] [--rename] [--strings-out file]
// Build: csc /platform:x86 /r:dnlib.dll /out:ReactorDeobf.exe ReactorDeobf.cs
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using dnlib.DotNet;
using dnlib.DotNet.Emit;
using dnlib.DotNet.Writer;

static class ReactorDeobf
{
    static ModuleDefMD mod;
    static Assembly rasm;                 // reflection copy (dynamic mode only)
    static Module rmod;
    static bool dynamicMode, rename, unflatten;
    static readonly Dictionary<string, int> stats = new Dictionary<string, int>();
    static readonly List<string> stringLog = new List<string>();

    static void Stat(string k, int n = 1) { int v; stats.TryGetValue(k, out v); stats[k] = v + n; }
    static void Log(string s) { Console.WriteLine(s); Console.Out.Flush(); }

    static int Main(string[] args)
    {
        if (args.Length == 0) { Log("usage: ReactorDeobf.exe <in> [-o out] [--dynamic] [--rename] [--strings-out file]"); return 1; }
        string input = args[0], output = null, stringsOut = null;
        for (int i = 1; i < args.Length; i++)
        {
            if (args[i] == "-o") output = args[++i];
            else if (args[i] == "--dynamic") dynamicMode = true;
            else if (args[i] == "--rename") rename = true;
            else if (args[i] == "--unflatten") unflatten = true;
            else if (args[i] == "--strings-out") stringsOut = args[++i];
        }
        if (output == null) output = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(input)), Path.GetFileNameWithoutExtension(input) + ".deobf" + (IsDll(input) ? ".dll" : ".exe"));

        byte[] raw = File.ReadAllBytes(input);
        mod = ModuleDefMD.Load(raw);
        Log("[*] " + mod.Assembly.FullName + "  types=" + mod.GetTypes().Count());

        if (dynamicMode)
        {
            Log("[!] DYNAMIC MODE: the protector's runtime code will execute in this process. Isolated lab VM only.");
            rasm = Assembly.Load(raw);      // byte load, like the real chain (avoids file-based anti-tamper / MOTW)
            rmod = rasm.ManifestModule;
        }

        foreach (MethodDef m in AllMethods()) if (m.HasBody) m.Body.SimplifyMacros(m.Parameters);

        FixProxies();
        var consts = FindConstHelpers();
        var opaque = dynamicMode ? ReadOpaqueConstants() : new Dictionary<FieldDef, int>();
        var dyn = dynamicMode ? FindDynamicHelpers() : new DynHelpers();

        // folding is iterative: each round can expose new constant arguments
        for (int round = 0; round < 6; round++)
        {
            int before = stats.Values.Sum();
            foreach (MethodDef m in AllMethods())
                if (m.HasBody && m.Body.Instructions.Count > 0) Fold(m, consts, opaque, dyn);
            if (stats.Values.Sum() == before) break;
        }

        if (unflatten)
        {
            int ok = 0, reverted = 0;
            foreach (MethodDef m in AllMethods())
            {
                if (!m.HasBody || m.Body.Instructions.Count < 4) continue;
                var snap = Snapshot(m.Body);
                int e0 = Unflattener.Edges, r0 = Unflattener.Removed, d0 = Unflattener.DeadStores;
                bool stackOkBefore = StackOk(m.Body);
                try
                {
                    Unflattener.Run(m);
                    // reject only if we broke a previously consistent stack (Reactor junk can make the original fail)
                    if (stackOkBefore && !StackOk(m.Body) && Environment.GetEnvironmentVariable("UNFLAT_KEEP") != m.Name)
                        throw new InvalidOperationException("stack check failed");
                    ok++;
                }
                catch (Exception e)
                {
                    Restore(m.Body, snap); reverted++;
                    Unflattener.Edges = e0; Unflattener.Removed = r0; Unflattener.DeadStores = d0;
                    if (reverted <= 5) Log("    unflatten reverted " + m.FullName + ": " + e.Message);
                }
            }
            Stat("unflatten: edges threaded", Unflattener.Edges);
            Stat("unflatten: unreachable insns removed", Unflattener.Removed);
            Stat("unflatten: dead stores removed", Unflattener.DeadStores);
            Stat("unflatten: methods reverted", reverted);
            // threading exposes more constants: one more folding round
            foreach (MethodDef m in AllMethods()) if (m.HasBody && m.Body.Instructions.Count > 0) Fold(m, consts, opaque, dyn);
        }

        if (rename) Rename();

        foreach (MethodDef m in AllMethods()) if (m.HasBody) { m.Body.OptimizeMacros(); }

        var opts = IsDll(input) ? (ModuleWriterOptions)new ModuleWriterOptions(mod) : new ModuleWriterOptions(mod);
        opts.MetadataOptions.Flags |= MetadataFlags.PreserveAll | MetadataFlags.KeepOldMaxStack;
        opts.Logger = DummyLogger.NoThrowInstance;
        mod.Write(output, opts);

        Log("\n=== Summary ===");
        foreach (var kv in stats.OrderBy(k => k.Key)) Log(string.Format("  {0,-28} {1}", kv.Key, kv.Value));
        Log("[+] written " + output);
        if (stringsOut != null)
        {
            // keep final plaintext only (drop intermediate, still XOR-masked forms)
            var final = stringLog.Distinct().Where(s => s.Length > 0 && s.Count(ch => ch >= 0x20 && ch < 0x7f) >= s.Length * 0.9).ToList();
            File.WriteAllLines(stringsOut, final, new UTF8Encoding(false));
            Log("[+] strings -> " + stringsOut + " (" + final.Count + ")");
        }
        return 0;
    }

    static bool StackOk(CilBody b)
    {
        try { uint ms; return MaxStackCalculator.GetMaxStack(b.Instructions, b.ExceptionHandlers, out ms); }
        catch { return false; }
    }

    // per-method snapshot so a failed unflatten can be rolled back exactly
    sealed class BodySnap { public List<Instruction> Order; public List<Tuple<Instruction, OpCode, object>> Ops; }
    static BodySnap Snapshot(CilBody b)
    {
        return new BodySnap
        {
            Order = b.Instructions.ToList(),
            Ops = b.Instructions.Select(i => Tuple.Create(i, i.OpCode, i.Operand is Instruction[] ? ((Instruction[])i.Operand).Clone() : i.Operand)).ToList()
        };
    }
    static void Restore(CilBody b, BodySnap s)
    {
        b.Instructions.Clear();
        foreach (var i in s.Order) b.Instructions.Add(i);
        foreach (var t in s.Ops) { t.Item1.OpCode = t.Item2; t.Item1.Operand = t.Item3; }
    }

    static bool IsDll(string p) { return (ModuleDefMD.Load(File.ReadAllBytes(p)).Characteristics & dnlib.PE.Characteristics.Dll) != 0; }
    static IEnumerable<MethodDef> AllMethods() { return mod.GetTypes().SelectMany(t => t.Methods); }

    // ------------------------------------------------------------------ proxies
    static uint KsStep(uint s)
    {
        uint a = 1331087956U, b = s;
        uint t = (a >> 5 | a << 27) ^ b;
        uint lo = t & 0x00FF00FFU; t &= 0xFF00FF00U;
        a = t >> 8 | lo << 8;
        uint c = (a ^ a) - a;
        if (b == 0) b -= 1;
        uint d = a / b + b;
        b = a - a - d + a;
        c = 10476U * (c & 0xFFFF) - (c >> 16);
        a = 22014U * a + b;
        b ^= b << 9; b += c; b ^= b << 1; b += b; b ^= b >> 5; b += 146803825U;
        b = ((c << 11) + a ^ c) + b;
        return s + b;
    }

    static byte[] KeylessDecrypt(byte[] d)
    {
        int rem = d.Length % 4, n = d.Length / 4 + (rem > 0 ? 1 : 0);
        byte[] o = new byte[d.Length]; uint s = 0;
        for (int i = 0; i < n; i++)
        {
            bool last = i == n - 1 && rem > 0; uint w = 0;
            if (last) { for (int j = 0; j < rem; j++) { if (j > 0) w <<= 8; w |= d[d.Length - (1 + j)]; } }
            else w = BitConverter.ToUInt32(d, i * 4);
            s = KsStep(s); uint x = s ^ w;
            if (last) for (int k = 0; k < rem; k++) o[i * 4 + k] = (byte)(x >> (8 * k));
            else BitConverter.GetBytes(x).CopyTo(o, i * 4);
        }
        return o;
    }

    static void FixProxies()
    {
        var map = new Dictionary<FieldDef, uint>();
        foreach (var r in mod.Resources.OfType<EmbeddedResource>())
        {
            byte[] d = r.CreateReader().ToArray();
            if (d.Length < 64 || d.Length % 8 != 0) continue;
            byte[] p = KeylessDecrypt(d);
            int ok = 0, n = p.Length / 8;
            for (int i = 0; i < n; i++)
            {
                uint f = BitConverter.ToUInt32(p, i * 8), m = BitConverter.ToUInt32(p, i * 8 + 4) & 0x3FFFFFFF;
                if (f >> 24 == 0x04 && (m >> 24 == 0x06 || m >> 24 == 0x0A || m >> 24 == 0x2B)) ok++;
            }
            if (ok < n * 0.9) continue;
            Log("[+] delegate map: resource '" + r.Name + "' (" + n + " entries)");
            for (int i = 0; i < n; i++)
            {
                var f = mod.ResolveToken(BitConverter.ToUInt32(p, i * 8)) as FieldDef;
                if (f != null) map[f] = BitConverter.ToUInt32(p, i * 8 + 4);
            }
        }
        if (map.Count == 0) { Log("[-] no delegate map found (no proxy calls?)"); return; }

        var proxyTypes = new HashSet<TypeDef>(map.Keys.Select(f => f.DeclaringType));
        foreach (MethodDef m in AllMethods())
        {
            if (!m.HasBody || proxyTypes.Contains(m.DeclaringType)) continue;
            var ins = m.Body.Instructions;
            for (int i = 1; i < ins.Count; i++)
            {
                if (ins[i].OpCode.Code != Code.Call) continue;
                var inv = ins[i].Operand as MethodDef;
                if (inv == null || !proxyTypes.Contains(inv.DeclaringType)) continue;
                if (ins[i - 1].OpCode.Code != Code.Ldsfld) continue;
                var f = (ins[i - 1].Operand as IField) == null ? null : ((IField)ins[i - 1].Operand).ResolveFieldDef();
                uint v;
                if (f == null || !map.TryGetValue(f, out v)) continue;
                var target = mod.ResolveToken(v & 0x3FFFFFFF) as IMethod;
                if (target == null) continue;
                ins[i - 1].OpCode = OpCodes.Nop; ins[i - 1].Operand = null;
                ins[i].OpCode = (v & 0x40000000) != 0 ? OpCodes.Callvirt : OpCodes.Call;
                ins[i].Operand = target;
                Stat("proxy calls restored");
            }
        }
    }

    // ------------------------------------------------------------------ constant helper methods
    sealed class NullConst { public static readonly NullConst I = new NullConst(); }

    static Dictionary<MethodDef, object> FindConstHelpers()
    {
        var stored = new HashSet<FieldDef>();
        foreach (MethodDef m in AllMethods())
            if (m.HasBody)
                foreach (var i in m.Body.Instructions)
                    if (i.OpCode.Code == Code.Stsfld || i.OpCode.Code == Code.Ldsflda)
                    { var f = i.Operand as IField; var fd = f == null ? null : f.ResolveFieldDef(); if (fd != null) stored.Add(fd); }

        var res = new Dictionary<MethodDef, object>();
        foreach (MethodDef m in AllMethods())
        {
            if (!m.IsStatic || !m.HasBody || m.Parameters.Count != 0 || m.ReturnType.ElementType == ElementType.Void) continue;
            var all = m.Body.Instructions;
            int start = 0;   // skip Reactor's anti-decompiler prologue: br <next real insn>; call <invalid>
            if (all.Count > 0 && all[0].OpCode.Code == Code.Br && all[0].Operand is Instruction) start = all.IndexOf((Instruction)all[0].Operand);
            if (start < 0) start = 0;
            var b = all.Skip(start).Where(x => x.OpCode.Code != Code.Nop).ToList();
            object val = null;
            if (b.Count == 2 && b[1].OpCode.Code == Code.Ret)
            {
                if (b[0].IsLdcI4()) val = b[0].GetLdcI4Value();
                else if (b[0].OpCode.Code == Code.Ldnull) val = NullConst.I;
                else if (b[0].OpCode.Code == Code.Ldsfld && Unassigned(b[0], stored)) val = NullConst.I;
            }
            else if (b.Count == 4 && b[3].OpCode.Code == Code.Ret && b[2].OpCode.Code == Code.Ceq && b[1].OpCode.Code == Code.Ldnull)
            {
                if (b[0].OpCode.Code == Code.Ldnull) val = 1;
                else if (b[0].OpCode.Code == Code.Ldsfld && Unassigned(b[0], stored)) val = 1;
            }
            if (val != null) res[m] = val;
        }
        Log("[+] constant predicate helpers: " + res.Count);
        return res;
    }

    static bool Unassigned(Instruction ldsfld, HashSet<FieldDef> stored)
    {
        var f = ldsfld.Operand as IField; var fd = f == null ? null : f.ResolveFieldDef();
        return fd != null && !fd.HasConstant && fd.InitialValue == null && !stored.Contains(fd) && !fd.FieldType.IsValueType;
    }

    // ------------------------------------------------------------------ dynamic helpers
    sealed class DynHelpers
    {
        public HashSet<MethodDef> StringDecryptors = new HashSet<MethodDef>();
        public HashSet<MethodDef> IntTables = new HashSet<MethodDef>();
        public HashSet<MethodDef> StringXor = new HashSet<MethodDef>();
        public HashSet<TypeDef> OpaqueStructs = new HashSet<TypeDef>();
    }

    static Dictionary<FieldDef, int> ReadOpaqueConstants()
    {
        var res = new Dictionary<FieldDef, int>();
        foreach (TypeDef t in mod.GetTypes())
            foreach (FieldDef sf in t.Fields)
            {
                if (!sf.IsStatic) continue;
                var st = sf.FieldType.ToTypeDefOrRef() == null ? null : sf.FieldType.ToTypeDefOrRef().ResolveTypeDef();
                if (st == null || st != t || !t.Name.String.StartsWith("<Module>{") || t.Fields.Count(f => !f.IsStatic && f.FieldType.ElementType == ElementType.I4) < 10) continue;
                if (t.Fields.Any(f => res.ContainsKey(f))) continue;   // one instance per struct type is enough
                try
                {
                    object box = rmod.ResolveField(sf.MDToken.ToInt32()).GetValue(null);
                    if (box == null) continue;
                    foreach (FieldDef f in t.Fields.Where(f => !f.IsStatic && f.FieldType.ElementType == ElementType.I4))
                        res[f] = (int)rmod.ResolveField(f.MDToken.ToInt32()).GetValue(box);
                    Log("[+] opaque constants: " + t.Name + " (" + res.Count + " fields)");
                }
                catch (Exception e) { Log("[-] opaque struct read failed: " + Inner(e)); }
            }
        return res;
    }

    static DynHelpers FindDynamicHelpers()
    {
        var h = new DynHelpers();
        var callCount = new Dictionary<MethodDef, int>();
        foreach (MethodDef m in AllMethods())
            if (m.HasBody)
                for (int i = 1; i < m.Body.Instructions.Count; i++)
                {
                    var ins = m.Body.Instructions[i];
                    var md = (ins.OpCode.Code == Code.Call ? ins.Operand as MethodDef : null);
                    if (md != null) { int c; callCount.TryGetValue(md, out c); callCount[md] = c + 1; }
                }

        foreach (MethodDef m in AllMethods())
        {
            if (!m.IsStatic || !m.HasBody || m.DeclaringType.HasGenericParameters) continue;
            var sig = m.MethodSig;
            string ret = m.ReturnType.FullName;
            var ps = sig.Params.Select(p => p.FullName).ToArray();
            var ops = m.Body.Instructions;
            if (ret == "System.String" && ps.Length == 1 && ps[0] == "System.Int32"
                && ops.Any(x => x.Operand is IMethod && ((IMethod)x.Operand).FullName.Contains("System.Diagnostics.StackFrame::.ctor"))
                && ops.Any(x => x.Operand is IMethod && ((IMethod)x.Operand).Name == "get_Unicode"))
                h.StringDecryptors.Add(m);
            else if (ret == "System.Int32" && ps.Length == 1 && ps[0] == "System.Int32" && callCount.ContainsKey(m)
                && (callCount[m] >= 20 || IsPureIntHelper(m)))
                h.IntTables.Add(m);
            else if (ret == "System.String" && ps.Length == 2 && ps[0] == "System.String" && ps[1] == "System.Int32")
                h.StringXor.Add(m);
        }
        Log("[+] string decryptors: " + string.Join(", ", h.StringDecryptors.Select(x => x.DeclaringType.Name + "::" + x.Name)));
        Log("[+] int constant tables / CF helpers: " + h.IntTables.Count);
        Log("[+] string(string,int) helpers: " + string.Join(", ", h.StringXor.Select(x => x.DeclaringType.Name + "::" + x.Name)));
        return h;
    }

    // int(int) with no field writes and no calls leaving the module: Reactor control-flow / constant helpers
    static bool IsPureIntHelper(MethodDef m)
    {
        foreach (var x in m.Body.Instructions)
        {
            var c = x.OpCode.Code;
            if (c == Code.Stsfld || c == Code.Stfld || c == Code.Newobj || c == Code.Calli) return false;
            if ((c == Code.Call || c == Code.Callvirt) && x.Operand is IMethod)
            {
                var md = ((IMethod)x.Operand).ResolveMethodDef();
                if (md == null || md.Module != mod) return false;
            }
        }
        return true;
    }

    static readonly Dictionary<string, object> dynCache = new Dictionary<string, object>();
    static object Invoke(MethodDef m, params object[] a)
    {
        string key = m.MDToken.Raw + "|" + string.Join("|", a.Select(x => x == null ? "null" : x.ToString()));
        object v;
        if (dynCache.TryGetValue(key, out v)) return v;
        try { v = ((MethodBase)rmod.ResolveMethod(m.MDToken.ToInt32())).Invoke(null, a); }
        catch (Exception e) { Stat("dynamic invoke failures"); if (stats["dynamic invoke failures"] <= 5) Log("    invoke " + m.Name + " failed: " + Inner(e)); v = null; }
        dynCache[key] = v;
        return v;
    }
    static string Inner(Exception e) { while (e.InnerException != null) e = e.InnerException; return e.GetType().Name + ": " + e.Message; }

    // ------------------------------------------------------------------ folding
    sealed class Val
    {
        public object V;                                // int, string, NullConst, StructRef or null(unknown)
        public List<Instruction> Src = new List<Instruction>();
        public bool Known { get { return V != null && !(V is StructRef); } }
    }
    sealed class StructRef { }

    static Val U() { return new Val(); }
    static Val K(object v, Instruction i, params Val[] from)
    {
        var r = new Val { V = v };
        foreach (var f in from) r.Src.AddRange(f.Src);
        r.Src.Add(i);
        return r;
    }
    static void Kill(Val v) { foreach (var i in v.Src) { i.OpCode = OpCodes.Nop; i.Operand = null; } }

    static void Fold(MethodDef m, Dictionary<MethodDef, object> consts, Dictionary<FieldDef, int> opaque, DynHelpers dyn)
    {
        var body = m.Body; var ins = body.Instructions;
        var targets = new HashSet<Instruction>();
        foreach (var i in ins)
        {
            if (i.Operand is Instruction) targets.Add((Instruction)i.Operand);
            if (i.Operand is Instruction[]) foreach (var t in (Instruction[])i.Operand) targets.Add(t);
        }
        foreach (var eh in body.ExceptionHandlers)
            foreach (var t in new[] { eh.TryStart, eh.TryEnd, eh.HandlerStart, eh.HandlerEnd, eh.FilterStart }) if (t != null) targets.Add(t);

        var st = new List<Val>();
        Func<Val> pop = () => { if (st.Count == 0) return U(); var v = st[st.Count - 1]; st.RemoveAt(st.Count - 1); return v; };
        bool hasRet = m.ReturnType.ElementType != ElementType.Void;

        for (int idx = 0; idx < ins.Count; idx++)
        {
            var i = ins[idx];
            if (targets.Contains(i)) st.Clear();
            var c = i.OpCode.Code;

            if (i.IsLdcI4()) { st.Add(K(i.GetLdcI4Value(), i)); continue; }
            if (c == Code.Ldnull) { st.Add(K(NullConst.I, i)); continue; }
            if (c == Code.Ldstr) { st.Add(K((string)i.Operand, i)); continue; }

            if (c == Code.Ldsfld || c == Code.Ldsflda)
            {
                var f = (i.Operand as IField) == null ? null : ((IField)i.Operand).ResolveFieldDef();
                var ft = f == null || f.FieldType.ToTypeDefOrRef() == null ? null : f.FieldType.ToTypeDefOrRef().ResolveTypeDef();
                if (ft != null && ft == f.DeclaringType && ft.Name.String.StartsWith("<Module>{")) { var v = new Val { V = new StructRef() }; v.Src.Add(i); st.Add(v); continue; }
            }
            if (c == Code.Ldfld)
            {
                var obj = pop();
                var f = (i.Operand as IField) == null ? null : ((IField)i.Operand).ResolveFieldDef();
                int ov;
                if (obj.V is StructRef && f != null && opaque.TryGetValue(f, out ov)) { st.Add(K(ov, i, obj)); Stat("opaque constants folded"); continue; }
                st.Add(U()); continue;
            }

            switch (c)
            {
                case Code.Add: case Code.Sub: case Code.Mul: case Code.And: case Code.Or: case Code.Xor:
                case Code.Shl: case Code.Shr: case Code.Shr_Un: case Code.Div: case Code.Div_Un: case Code.Rem: case Code.Rem_Un:
                case Code.Ceq: case Code.Cgt: case Code.Cgt_Un: case Code.Clt: case Code.Clt_Un:
                {
                    var b = pop(); var a = pop();
                    if (a.V is int && b.V is int)
                    {
                        int x = (int)a.V, y = (int)b.V; int? r = null;
                        try
                        {
                            switch (c)
                            {
                                case Code.Add: r = unchecked(x + y); break; case Code.Sub: r = unchecked(x - y); break;
                                case Code.Mul: r = unchecked(x * y); break; case Code.And: r = x & y; break;
                                case Code.Or: r = x | y; break; case Code.Xor: r = x ^ y; break;
                                case Code.Shl: r = x << (y & 31); break; case Code.Shr: r = x >> (y & 31); break;
                                case Code.Shr_Un: r = (int)((uint)x >> (y & 31)); break;
                                case Code.Div: if (y != 0) r = x / y; break; case Code.Div_Un: if (y != 0) r = (int)((uint)x / (uint)y); break;
                                case Code.Rem: if (y != 0) r = x % y; break; case Code.Rem_Un: if (y != 0) r = (int)((uint)x % (uint)y); break;
                                case Code.Ceq: r = x == y ? 1 : 0; break; case Code.Cgt: r = x > y ? 1 : 0; break;
                                case Code.Cgt_Un: r = (uint)x > (uint)y ? 1 : 0; break; case Code.Clt: r = x < y ? 1 : 0; break;
                                case Code.Clt_Un: r = (uint)x < (uint)y ? 1 : 0; break;
                            }
                        }
                        catch { }
                        if (r.HasValue) { st.Add(K(r.Value, i, a, b)); continue; }
                    }
                    else if (c == Code.Ceq && a.V is NullConst && b.V is NullConst) { st.Add(K(1, i, a, b)); continue; }
                    st.Add(U()); continue;
                }
                case Code.Not: case Code.Neg:
                {
                    var a = pop();
                    if (a.V is int) { st.Add(K(c == Code.Not ? ~(int)a.V : unchecked(-(int)a.V), i, a)); continue; }
                    st.Add(U()); continue;
                }
                case Code.Conv_I4: case Code.Conv_U4:
                {
                    var a = pop();
                    if (a.V is int) { st.Add(K(a.V, i, a)); continue; }
                    st.Add(U()); continue;
                }
                case Code.Dup: { pop(); st.Add(U()); st.Add(U()); continue; }
                case Code.Brtrue: case Code.Brfalse:
                {
                    var a = pop();
                    if (a.Known)
                    {
                        bool truth = a.V is NullConst ? false : a.V is int ? (int)a.V != 0 : true;
                        bool taken = (c == Code.Brtrue) == truth;
                        Kill(a);
                        if (taken) { i.OpCode = OpCodes.Br; st.Clear(); } else { i.OpCode = OpCodes.Nop; i.Operand = null; }
                        Stat("branches folded");
                    }
                    else st.Clear();
                    continue;
                }
                case Code.Beq: case Code.Bne_Un: case Code.Blt: case Code.Blt_Un: case Code.Bgt: case Code.Bgt_Un:
                case Code.Ble: case Code.Ble_Un: case Code.Bge: case Code.Bge_Un:
                {
                    var b = pop(); var a = pop();
                    if (a.V is int && b.V is int)
                    {
                        int x = (int)a.V, y = (int)b.V; uint ux = (uint)x, uy = (uint)y; bool t = false;
                        switch (c)
                        {
                            case Code.Beq: t = x == y; break; case Code.Bne_Un: t = x != y; break;
                            case Code.Blt: t = x < y; break; case Code.Blt_Un: t = ux < uy; break;
                            case Code.Bgt: t = x > y; break; case Code.Bgt_Un: t = ux > uy; break;
                            case Code.Ble: t = x <= y; break; case Code.Ble_Un: t = ux <= uy; break;
                            case Code.Bge: t = x >= y; break; case Code.Bge_Un: t = ux >= uy; break;
                        }
                        Kill(a); Kill(b);
                        if (t) { i.OpCode = OpCodes.Br; st.Clear(); } else { i.OpCode = OpCodes.Nop; i.Operand = null; }
                        Stat("branches folded");
                    }
                    else st.Clear();
                    continue;
                }
                case Code.Switch:
                {
                    var a = pop();
                    if (a.V is int)
                    {
                        var tg = (Instruction[])i.Operand; int x = (int)a.V;
                        Kill(a);
                        if (x >= 0 && x < tg.Length) { i.OpCode = OpCodes.Br; i.Operand = tg[x]; st.Clear(); }
                        else { i.OpCode = OpCodes.Nop; i.Operand = null; }
                        Stat("switches folded");
                    }
                    else st.Clear();
                    continue;
                }
                case Code.Call:
                {
                    var md = (i.Operand as IMethod) == null ? null : ((IMethod)i.Operand).ResolveMethodDef();
                    object cv;
                    if (md != null && md.Module == mod && consts.TryGetValue(md, out cv))
                    {
                        if (cv is int) { i.OpCode = OpCodes.Ldc_I4; i.Operand = (int)cv; } else { i.OpCode = OpCodes.Ldnull; i.Operand = null; }
                        st.Add(K(cv, i)); Stat("predicate calls inlined"); continue;
                    }
                    if (dynamicMode && md != null && md.Module == mod)
                    {
                        if (dyn.StringDecryptors.Contains(md) && st.Count >= 1 && st[st.Count - 1].V is int)
                        {
                            var a = pop(); var s = Invoke(md, (int)a.V) as string;
                            if (s != null) { Kill(a); i.OpCode = OpCodes.Ldstr; i.Operand = s; st.Add(K(s, i)); Stat("strings decrypted"); stringLog.Add(s.Replace("\r", "\\r").Replace("\n", "\\n")); continue; }
                            st.Add(U()); continue;
                        }
                        if (dyn.IntTables.Contains(md) && st.Count >= 1 && st[st.Count - 1].V is int)
                        {
                            var a = pop(); var r = Invoke(md, (int)a.V);
                            if (r is int) { Kill(a); i.OpCode = OpCodes.Ldc_I4; i.Operand = (int)r; st.Add(K(r, i)); Stat("int-table calls folded"); continue; }
                            st.Add(U()); continue;
                        }
                        if (dyn.StringXor.Contains(md) && st.Count >= 2 && st[st.Count - 1].V is int && st[st.Count - 2].V is string)
                        {
                            var b = pop(); var a = pop(); var s = Invoke(md, (string)a.V, (int)b.V) as string;
                            if (s != null) { Kill(a); Kill(b); i.OpCode = OpCodes.Ldstr; i.Operand = s; st.Add(K(s, i)); Stat("string helpers folded"); stringLog.Add(s.Replace("\r", "\\r").Replace("\n", "\\n")); continue; }
                            st.Add(U()); continue;
                        }
                    }
                    goto default;
                }
                default:
                {
                    int pushes, pops;
                    i.CalculateStackUsage(hasRet, out pushes, out pops);
                    if (pops < 0) st.Clear(); else for (int k = 0; k < pops; k++) pop();
                    for (int k = 0; k < pushes; k++) st.Add(U());
                    var fc = i.OpCode.FlowControl;
                    if (fc == FlowControl.Branch || fc == FlowControl.Return || fc == FlowControl.Throw || fc == FlowControl.Cond_Branch) st.Clear();
                    continue;
                }
            }
        }
    }

    // ------------------------------------------------------------------ renaming
    // Reactor identifiers: 9-24 chars mixing digits/upper/lower, 10-char names with >=3 capitals, or 6-char lowercase nested names
    static readonly Regex Obf = new Regex(@"^(?=.*\d)(?=.*[A-Z])(?=.*[a-z])[A-Za-z0-9]{9,24}$|^(?=(?:.*[A-Z]){3})(?=.*[a-z])[A-Za-z]{10}$|^[a-z]{6}$");
    static readonly Dictionary<string, string> Known = new Dictionary<string, string>
    {
        // stage 1 (Lvgluhzlcf / Yhosh loader)
        {"uOTpBM4yxXYeu50Yni.RdgVw2Q62Awk9I6NlA","Loader.Program"}, {"CJenZtiPcBOiQyVfoO.mA2iBc9M4PFoZistOo","Loader.CryptoConfig"},
        {"rqQuqc1N1LS2w50R7p1.tnVuMb11XsytpLQxB2Z","Loader.TripleDesStage"}, {"PgctAf1ecrVdM1JIGQM.mb0p1J18juKNZM8Fl4b","Loader.GZipStage"},
        {"fJuCLi1nlAEqgDZ5uTJ.P0FyYA1Zl2mh0qKKNGw","Loader.AssemblyLoadStage"}, {"gS5ogqNZtRb7NIMAIpA.AXZ6vJNe5n6MM4wsl97","Loader.Pipeline"},
        {"UeH88kNFQrWbN3WDQQU.QReapGNwpAQyPC3uUOx","Loader.PipelineRunner"}, {"mKjyb91IuKJP3b4LE4c.IYy2YWz6XUy266Jxjf","Loader.IStage"},
        {"HZLnumXbH0fUr6Sqau.r72Bg6Oe2xLAAtr77o","Loader.StageResult"}, {"Lvgluhzlcf.Properties.Ioulf","Loader.Resources"},
        {"rjNgAfNbGkHyvicuA2O.BdKi3KNJpUhg0qT3Rma","Reactor.Runtime"}, {"Bgkn6aeiWZkvdXt8MkR.ovfXqWe9lS3kVjcRu4k","Reactor.ResourceResolver"},
        {"ODqRw0eSAn1sbKIsWQo.uXSds1eAmg1WLA6vJZS","Reactor.VM"}, {"mhrJ4RNDfsPTB6LmpM4.roj5uYNiVPparT9QKEV","Reactor.DelegateResolver"},
        // stage 2 (Piatm.dll / PureRAT)
        {"FN8emunC8ZVBJJ8aHt.YnLRfF3vTG0PWsJQHk","PureRat.Entry"}, {"c38qoHxlrsmVb86PSpO.cQpavex1EWXTRbVhcBQ","PureRat.C2Client"},
        {"oFNUTSO5mfikLLRYZi.IHPog1oUgue51WpvM9","PureRat.Config"}, {"vqiY6KKeXmPWlsh2qd.bV6Gec9UBitWGDLSUA","PureRat.Serializer"},
        {"CJqahM2eu5IuSIsvGcr.coQ0nd2nYmbWtfwvfhG","PureRat.Installer"}, {"gQwjyb2ib5J9FlVA9aU.zLI1rM2FKBOBxS1DrW6","PureRat.MutexGuard"},
        {"N824OHxi8b22PorsgJO.zckkZixFs0SKlLu0tPE","PureRat.SocketConnector"}, {"SK23sZq0AaXY5kr3eaE.GaHKZPxzygCRjvcYa2v","PureRat.GZip"},
        {"lYdiak2muhc6yeg9gCl.IpdsPf2aocRKUJHmx2w","PureRat.SystemInfo"}, {"WcrnTJq22iUakYvYNXy.aFoOGnqwpQnmwtihB94","PureRat.HwidMd5"},
        {"d9O6F12xbktCJ8EfIMV.uWbDQK22pTsb6b7WR79","PureRat.IdleTime"}, {"iH0XZQ2vnZ0r9CYD49e.VOy3lr2Zm0NMn6FMKUg","PureRat.Screenshot"},
        {"FM0Bjp2AS9iZjeVkaWk.eomt1K2LAdAiVgOlYHH","PureRat.WalletScanner"}, {"g4TNYS2s6Okt2BMe20e.fAShXk24jpNPBVvsZdY","PureRat.RegistryStore"},
        {"n7PmXY2N2IghmdVnAbC.ugsjQr2JqLOrHAcdYnM","PureRat.PluginHost"}, {"L0Z6cWwjc0ZBN4tN8S4.iauf0kwYhRTT3Nd98uT","PureRat.PluginRunner"},
        {"WkW2y7qaT78OX1k3Th9.khmKPgqDdW6me8cEePD","PureRat.AntiDebugWatchdog"}, {"GPA4s1dDPBGQ9CT0eCJ.olUNrSdTPbfwcNBiM4V","PureRat.AntiDebugWatchdog2"},
        {"IZ8RNOd8xhqYwVlptW0.VF9ixsdgRDLhZcp2JkH","PureRat.StringXorA"}, {"fO0aG7q81F2GPERTytf.SjvSy5qg2os6HKPRMu7","PureRat.StringXorB"},
        {"iyp4thcR21m2Jnpc9i7.bYn8iVcq2efj6s0GQNh","Reactor.Runtime"}, {"sTJMuTdRZ4TdgnNncJ8.jIWn3NdqSMM1bJqjE0W","Reactor.ConstTable"},
        {"KnSkUpqRQjQCXeSyYgP.JfCJayqqAd1W5IdHSvm","Reactor.ConstTable2"},
    };
    static readonly Dictionary<string, string> KnownMethods = new Dictionary<string, string>
    {
        {"Loader.Program::xYHgGhh6M","Main"}, {"PureRat.Entry::AgLecDCGR","Main"},
        {"PureRat.C2Client::BscxWYevol","Run"}, {"PureRat.C2Client::h60xtKKkXW","Initialize"},
        {"PureRat.C2Client::rSVxEuEtfg","Send"}, {"PureRat.C2Client::S7IxNVEW5i","ValidateServerCertificate"},
        {"Reactor.Runtime::vhgNMSuGxM","DecryptString"}, {"Reactor.Runtime::bIac9WHcPg","DecryptString"},
        {"Reactor.Runtime::f3WNrwUu0E","ResolveProxyDelegates"}, {"Reactor.Runtime::skdNXI5QKm","StreamCipher"},
        {"Reactor.ResourceResolver::pMMel3bLtk","DecryptResourceAssembly"}, {"Reactor.ConstTable::TwsdVvQN6i","Get"},
        {"Loader.Resources::get_Ojrntjghte","get_EncryptedPayload"},
        {"Loader.PipelineRunner::SdYNY1Ag95","Run"}, {"Loader.PipelineRunner::BapNQ1dIGS","BuildPipeline"},
        {"Loader.Pipeline::V6bNnYYOdl","AddStage"}, {"Loader.Pipeline::JS4NCbmDEw","Execute"},
        {"Loader.TripleDesStage::E1gFSV4bEQ","Process"}, {"Loader.GZipStage::E1gFSV4bEQ","Process"},
        {"Loader.AssemblyLoadStage::E1gFSV4bEQ","Process"},
        {"Loader.CryptoConfig::GA3lqF1D7","GetKey"}, {"Loader.CryptoConfig::dfuJmWEOG","GetIV"},
        {"Loader.CryptoConfig::ouELigiiK","GetMode"}, {"Loader.CryptoConfig::xijjvjJSF","GetPadding"},
        {"Loader.CryptoConfig::jxlDGFCYm","WipeKeys"},
        {"Reactor.ResourceResolver::kLjw4iIsCLsZtxc4lksN0j","Install"}, {"Reactor.ResourceResolver::x8SeJoLmSA","OnResourceResolve"},
        {"PureRat.StringXorA::e2AdI3Epm2","Xor"}, {"PureRat.StringXorB::h9jqIhAYpA","Xor"},
        {"PureRat.Serializer::ewGsBkW1r","Deserialize"}, {"PureRat.SocketConnector::YycxcPYg7Q","Connect"},
        {"PureRat.Config::xKvLIpRfH","GetCertificateB64"},
    };

    static readonly Dictionary<string, string> virtualNames = new Dictionary<string, string>();
    static readonly Dictionary<string, string> KnownVirtual = new Dictionary<string, string>
    {
        {"E1gFSV4bEQ", "Process"},                       // Loader.IStage::Process(byte[], CryptoConfig)
    };
    // stage-2 config (PureRat.Config) accessors and backing fields, by original name (verified against the decoded config)
    static readonly Dictionary<string, string> KnownByName = new Dictionary<string, string>
    {
        {"w30YK9y23","get_Hosts"}, {"CP9js3oyZ","set_Hosts"}, {"P2BBySaqr","get_Ports"}, {"VfjG9VkfD","set_Ports"},
        {"xKvLIpRfH","get_CertificateB64"}, {"NwMA7ivuE","set_CertificateB64"}, {"Sv8zo1UW4","get_Group"}, {"Caef0b97tr","set_Group"},
        {"JZLfu4M8NU","get_InstallEnabled"}, {"TVnfwM94A7","set_InstallEnabled"}, {"D9Nfx7Wh6k","get_FlagB"}, {"AbNfq6VSDm","set_FlagB"},
        {"JOFfVcjaoA","get_InstallFileName"}, {"XbofdcRQaI","set_InstallFileName"}, {"B8gfiHuT9r","get_InstallFolderEnv"}, {"XZufctHNIF","set_InstallFolderEnv"},
        {"XWjfnS2xCU","get_MutexName"}, {"IZofebbtHu","set_MutexName"}, {"tKEflS659Y","get_FlagC"}, {"RxOftlTgZO","set_FlagC"},
    };
    static readonly Dictionary<string, string> KnownFieldsByName = new Dictionary<string, string>
    {
        {"nJpfSB1aF8","Hosts"}, {"y4pfJqLbdW","Ports"}, {"ka8fNuMd8I","CertificateB64"}, {"x2QfEeEo4B","Group"},
        {"wJTfMEuhOR","InstallEnabled"}, {"prCfgFHx1J","FlagB"}, {"MK2f871pZ2","InstallFileName"}, {"Tw3fIy8osl","InstallFolderEnv"},
        {"B3Cfhgd89H","MutexName"}, {"sIwf9nUFeP","FlagC"},
    };
    // "<new type full name>@<method token>" -> name, for methods identified by decompilation of the unflattened output
    static readonly Dictionary<string, string> KnownByToken = new Dictionary<string, string>
    {
        {"PureRat.Installer@060000C6","InstallIfNotInstalled"}, {"PureRat.Installer@060000C7","CopySelfAndRegisterTask"},
        {"PureRat.Installer@060000C8","EnsureRunKeyIfNotInWindowsDir"}, {"PureRat.Installer@060000C9","SetRunKey"},
        {"PureRat.Installer@060000CA","RunHiddenPowerShell"}, {"PureRat.MutexGuard@060000C2","Acquire"},
        {"PureRat.SocketConnector@06000116","TryConnect"}, {"PureRat.RegistryStore@060000E2","ReadValue"},
        {"PureRat.RegistryStore@060000E1","GetKeyPath"}, {"PureRat.RegistryStore@060000E3","WriteValue"},
        {"PureRat.SystemInfo@060000F0","GetHwid"}, {"PureRat.SystemInfo@060000F8","WmiQuery"},
    };

    static void Rename()
    {
        int nt = 0, nm = 0, nf = 0;
        foreach (TypeDef t in mod.GetTypes().ToList())
        {
            string newFull;
            if (Known.TryGetValue(t.FullName, out newFull))
            {
                int dot = newFull.LastIndexOf('.');
                if (!t.IsNested) t.Namespace = newFull.Substring(0, dot);
                t.Name = newFull.Substring(dot + 1); nt++;
            }
            else if (Obf.IsMatch(t.Name))
            {
                if (!t.IsNested && Obf.IsMatch(t.Namespace ?? "")) t.Namespace = "";
                t.Name = (t.IsDelegate ? "Proxy_" : "Class_") + t.MDToken.Raw.ToString("X8"); nt++;
            }
            else if (!t.IsNested && Obf.IsMatch(t.Namespace ?? "")) t.Namespace = "";

            foreach (MethodDef m in t.Methods)
            {
                // only constructors are off-limits; Reactor keeps SpecialName on the property accessors it renames
                if (m.IsRuntimeSpecialName || m.IsConstructor) continue;
                if (m.IsSpecialName && !Obf.IsMatch(m.Name)) continue;
                string byName, byTok;
                string tfull = (t.Namespace.String.Length > 0 ? t.Namespace + "." : "") + t.Name;
                if (KnownByToken.TryGetValue(tfull + "@" + m.MDToken.Raw.ToString("X8"), out byTok)) { m.Name = byTok; nm++; continue; }
                if (KnownByName.TryGetValue(m.Name, out byName)) { m.Name = byName; nm++; continue; }
                if (m.IsVirtual)
                {
                    // virtual / interface members: rename by old name so implicit interface binding stays consistent
                    // (Reactor names never collide with framework member names)
                    if (!Obf.IsMatch(m.Name)) continue;
                    string vn;
                    if (!virtualNames.TryGetValue(m.Name, out vn))
                        virtualNames[m.Name] = vn = KnownVirtual.ContainsKey(m.Name) ? KnownVirtual[m.Name] : "vmethod_" + m.MDToken.Raw.ToString("X8");
                    m.Name = vn; nm++;
                    continue;
                }
                string km;
                string key = (t.Namespace.String.Length > 0 ? t.Namespace + "." : "") + t.Name + "::" + m.Name;
                if (KnownMethods.TryGetValue(key, out km)) { m.Name = km; nm++; }
                else if (Obf.IsMatch(m.Name)) { m.Name = "method_" + m.MDToken.Raw.ToString("X8"); nm++; }
                foreach (var p in m.ParamDefs) if (p.Name == " " || p.Name == "\u0020" || Obf.IsMatch(p.Name)) p.Name = "arg" + p.Sequence;
            }
            foreach (FieldDef f in t.Fields)
            {
                string kf;
                if (KnownFieldsByName.TryGetValue(f.Name, out kf)) { f.Name = kf; nf++; }
                else if (Obf.IsMatch(f.Name) || f.Name.String.StartsWith("m_")) { f.Name = "field_" + f.MDToken.Raw.ToString("X8"); nf++; }
            }
            foreach (PropertyDef p in t.Properties) if (Obf.IsMatch(p.Name)) p.Name = "prop_" + p.MDToken.Raw.ToString("X8");
        }
        Stat("types renamed", nt); Stat("methods renamed", nm); Stat("fields renamed", nf);
    }
}
