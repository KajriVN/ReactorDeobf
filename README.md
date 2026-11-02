# ReactorDeobf

A deobfuscator for the .NET Reactor protection used by **UACRT-0009**: stage 1 (`Yhosh`/`Lvgluhzlcf` loader) and stage 2 (`Piatm.dll`, PureRAT). It is built on dnlib 3.3.2 (net45), and every transform is grounded in the protector internals reversed during this case.

> **Dynamic mode executes the protector's runtime code** (string decryptor, VM init, constant tables) through reflection in the tool's own process. Run it **only in the isolated, snapshotted lab VM**. Static mode only parses the file.

## Usage
```
ReactorDeobf.exe <input> [-o <output>] [--dynamic] [--unflatten] [--rename] [--strings-out <file>]
```
| Flag | Effect |
|---|---|
| *(none)* | Static passes only: proxy restore, predicate inlining, constant/branch folding |
| `--dynamic` | Adds opaque constants, string decryption, int constant-table folding and string-XOR helper folding (lab only) |
| `--unflatten` | Removes control-flow flattening (jump threading through the state-machine dispatchers; see below) |
| `--rename` | Readable names; semantic names for known UACRT-0009 classes (`PureRat.C2Client`, `Loader.TripleDesStage`, …), `Class_/method_/field_<token>` elsewhere |
| `--strings-out` | Writes every recovered plaintext string |

Examples (as run in this case):
```
ReactorDeobf.exe ..\..\sample -o final\stage1.deobf.exe.infected --dynamic --unflatten --rename --strings-out final\stage1.strings.txt
ReactorDeobf.exe ..\..\extracted\stage2_decrypted.bin.infected -o final\stage2.deobf.dll.infected --dynamic --unflatten --rename --strings-out final\stage2.strings.txt
```
Build: `C:\Windows\Microsoft.NET\Framework\v4.0.30319\csc.exe /platform:x86 /r:dnlib.dll /out:ReactorDeobf.exe ReactorDeobf.cs Unflattener.cs`

## Passes
| Pass | Mode | What it reverses |
|---|---|---|
| Proxy calls | static | Finds the delegate-map resource by trial-decrypting each resource with Reactor's keyless word-keystream cipher and checking for valid (field → method) token pairs. Rewrites `ldsfld <proxyField>; call <Delegate>::Invoker` into `call`/`callvirt <real target>` (bit `0x40000000` = callvirt) |
| Predicate helpers | static | Inlines `return null==null`, `return <never-assigned field> == null`, `return <const>` helpers, skipping Reactor's `br; call <invalid>` anti-decompiler prologue |
| Folding | static | Per-block abstract stack: folds int arithmetic/compare, `brtrue/brfalse/bcc/switch` on constants → `br`/`nop`. Iterates until a fixpoint |
| Opaque constants | dynamic | Reads the `<Module>{GUID}` opaque-predicate struct (filled by Reactor VM init) and folds `ldsfld S; ldfld m_…` |
| Strings | dynamic | Finds `string(int)` decryptors (StackFrame + Encoding.Unicode signature) and replaces constant call sites with `ldstr` |
| Int tables / CF helpers | dynamic | Folds `int(int)` helpers (Reactor constant tables and pure control-flow helpers) with constant args |
| String XOR helpers | dynamic | Folds `string(string,int)` helpers when both args are constant, so stage-2 strings come out fully decoded |

## Unflattening (`Unflattener.cs`)
Reactor flattens each method into a `switch` dispatcher. Every real block pushes the next state on the **evaluation stack** (usually through an opaque `brfalse` that keeps or replaces it) and jumps straight into the `switch`, or stores it to a local and jumps to `ldloc; switch`. The pass works as follows:
1. Builds a CFG and computes entry stack depths, forward constant propagation over primitive locals, and backward liveness (exception handlers count as successors of their try blocks).
2. For each edge B→D, simulates the **pure** dispatcher blocks from D using B's exit state (locals plus stack). Pure means constant arithmetic, loads/stores of known values, pops, and decided branches. It stops at the first real block T, and requires at least one bypassed decision.
3. Accepts the path only if the stack at T is B's untouched items plus known constants, the depth matches, and the EH region matches (entering a `try` at its first instruction is allowed). It rewrites the edge as `pop×n; ldc…; ldc/stloc for each dispatcher-changed local live at T; br T`. Conditional/switch edges that need a replay go through a trampoline placed after an unconditional instruction in the same region.
4. Iterates to a fixpoint, then removes unreachable blocks, dead stores, and `ldc/ldloc; pop` pairs.

Safety: each method is snapshotted before the pass and restored if it throws or if dnlib's stack calculator rejects the result (when the original passed). In this case **0 methods were reverted** in either stage.

## Results on this case
| | Stage 1 | Stage 2 |
|---|---|---|
| Proxy calls restored | 2,732 | n/a (none used) |
| Predicate calls inlined | 1,790 | 202 |
| Opaque constants folded | 167 | 2,368 |
| Int-table / CF calls folded | 0 | 4,046 |
| Strings decrypted (+ XOR folded) | 17 | 184 (+320) |
| Branches folded | 2,099 | 2,816 |
| **Dispatcher edges threaded** | **6,345** | **15,999** |
| **Dead dispatcher instructions removed** | **22,023** | **87,764** |
| Dead stores removed | 3,883 | 4,007 |
| Methods reverted by safety check | 0 | 0 |
| Output size (input) | 469 KB (572 KB) | 190 KB (425 KB) |

Outputs: `final\stage1.deobf.exe.infected`, `final\stage2.deobf.dll.infected`, `final\stage*.strings.txt`, `final\stage*.log.txt`. Both load and IL-walk cleanly and decompile in dnSpy to near-source code. For example, stage-1 `Main` is now:
```csharp
ResourceResolver.Install();
try { byte[] kgrjqcz = Resources.Ojrntjghte;
      new PipelineRunner(new CryptoConfig("j2c8AnTg7gDjq4ITR+gy1A==", "Vc5iY6qJq2c=")).Run(kgrjqcz); }
catch { }
```

## Limitations
- **Residual `goto`s.** The decompiler sometimes still emits labels where the original block order was scrambled. The logic is linear, but block order is not restored.
- **Reactor VM methods are not devirtualized** (e.g. stage-1 `Reactor.Runtime::uXXNaxhTdZ`); their effects are recovered dynamically instead.
- **Resource encryption is not undone in-place.** The stage-1 resources assembly was recovered separately (`extracted\stage1_reactor_resources_asm.bin.infected`).
- Output is for **analysis only**: anti-tamper will reject it at runtime, and renaming skips virtual/interface members.
- Heuristics (decryptor signature, helper purity) are tuned to this Reactor build; other builds may need adjustment.
