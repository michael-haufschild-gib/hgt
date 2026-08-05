/-
Audit instrument: which corpus declarations depend on axioms beyond the standard three.

`propext`, `Classical.choice` and `Quot.sound` are the accepted foundation.  Anything else —
`Lean.ofReduceBool` from `native_decide`, `sorryAx`, a user axiom — makes a result conditional in
the kernel sense.  This scans every declaration of the imported area and reports the offenders,
grouped by the extra axiom, together with the size of their union.

Run from `formal/` with the theorem-area umbrella of interest as the import:

    lake env lean ../scripts/lean/audit_extra_axioms.lean

Measured 2026-08-05: `HTGeometry ∪ RHTower ∪ HilbertMetric` (160 938 declarations), `PNTPlus`
(1 209) and `QuantumAlg` (19 512) are all clean.  `QECLean` (4 253) has 279 distinct
`native_decide` axioms tainting 486 declarations, all in the bivariate-bicycle layer.
-/
import GaloisForLFunctions.QECLean
import Lean.Util.CollectAxioms

open Lean Meta Elab Command

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd liftTermElabM do
  let env ← getEnv
  let mut offenders : Std.HashMap Name (Array Name) := {}
  let mut scanned : Nat := 0
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf m do continue
    scanned := scanned + 1
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless stdAxioms.contains a do
        offenders := offenders.insert a ((offenders.getD a #[]).push n)
  let mut tainted : Std.HashSet Name := {}
  for (_, ns) in offenders.toList do
    for n in ns do tainted := tainted.insert n
  logInfo m!"scanned {scanned}; extra-axiom kinds {offenders.size}; tainted declarations {tainted.size}"
  for (a, ns) in offenders.toList do
    logInfo m!"{a}: {(ns : Array Name).size}"
