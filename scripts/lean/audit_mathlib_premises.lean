/-
Audit instrument: mathlib-`Prop` premises applied to corpus objects that no corpus theorem produces.

Run from `formal/` with the theorem-area umbrella of interest as the import:

    lake env lean ../scripts/lean/audit_mathlib_premises.lean

For every project constant it telescopes the statement (non-reducing), keys each `Prop` binder by
its head constant together with the set of `GaloisForLFunctions` constants occurring in it, and
compares against the conclusion atoms of every project constant.  A conclusion contributes atoms
through `∃`, `Nonempty`, `∧`, both sides of `↔`, and under leading binders; a premise key counts as
produced when some atom has the same head over a superset of its corpus constants.  Anything left is
a nomination, not a verdict: producers whose conclusion is a container of the target, or an instance,
remain invisible, as do producers that *specialize* a parameter (their conclusion drops the
constants the general premise mentions).  Two further false-positive classes, both seen in practice:
a premise `x ≠ y` between two elements of a corpus *type* is a parameter constraint, not debt; and a
premise satisfied only by a specialized producer shows up because the superset test is on constants,
not on unification.
-/
import GaloisForLFunctions.HilbertMetric

open Lean Meta Elab Command

def isProj (n : Name) : Bool := (`GaloisForLFunctions).isPrefixOf n

def projConsts (e : Expr) : List Name :=
  (e.getUsedConstants.foldl
    (fun (s : NameSet) n => if isProj n then s.insert n else s) {}).toList

/-- Split a conclusion into the atoms it actually asserts: existentials, `Nonempty`,
conjunctions and both sides of an `Iff` all count as produced. -/
partial def conclAtoms (e : Expr) : MetaM (Array Expr) := do
  if e.isForall then
    return ← forallTelescope e fun _ b => conclAtoms b
  match e.getAppFn.constName? with
  | some ``Exists =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        lambdaTelescope args[1]! fun _ b => conclAtoms b
      else return #[e]
  | some ``Nonempty =>
      let args := e.getAppArgs
      if args.size ≥ 1 then conclAtoms args[0]! else return #[e]
  | some ``And =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return (← conclAtoms args[0]!) ++ (← conclAtoms args[1]!)
      else return #[e]
  | some ``Iff =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return (← conclAtoms args[0]!) ++ (← conclAtoms args[1]!)
      else return #[e]
  | _ => return #[e]

def inArea (m : Name) : Bool :=
  (`GaloisForLFunctions.HilbertMetric).isPrefixOf m ||
  (`GaloisForLFunctions.HTGeometry).isPrefixOf m ||
  (`GaloisForLFunctions.RHTower).isPrefixOf m

def scanOne (ty : Expr) (isInside : Bool) :
    MetaM (Array (Name × List Name) × Array (Name × List Name)) :=
  forallTelescope ty fun xs body => do
    let mut ps : Array (Name × List Name) := #[]
    if isInside then
      for x in xs do
        let t ← inferType x
        if (← isProp t) then
          match t.getAppFn.constName? with
          | some h =>
              if !isProj h then
                let cs := projConsts t
                if !cs.isEmpty then ps := ps.push (h, cs)
          | none => pure ()
    let atoms ← conclAtoms body
    let mut pr : Array (Name × List Name) := #[]
    for a in atoms do
      match a.getAppFn.constName? with
      | some h => pr := pr.push (h, projConsts a)
      | none => pure ()
    return (ps, pr)

run_cmd liftTermElabM do
  let env ← getEnv
  let mut premises : Std.HashMap (Name × List Name) Nat := {}
  let mut produced : Std.HashSet (Name × List Name) := {}
  let mut nthm := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf m do continue
    nthm := nthm + 1
    let r ← (try scanOne ci.type (inArea m) catch _ => pure (#[], #[]))
    for k in r.1 do
      premises := premises.insert k ((premises.getD k 0) + 1)
    for k in r.2 do
      produced := produced.insert k
  let mut openRows : Array (Nat × Name × List Name) := #[]
  for (k, cnt) in premises.toList do
    let (h, cs) := k
    let mut ok := false
    for (h', cs') in produced.toList do
      if h' == h && cs.all (fun c => cs'.contains c) then
        ok := true
        break
    unless ok do
      openRows := openRows.push (cnt, h, cs)
  let rows := openRows.qsort (fun a b => a.1 > b.1)
  logInfo m!"scanned {nthm}; premiseKeys {premises.size}; conclAtoms {produced.size}; unproduced {rows.size}"
  for r in rows[0:40] do
    logInfo m!"{r.1}  {r.2.1}   {r.2.2}"
