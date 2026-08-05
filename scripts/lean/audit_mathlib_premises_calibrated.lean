/-
Mathlib-premise instrument, calibrated.

Three ways a real producer hid from the first version, all measured this session:

* its conclusion is a *container* of the existential (`Finset.Nonempty`, `Set.Nonempty`,
  `Set.Infinite`) rather than a membership;
* its conclusion has a different *head* from the premise (`0 < X` against `X ≠ 0`);
* (not fixable by unfolding) it is general and never mentions the consumer's corpus constants.

This version emits the extra conclusion keys for the first two, so the nomination list is closer to
genuine debt.  The premise side is unchanged.
-/
import GaloisForLFunctions.RHTower
import GaloisForLFunctions.HTGeometry
import GaloisForLFunctions.HilbertMetric

open Lean Meta Elab Command

def isProj (n : Name) : Bool := (`GaloisForLFunctions).isPrefixOf n

def isInstName (n : Name) : Bool :=
  n.components.any fun c => c.toString.startsWith "inst"

def allInstance (cs : List Name) : Bool := cs.all isInstName

def projConsts (e : Expr) : List Name :=
  (e.getUsedConstants.foldl
    (fun (s : NameSet) n => if isProj n then s.insert n else s) {}).toList

/-- Conclusion keys, with the container and head bridges. -/
partial def conclKeys (e : Expr) : MetaM (Array (Name × List Name)) := do
  if e.isForall then
    return ← forallTelescope e fun _ b => conclKeys b
  match e.getAppFn.constName? with
  | some ``Exists =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        let inner ← lambdaTelescope args[1]! fun _ b => conclKeys b
        return inner.push (``Exists, projConsts e)
      else return #[(``Exists, projConsts e)]
  | some ``Nonempty =>
      let args := e.getAppArgs
      if args.size ≥ 1 then
        let inner ← conclKeys args[0]!
        return inner.push (``Nonempty, projConsts e)
      else return #[(``Nonempty, projConsts e)]
  | some ``And =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return ((← conclKeys args[0]!) ++ (← conclKeys args[1]!)).push (``And, projConsts e)
      else return #[(``And, projConsts e)]
  | some ``Iff =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return ((← conclKeys args[0]!) ++ (← conclKeys args[1]!)).push (``Iff, projConsts e)
      else return #[(``Iff, projConsts e)]
  | some ``Finset.Nonempty =>
      let cs := projConsts e
      return #[(``Finset.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``Set.Nonempty =>
      let cs := projConsts e
      return #[(``Set.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``Set.Infinite =>
      let cs := projConsts e
      return #[(``Set.Infinite, cs), (``Set.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``LT.lt =>
      let cs := projConsts e
      return #[(``LT.lt, cs), (``Ne, cs), (``LE.le, cs)]
  | some ``GT.gt =>
      let cs := projConsts e
      return #[(``GT.gt, cs), (``LT.lt, cs), (``Ne, cs)]
  | some h => return #[(h, projConsts e)]
  | none => return #[]

def inArea (m : Name) : Bool := (`GaloisForLFunctions.RHTower).isPrefixOf m

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
                if !cs.isEmpty && !allInstance cs then ps := ps.push (h, cs)
          | none => pure ()
    let pr ← conclKeys body
    return (ps, pr)

run_cmd liftTermElabM do
  let env ← getEnv
  let mut premises : Std.HashMap (Name × List Name) Nat := {}
  let mut produced : Std.HashSet (Name × List Name) := {}
  let mut nthm : Nat := 0
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
  logInfo m!"scanned {nthm}; premiseKeys {premises.size}; conclKeys {produced.size}; unproduced {rows.size}"
  for r in rows[0:30] do
    logInfo m!"{r.1}  {r.2.1}   {r.2.2}"
