/-
Audit instrument: project-`Prop` interfaces consumed as hypotheses but never established.

Run from `formal/` after editing the import to the theorem-area umbrella of interest:

    lake env lean ../scripts/lean/audit_corpus_props.lean

For every project constant the statement is telescoped (non-reducing).  A `Prop` binder whose head
is itself a project constant is a *consumed interface*.  A conclusion contributes *produced*
interfaces through `∃`, `Nonempty`, `∧`, both sides of `↔`, and under leading binders.

Two rounds are reported:

* **round 1** — consumed but never concluded anywhere: nothing in the corpus establishes them, not
  even conditionally;
* **round 2** — the grounding least fixpoint.  `P` is *grounded* when some theorem concludes `P` and
  every project-`Prop` hypothesis of that theorem is already grounded.  An `↔`-characterization
  therefore no longer grounds its left side for free.

Both directions are approximations, so every row is a nomination to be checked by hand: a producer
whose conclusion is a *container* of the interface, or an instance, stays invisible.
-/
import GaloisForLFunctions.MainTheorems

open Lean Meta Elab Command

def isProj (n : Name) : Bool := (`GaloisForLFunctions).isPrefixOf n

/-- Split a conclusion into the atoms it actually asserts. -/
partial def conclAtoms (e : Expr) : MetaM (Array Expr) := do
  if e.isForall then
    return ← forallTelescope e fun _ b => conclAtoms b
  match e.getAppFn.constName? with
  | some ``ExistsUnique =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        lambdaTelescope args[1]! fun _ b => conclAtoms b
      else return #[e]
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

/-- The project-`Prop` heads consumed as hypotheses, and the project heads asserted. -/
def scanOne (ty : Expr) : MetaM (Array Name × Array Name) :=
  forallTelescope ty fun xs body => do
    let mut ps : Array Name := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        match t.getAppFn.constName? with
        | some h => if isProj h then ps := ps.push h
        | none => pure ()
    let atoms ← conclAtoms body
    let mut pr : Array Name := #[]
    for a in atoms do
      match a.getAppFn.constName? with
      | some h => if isProj h then pr := pr.push h
      | none => pure ()
    return (ps, pr)

run_cmd liftTermElabM do
  let env ← getEnv
  -- consumers[P] = number of project theorems taking `P` as a hypothesis
  let mut consumers : Std.HashMap Name Nat := {}
  -- defining module of each project constant
  let mut defMod : Std.HashMap Name Name := {}
  -- producers: (conclusion atoms, premise interfaces) of each project constant
  let mut prods : Array (Array Name × Array Name) := #[]
  let mut nthm : Nat := 0
  let mut propDefs : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf m do continue
    defMod := defMod.insert n m
    nthm := nthm + 1
    -- is `n` itself a `Prop`-valued definition (an interface)?
    let isInterface ← forallTelescope ci.type fun _ b => do
      return b.isSort && b == .sort .zero
    if isInterface then propDefs := propDefs.insert n
    let r ← (try scanOne ci.type catch _ => pure (#[], #[]))
    for k in r.1 do
      consumers := consumers.insert k ((consumers.getD k 0) + 1)
    prods := prods.push r
  -- round 1: concluded anywhere at all
  let mut concluded : Std.HashSet Name := {}
  for (_, pr) in prods do
    for a in pr do concluded := concluded.insert a
  let mut row1 : Array (Nat × Name) := #[]
  for (p, c) in consumers.toList do
    unless concluded.contains p do row1 := row1.push (c, p)
  -- round 2: grounding least fixpoint
  let mut grounded : Std.HashSet Name := {}
  let mut changed := true
  while changed do
    changed := false
    for (ps, pr) in prods do
      if ps.all (fun q => grounded.contains q) then
        for a in pr do
          unless grounded.contains a do
            grounded := grounded.insert a
            changed := true
  let mut row2 : Array (Nat × Name) := #[]
  for (p, c) in consumers.toList do
    unless grounded.contains p do row2 := row2.push (c, p)
  let s1 := row1.qsort (fun a b => a.1 > b.1)
  let s2 := row2.qsort (fun a b => a.1 > b.1)
  logInfo m!"constants {nthm}; propDefs {propDefs.size}; consumed {consumers.size}; \
never-concluded {s1.size}; ungrounded {s2.size}"
  logInfo m!"--- never concluded ---"
  for r in s1 do
    logInfo m!"{r.1}  {r.2}   [{defMod.getD r.2 `_}]"
  logInfo m!"--- ungrounded (fixpoint) ---"
  for r in s2 do
    logInfo m!"{r.1}  {r.2}   [{defMod.getD r.2 `_}]"
