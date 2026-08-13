/-
Audit instrument: project-`Prop` interfaces consumed as hypotheses but never established.

Run from `formal/` after editing the import to the theorem-area umbrella of interest:

    lake env lean ../scripts/lean/audit_corpus_props.lean

For every project constant the statement is telescoped (non-reducing).  A `Prop` binder whose head
is itself a project constant is a *consumed interface*.  A conclusion contributes *produced*
interfaces through `∃`, `Nonempty`, `∧`, and under leading binders.  An `↔` alone establishes
neither side, so it is deliberately not a producer.

Two rounds are reported:

* **round 1** — consumed but never concluded anywhere: nothing in the corpus establishes them, not
  even conditionally;
* **round 2** — the grounding least fixpoint.  `P` is *grounded* when some theorem concludes `P` and
  every project-`Prop` hypothesis of that theorem is already grounded.  An `↔`-characterization
  therefore no longer grounds its left side for free.

Both directions are approximations, so every row is a nomination to be checked by hand: a producer
whose conclusion is a *container* of the interface, or an instance, stays invisible.
-/
import GaloisForLFunctions.HTGeometry
import GaloisForLFunctions.RHTower
import GaloisForLFunctions.HilbertMetric

open Lean Meta Elab Command

def isProj (n : Name) : Bool := (`GaloisForLFunctions).isPrefixOf n

/-- `P (x : α) : Prop` has constant type `∀ x, Prop`; recognizing that shape needs no elaboration. -/
partial def isInterfaceType : Expr → Bool
  | .forallE _ _ body _ => isInterfaceType body
  | .sort .zero => true
  | _ => false

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
      return #[]
  | _ => return #[e]

/-- The project-`Prop` heads consumed as hypotheses, and the project heads asserted. -/
def scanOne (propDefs : Std.HashSet Name) (ty : Expr) : MetaM (Array Name × Array Name) :=
  forallTelescope ty fun xs body => do
    let mut premiseSet : Std.HashSet Name := {}
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        for h in t.getUsedConstants do
          if propDefs.contains h then premiseSet := premiseSet.insert h
    let atoms ← conclAtoms body
    let mut conclusionSet : Std.HashSet Name := {}
    for a in atoms do
      match a.getAppFn.constName? with
      | some h => if propDefs.contains h then conclusionSet := conclusionSet.insert h
      | none => pure ()
    return (premiseSet.toList.toArray, conclusionSet.toList.toArray)

run_cmd liftTermElabM do
  let env ← getEnv
  -- consumers[P] = project declarations taking `P` as a hypothesis
  let mut consumers : Std.HashMap Name (Array Name) := {}
  -- defining module of each project constant
  let mut defMod : Std.HashMap Name Name := {}
  -- producers: (conclusion atoms, premise interfaces) of each project constant
  let mut prods : Array (Name × Array Name × Array Name) := #[]
  let mut producerNames : Std.HashMap Name (Array Name) := {}
  let mut nthm : Nat := 0
  let mut propDefs : Std.HashSet Name := {}
  let constants := env.constants.toList
  -- First identify interfaces.  The second pass can then reject irrelevant declarations without
  -- invoking the meta elaborator and can see interfaces nested inside compound hypotheses.
  for (n, ci) in constants do
    if n.isInternal then continue
    unless isProj n do continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf m do continue
    defMod := defMod.insert n m
    nthm := nthm + 1
    if isInterfaceType ci.type then propDefs := propDefs.insert n
  for (n, ci) in constants do
    if n.isInternal then continue
    unless isProj n do continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf m do continue
    unless ci.type.getUsedConstants.any propDefs.contains do continue
    let r ← (try scanOne propDefs ci.type catch _ => pure (#[], #[]))
    for k in r.1 do
      consumers := consumers.insert k ((consumers.getD k #[]).push n)
    for k in r.2 do
      producerNames := producerNames.insert k ((producerNames.getD k #[]).push n)
    prods := prods.push (n, r.1, r.2)
  -- round 1: concluded anywhere at all
  let mut concluded : Std.HashSet Name := {}
  for (_, _, pr) in prods do
    for a in pr do concluded := concluded.insert a
  let mut row1 : Array (Nat × Name) := #[]
  for (p, cs) in consumers.toList do
    unless concluded.contains p do row1 := row1.push (cs.size, p)
  -- round 2: grounding least fixpoint.  Use a dependency-indexed worklist rather than repeatedly
  -- scanning every declaration: long connector chains then cost O(edges), not O(depth * corpus).
  let mut grounded : Std.HashSet Name := {}
  let mut remaining : Std.HashMap Nat Nat := {}
  let mut waiting : Std.HashMap Name (Array Nat) := {}
  let mut queue : Array Name := #[]
  for i in [:prods.size] do
    let (_, ps, pr) := prods[i]!
    let mut deps : Std.HashSet Name := {}
    for p in ps do deps := deps.insert p
    remaining := remaining.insert i deps.size
    for p in deps.toList do
      waiting := waiting.insert p ((waiting.getD p #[]).push i)
    if deps.isEmpty then
      for a in pr do
        unless grounded.contains a do
          grounded := grounded.insert a
          queue := queue.push a
  let mut head := 0
  while head < queue.size do
    let p := queue[head]!
    head := head + 1
    for i in waiting.getD p #[] do
      let left := remaining.getD i 0
      if left > 0 then
        let next := left - 1
        remaining := remaining.insert i next
        if next == 0 then
          let (_, _, pr) := prods[i]!
          for a in pr do
            unless grounded.contains a do
              grounded := grounded.insert a
              queue := queue.push a
  let mut row2 : Array (Nat × Name) := #[]
  for (p, cs) in consumers.toList do
    unless grounded.contains p do row2 := row2.push (cs.size, p)
  let s1 := row1.qsort (fun a b => a.1 > b.1)
  let s2 := row2.qsort (fun a b => a.1 > b.1)
  logInfo m!"constants {nthm}; propDefs {propDefs.size}; consumed {consumers.size}; \
never-concluded {s1.size}; ungrounded {s2.size}"
  logInfo m!"--- never concluded ---"
  for r in s1 do
    logInfo m!"{r.1}  {r.2}   [{defMod.getD r.2 `_}] <- {consumers.getD r.2 #[]}"
  logInfo m!"--- ungrounded (fixpoint) ---"
  for r in s2 do
    logInfo m!"{r.1}  {r.2}   [{defMod.getD r.2 `_}] <- {consumers.getD r.2 #[]}; produced by {producerNames.getD r.2 #[]}"
