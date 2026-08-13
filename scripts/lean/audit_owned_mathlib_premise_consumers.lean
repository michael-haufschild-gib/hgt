/-
Trace audit for mathlib-headed `Prop` premises on project objects.

Unlike `audit_mathlib_premises_calibrated.lean`, this instrument records every consuming
declaration and reports `RHTower` and `HTGeometry` separately in one environment traversal.
Rows remain nominations: dependent recursors, structure constructors, and conclusions whose
logical shape differs from their premise can still hide producers.

Run from `formal/`:

    lake env lean ../scripts/lean/audit_owned_mathlib_premise_consumers.lean
-/
import GaloisForLFunctions.MainTheorems

open Lean Meta Elab Command

abbrev PremiseKey := Name × List Name

def isProjectConstant (n : Name) : Bool := (`GaloisForLFunctions).isPrefixOf n

def isInstanceName (n : Name) : Bool :=
  n.components.any fun c => c.toString.startsWith "inst"

def allInstances (cs : List Name) : Bool := cs.all isInstanceName

def projectConstants (e : Expr) : List Name :=
  (e.getUsedConstants.foldl
    (fun (s : NameSet) n => if isProjectConstant n then s.insert n else s) {}).toList

partial def conclusionKeys (e : Expr) : MetaM (Array PremiseKey) := do
  if e.isForall then
    return ← forallTelescope e fun _ body => conclusionKeys body
  let cs := projectConstants e
  match e.getAppFn.constName? with
  | some ``ExistsUnique =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        let inner ← lambdaTelescope args[1]! fun _ body => conclusionKeys body
        return (inner.push (``ExistsUnique, cs)).push (``Exists, cs)
      else return #[(``ExistsUnique, cs), (``Exists, cs)]
  | some ``Exists =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return (← lambdaTelescope args[1]! fun _ body => conclusionKeys body).push (``Exists, cs)
      else return #[(``Exists, cs)]
  | some ``Nonempty =>
      let args := e.getAppArgs
      if args.size ≥ 1 then
        return (← conclusionKeys args[0]!).push (``Nonempty, cs)
      else return #[(``Nonempty, cs)]
  | some ``And =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return ((← conclusionKeys args[0]!) ++ (← conclusionKeys args[1]!)).push (``And, cs)
      else return #[(``And, cs)]
  | some ``Iff =>
      let args := e.getAppArgs
      if args.size ≥ 2 then
        return ((← conclusionKeys args[0]!) ++ (← conclusionKeys args[1]!)).push (``Iff, cs)
      else return #[(``Iff, cs)]
  | some ``Finset.Nonempty =>
      return #[(``Finset.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``Set.Nonempty =>
      return #[(``Set.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``Set.Infinite =>
      return #[(``Set.Infinite, cs), (``Set.Nonempty, cs), (``Membership.mem, cs), (``Exists, cs)]
  | some ``LT.lt => return #[(``LT.lt, cs), (``Ne, cs), (``LE.le, cs)]
  | some ``GT.gt => return #[(``GT.gt, cs), (``LT.lt, cs), (``Ne, cs)]
  | some head => return #[(head, cs)]
  | none => return #[]

def scanDeclaration (type : Expr) : MetaM (Array PremiseKey × Array PremiseKey) :=
  forallTelescope type fun xs body => do
    let mut premises : Array PremiseKey := #[]
    for x in xs do
      let type ← inferType x
      if (← isProp type) then
        match type.getAppFn.constName? with
        | some head =>
            if !isProjectConstant head then
              let cs := projectConstants type
              if !cs.isEmpty && !allInstances cs then
                premises := premises.push (head, cs)
        | none => pure ()
    return (premises, ← conclusionKeys body)

def addConsumer (m : Std.HashMap PremiseKey (Array Name)) (key : PremiseKey) (consumer : Name) :
    Std.HashMap PremiseKey (Array Name) :=
  m.insert key ((m.getD key #[]).push consumer)

def unproducedRows (premises : Std.HashMap PremiseKey (Array Name))
    (produced : Std.HashSet PremiseKey) : Array (Array Name × PremiseKey) := Id.run do
  let mut rows : Array (Array Name × PremiseKey) := #[]
  for (key, consumers) in premises.toList do
    let (head, cs) := key
    let mut found := false
    for (head', cs') in produced.toList do
      if head' == head && cs.all (fun c => cs'.contains c) then
        found := true
        break
    unless found do rows := rows.push (consumers, key)
  return rows.qsort fun a b => a.1.size > b.1.size

run_cmd liftTermElabM do
  let env ← getEnv
  let mut rhtPremises : Std.HashMap PremiseKey (Array Name) := {}
  let mut htPremises : Std.HashMap PremiseKey (Array Name) := {}
  let mut hmPremises : Std.HashMap PremiseKey (Array Name) := {}
  let mut produced : Std.HashSet PremiseKey := {}
  let mut declarations : Nat := 0
  for (name, info) in env.constants.toList do
    if name.isInternal then continue
    unless isProjectConstant name do continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    unless (`GaloisForLFunctions).isPrefixOf moduleName do continue
    declarations := declarations + 1
    let result ← (try scanDeclaration info.type catch _ => pure (#[], #[]))
    if (`GaloisForLFunctions.RHTower).isPrefixOf moduleName then
      for key in result.1 do rhtPremises := addConsumer rhtPremises key name
    if (`GaloisForLFunctions.HTGeometry).isPrefixOf moduleName then
      for key in result.1 do htPremises := addConsumer htPremises key name
    if (`GaloisForLFunctions.HilbertMetric).isPrefixOf moduleName then
      for key in result.1 do hmPremises := addConsumer hmPremises key name
    for key in result.2 do produced := produced.insert key
  let rhtRows := unproducedRows rhtPremises produced
  let htRows := unproducedRows htPremises produced
  let hmRows := unproducedRows hmPremises produced
  logInfo m!"scanned {declarations}; conclusionKeys {produced.size}"
  logInfo m!"=== RHTower: premiseKeys {rhtPremises.size}; unproduced {rhtRows.size} ==="
  for row in rhtRows do
    logInfo m!"{row.1.size}  {row.2.1}  {row.2.2}  <- {row.1}"
  logInfo m!"=== HTGeometry: premiseKeys {htPremises.size}; unproduced {htRows.size} ==="
  for row in htRows do
    logInfo m!"{row.1.size}  {row.2.1}  {row.2.2}  <- {row.1}"
  logInfo m!"=== HilbertMetric: premiseKeys {hmPremises.size}; unproduced {hmRows.size} ==="
  for row in hmRows do
    logInfo m!"{row.1.size}  {row.2.1}  {row.2.2}  <- {row.1}"
