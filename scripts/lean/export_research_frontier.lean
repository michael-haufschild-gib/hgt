import Lean
import Lean.DocString
import Lean.Meta.Tactic.Apply
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import GaloisForLFunctions

/-!
Compiler-derived exporter for research-frontier logic.

It emits only checked theorem interfaces between named project propositions.
Proof constants are exported for retrieval/audit but never become logical edges.
-/

open Lean Elab Command Meta

set_option maxHeartbeats 8000000

private def interfaceSolverMaxDepth : Nat := 3
private def interfaceSolverMaxCandidatesPerGoal : Nat := 512
private def interfaceSolverMaxAttemptsPerInterface : Nat := 20

private def projectPrefix : String := "GaloisForLFunctions."

private inductive InterfaceLocation where
  | binder (index : Nat)
  | iffLeft
  | iffRight

private structure InterfaceSpec where
  sourceTheorem : Name
  location : InterfaceLocation
  ref : Json
  key : String

private structure InspectedTheorem where
  row : Json
  interfaces : Array InterfaceSpec
  closedKeys : Array String

private structure Producer where
  name : Name
  heads : Array String

private abbrev ProducerIndex := Std.HashMap String (Array Producer)

private structure SolverResult where
  proof : Expr
  usedTheorems : Array Name
  depth : Nat
  attempts : Nat

private def moduleFor? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? declName
  env.header.moduleNames[moduleIdx.toNat]?

private def isProjectDeclaration (env : Environment) (declName : Name) : Bool :=
  match moduleFor? env declName with
  | some moduleName => moduleName.toString.startsWith projectPrefix
  | none => false

private def headDeclaration? (expr : Expr) : Option Name :=
  match expr.getAppFn with
  | .const name _ => some name
  | _ => none

private def isNamedResearchProposition (env : Environment) (expr : Expr) : Bool :=
  match headDeclaration? expr with
  | some name => name == ``RiemannHypothesis || isProjectDeclaration env name
  | none => false

private def propositionJson (expr : Expr) : Json :=
  let declaration? := headDeclaration? expr
  let expression := expr.dbgToString
  let key := expression
  Json.mkObj [
    ("key", toJson key),
    ("expression", toJson expression),
    ("declaration", declaration?.map (toJson ·.toString) |>.getD Json.null)
  ]

private def namesJson (names : Array Name) : Json :=
  toJson <| names.qsort Name.quickLt |>.map (·.toString)

private def sourcePath (moduleName : String) : String :=
  "formal/" ++ String.intercalate "/" (moduleName.splitOn ".") ++ ".lean"

private def telescopeDomains : Expr → Array Expr → Array Expr × Expr
  | .forallE _ domain body _, domains => telescopeDomains body (domains.push domain)
  | result, domains => (domains, result)

private def isPropositionFormerType : Expr → Bool
  | .forallE _ _ body _ => isPropositionFormerType body
  | body => body.isProp

private def isPropositionExpression (env : Environment) : Expr → Bool
  | .forallE _ _ body _ => isPropositionExpression env body
  | expression =>
      match headDeclaration? expression with
      | some head =>
          head == ``RiemannHypothesis ||
            match env.find? head with
            | some info => isPropositionFormerType info.type
            | none => false
      | none => false

private def inspectTheorem? (declName : Name) : MetaM (Option InspectedTheorem) := do
  let env ← getEnv
  let info ← getConstInfo declName
  let (domains, result) := telescopeDomains info.type #[]
  let mut propositionBinders : Array Expr := #[]
  let mut interfaces : Array InterfaceSpec := #[]
  let mut hasUnnamedPropositionBinder := false
  let mut domainIndex := 0
  for domain in domains do
    if isPropositionExpression env domain then
      propositionBinders := propositionBinders.push domain
      if isNamedResearchProposition env domain then
        let ref := propositionJson domain
        interfaces := interfaces.push {
          sourceTheorem := declName
          location := .binder domainIndex
          ref
          key := domain.dbgToString
        }
      else
        hasUnnamedPropositionBinder := true
    domainIndex := domainIndex + 1

  let mut relation := "implication"
  let mut premises : Array Expr := propositionBinders
  let mut conclusions : Array Expr := #[]
  if result.isAppOfArity ``Iff 2 then
    let arguments := result.getAppArgs
    let left := arguments[0]!
    let right := arguments[1]!
    unless isPropositionExpression env left && isPropositionExpression env right do
      return none
    relation := "iff"
    premises := #[left]
    conclusions := #[right]
    if isNamedResearchProposition env left then
      interfaces := interfaces.push {
        sourceTheorem := declName
        location := .iffLeft
        ref := propositionJson left
        key := left.dbgToString
      }
    if isNamedResearchProposition env right then
      interfaces := interfaces.push {
        sourceTheorem := declName
        location := .iffRight
        ref := propositionJson right
        key := right.dbgToString
      }
  else if result.isAppOfArity ``Not 1 then
    let proposition := result.getAppArgs[0]!
    unless isPropositionExpression env proposition do return none
    unless propositionBinders.isEmpty do return none
    relation := "refutation"
    premises := #[]
    conclusions := #[proposition]
  else
    unless isPropositionExpression env result do return none
    conclusions := #[result]

  if hasUnnamedPropositionBinder then return none

  let typeText := info.type.dbgToString
  let doc := (docStringExt.find? (level := .server) env declName).getD ""
  let moduleName := (moduleFor? env declName).map (·.toString) |>.getD ""
  let premiseJson := premises.map propositionJson
  let conclusionJson := conclusions.map propositionJson
  let row := Json.mkObj [
    ("name", toJson declName.toString),
    ("module", toJson moduleName),
    ("type_text", toJson typeText),
    ("premises", toJson premiseJson),
    ("conclusions", toJson conclusionJson),
    ("relation", toJson relation),
    ("status", toJson "live"),
    ("type_dependencies", namesJson info.type.getUsedConstants),
    -- Proof-body indexing is a separate corpus-retrieval artifact.  Logical
    -- frontier refresh must not traverse every proof term.
    ("proof_dependencies", toJson (#[] : Array String)),
    -- Fast frontier refresh exports direct logic.  Full axiom audit remains the
    -- existing project lint gate and is intentionally not repeated per row.
    ("axioms", toJson (#[] : Array String)),
    ("doc", toJson doc),
    ("source", Json.mkObj [
      ("path", toJson (sourcePath moduleName)),
      ("line", toJson (0 : Nat))
    ])
  ]
  let closedKeys :=
    if relation == "implication" && propositionBinders.isEmpty then
      conclusions.map (·.dbgToString)
    else #[]
  return some { row, interfaces, closedKeys }

private def exprHeadKey (expr : Expr) : String :=
  match expr.getAppFn with
  | .const name _ => "const:" ++ name.toString
  | .forallE .. => "forall"
  | .sort .. => "sort"
  | .mvar .. => "mvar"
  | .fvar .. => "fvar"
  | .bvar .. => "bvar"
  | .lit .. => "lit"
  | .lam .. => "lambda"
  | .letE .. => "let"
  | .mdata .. => "mdata"
  | .proj name _ _ => "proj:" ++ name.toString
  | .app .. => "app"

private def pushStringUnique (items : Array String) (item : String) : Array String :=
  if items.contains item then items else items.push item

private def expressionHeadKeys (expr : Expr) : MetaM (Array String) := do
  let mut keys := #[exprHeadKey expr]
  let reduced ← withReducible <| whnf expr
  keys := pushStringUnique keys (exprHeadKey reduced)
  for candidate in #[expr, reduced] do
    if candidate.isAppOfArity ``Iff 2 || candidate.isAppOfArity ``And 2 then
      for argument in candidate.getAppArgs do
        keys := pushStringUnique keys (exprHeadKey argument)
        let argumentReduced ← withReducible <| whnf argument
        keys := pushStringUnique keys (exprHeadKey argumentReduced)
  return keys

private def syntacticHeadKeys (expr : Expr) : Array String := Id.run do
  let mut keys := #[exprHeadKey expr]
  if expr.isAppOfArity ``Iff 2 || expr.isAppOfArity ``And 2 then
    for argument in expr.getAppArgs do
      keys := pushStringUnique keys (exprHeadKey argument)
  keys

private def buildProducers (names : Array Name) : MetaM (Array Producer) := do
  let mut producers := #[]
  for name in names.qsort (fun left right => left.toString < right.toString) do
    let info ← getConstInfo name
    let (_, result) := telescopeDomains info.type #[]
    let heads ←
      if result.hasLooseBVars then
        pure (syntacticHeadKeys result)
      else expressionHeadKeys result
    producers := producers.push { name, heads }
  return producers

private def buildProducerIndex (producers : Array Producer) : ProducerIndex :=
  producers.foldl (init := {}) fun index producer =>
    producer.heads.foldl (init := index) fun index head =>
      let bucket := index[head]?.getD #[]
      index.insert head (bucket.push producer)

private def instantiateInterface (spec : InterfaceSpec) : MetaM Expr := do
  let source ← mkConstWithFreshMVarLevels spec.sourceTheorem
  let (arguments, _, result) ← forallMetaTelescopeReducing (← inferType source)
  match spec.location with
  | .binder index =>
      let some argument := arguments[index]?
        | throwError "interface binder {index} missing in {spec.sourceTheorem}"
      inferType argument
  | .iffLeft =>
      unless result.isAppOfArity ``Iff 2 do
        throwError "interface source {spec.sourceTheorem} no longer concludes Iff"
      return result.getAppArgs[0]!
  | .iffRight =>
      unless result.isAppOfArity ``Iff 2 do
        throwError "interface source {spec.sourceTheorem} no longer concludes Iff"
      return result.getAppArgs[1]!

private def definitionallyEqualWithoutAssignment (left right : Expr) : MetaM Bool := do
  let saved ← saveState
  let answer ← withReducible <| isDefEq left right
  restoreState saved
  return answer

private def producerMayMatch (producer : Producer) (goalHeads : Array String) : Bool :=
  producer.heads.any fun head => goalHeads.contains head

private def candidateApplication
    (goal : MVarId) (producer : Name) (mode : Nat) : MetaM (List MVarId) := do
  let config : ApplyConfig := { allowSynthFailures := true }
  if mode == 0 then
    return ← goal.applyConst producer config
  let theoremExpr ← mkConstWithFreshMVarLevels producer
  let (arguments, _, result) ← forallMetaTelescopeReducing (← inferType theoremExpr)
  let proof := mkAppN theoremExpr arguments
  if mode == 1 || mode == 2 then
    unless result.isAppOfArity ``Iff 2 do
      throwError "not an Iff producer"
    let transformer ←
      if mode == 1 then mkAppM ``Iff.mp #[proof] else mkAppM ``Iff.mpr #[proof]
    return ← goal.apply transformer config
  unless result.isAppOfArity ``And 2 do
    throwError "not an And producer"
  let projection ←
    if mode == 3 then mkAppM ``And.left #[proof] else mkAppM ``And.right #[proof]
  goal.apply projection config

private def pushNameUnique (items : Array Name) (item : Name) : Array Name :=
  if items.contains item then items else items.push item

private def appendNamesUnique (items more : Array Name) : Array Name :=
  more.foldl (init := items) pushNameUnique

private partial def solveInterfaceGoal
    (producerIndex : ProducerIndex)
    (goal : MVarId)
    (depth : Nat)
    (ancestors : Array Expr)
    (usedOnPath : NameSet)
    (attempts : IO.Ref Nat) : MetaM (Option (Array Name × Nat)) := do
  if depth == 0 then return none
  let goalType ← instantiateMVars (← goal.getType)
  let goalIsNamedInterface := isNamedResearchProposition (← getEnv) goalType
  for ancestor in ancestors do
    if ← definitionallyEqualWithoutAssignment goalType ancestor then
      return none
  let goalHeads ← expressionHeadKeys goalType
  let mut matching := #[]
  let mut seen : NameSet := {}
  for head in goalHeads do
    if matching.size >= interfaceSolverMaxCandidatesPerGoal then break
    for producer in producerIndex[head]?.getD #[] do
      if matching.size >= interfaceSolverMaxCandidatesPerGoal then break
      if !seen.contains producer.name && producerMayMatch producer goalHeads then
        matching := matching.push producer
        seen := seen.insert producer.name

  for producer in matching do
    if usedOnPath.contains producer.name then continue
    let modes := if goalIsNamedInterface then #[0, 1, 2, 3, 4] else #[0]
    for mode in modes do
      let attempted ← attempts.get
      if attempted >= interfaceSolverMaxAttemptsPerInterface then return none
      attempts.set (attempted + 1)
      let saved ← saveState
      try
        let subgoals ← candidateApplication goal producer.name mode
        let mut used := #[producer.name]
        let mut proofDepth := 1
        let mut solved := true
        for subgoal in subgoals do
          if ← subgoal.isAssigned then continue
          let subgoalType ← instantiateMVars (← subgoal.getType)
          if ← isProp subgoalType then
            let childDepth :=
              if isNamedResearchProposition (← getEnv) subgoalType then depth - 1 else 1
            let result? ← solveInterfaceGoal producerIndex subgoal childDepth
              (ancestors.push goalType) (usedOnPath.insert producer.name) attempts
            match result? with
            | some (childUsed, childDepth) =>
                used := appendNamesUnique used childUsed
                proofDepth := max proofDepth (childDepth + 1)
            | none => solved := false
          else
            try
              let instanceExpr ← synthInstance subgoalType
              subgoal.assign instanceExpr
            catch _ => solved := false
          if !solved then break
        unless solved do throwError "candidate left an unsolved premise"
        let proof ← instantiateMVars (.mvar goal)
        if proof.hasMVar || proof.hasLevelMVar || proof.hasSyntheticSorry then
          throwError "candidate witness contains unresolved or synthetic metavariables"
        check proof
        let proofType ← inferType proof
        unless ← withReducible <| isDefEq proofType (← instantiateMVars goalType) do
          throwError "candidate witness type does not match interface"
        return some (used, proofDepth)
      catch _ =>
        restoreState saved
  return none

private def solveInterface
    (producerIndex : ProducerIndex) (spec : InterfaceSpec) : MetaM (Option SolverResult) := do
  let saved ← saveState
  try
    let target ← instantiateInterface spec
    if ← definitionallyEqualWithoutAssignment target (mkConst ``RiemannHypothesis) then
      restoreState saved
      return none
    let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
    let attempts ← IO.mkRef 0
    let result? ← solveInterfaceGoal producerIndex goalExpr.mvarId! interfaceSolverMaxDepth #[] {} attempts
    match result? with
    | none =>
        restoreState saved
        return none
    | some (usedTheorems, depth) =>
        let proof ← instantiateMVars goalExpr
        let count ← attempts.get
        restoreState saved
        return some { proof, usedTheorems, depth, attempts := count }
  catch _ =>
    restoreState saved
    return none

private def exportResearchFrontier
    (theoremNames producerNames : Array Name) : MetaM Json := do
  let env ← getEnv
  let validateTheorems := fun names => names.filter fun name =>
    isProjectDeclaration env name && env.find? name matches some (.thmInfo _)
  let candidateNames := validateTheorems theoremNames
  let allProjectTheoremNames :=
    if producerNames.isEmpty then
      env.const2ModIdx.toList.toArray.filterMap fun entry =>
        let (declName, moduleIdx) := entry
        match env.header.moduleNames[moduleIdx.toNat]? with
        | some moduleName =>
            if moduleName.toString.startsWith projectPrefix &&
                env.find? declName matches some (.thmInfo _) then
              some declName
            else none
        | none => none
    else validateTheorems producerNames
  logInfo m!"HGT_FRONTIER_PHASE:producer_names={allProjectTheoremNames.size}"
  let producers ← buildProducers allProjectTheoremNames
  logInfo m!"HGT_FRONTIER_PHASE:producer_heads={producers.size}"
  let producerIndex := buildProducerIndex producers
  let mut reductions : Array Json := #[]
  let mut interfaces : Array InterfaceSpec := #[]
  let mut seenInterfaceKeys : Std.HashSet String := {}
  let mut exactClosedKeys : Std.HashSet String := {}
  for declName in candidateNames.qsort (fun left right => left.toString < right.toString) do
    if let some inspected ← inspectTheorem? declName then
      reductions := reductions.push inspected.row
      for key in inspected.closedKeys do
        exactClosedKeys := exactClosedKeys.insert key
      for spec in inspected.interfaces do
        if !seenInterfaceKeys.contains spec.key then
          seenInterfaceKeys := seenInterfaceKeys.insert spec.key
          interfaces := interfaces.push spec

  logInfo m!"HGT_FRONTIER_PHASE:reductions={reductions.size},interfaces={interfaces.size}"
  let mut solvedCount := 0
  let mut checkedCount : Nat := 0
  for spec in interfaces do
    checkedCount := checkedCount + 1
    if checkedCount % 100 == 0 then
      logInfo m!"HGT_FRONTIER_PHASE:interfaces_checked={checkedCount}"
    if exactClosedKeys.contains spec.key then continue
    if let some solved ← solveInterface producerIndex spec then
      let some rootTheorem := solved.usedTheorems[0]? | continue
      let mut axioms : Array Name := #[]
      for theoremName in solved.usedTheorems do
        for axiomName in (← collectAxioms theoremName) do
          if !axioms.contains axiomName then axioms := axioms.push axiomName
      let forbiddenAxiom := axioms.any fun name =>
        name.toString.contains "sorryAx" || isProjectDeclaration env name
      if forbiddenAxiom then continue
      let proofType ← inferType solved.proof
      let moduleName := (moduleFor? env rootTheorem).map (·.toString) |>.getD ""
      let edgeName := "interface-solver:" ++ rootTheorem.toString ++ "=>" ++ spec.key
      reductions := reductions.push <| Json.mkObj [
        ("name", toJson edgeName),
        ("module", toJson moduleName),
        ("type_text", toJson proofType.dbgToString),
        ("premises", toJson (#[] : Array Json)),
        ("conclusions", toJson #[spec.ref]),
        ("relation", toJson "implication"),
        ("status", toJson "live"),
        ("provenance", toJson "interface_solver"),
        ("witness", toJson rootTheorem.toString),
        ("solver_depth", toJson solved.depth),
        ("solver_attempts", toJson solved.attempts),
        ("type_dependencies", namesJson proofType.getUsedConstants),
        ("proof_dependencies", namesJson solved.usedTheorems),
        ("axioms", namesJson axioms),
        ("doc", toJson "Lean Meta constructed and checked this interface witness."),
        ("source", Json.mkObj [
          ("path", toJson (sourcePath moduleName)),
          ("line", toJson (0 : Nat))
        ])
      ]
      solvedCount := solvedCount + 1
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("area", toJson "rh"),
    ("commit", toJson ""),
    ("target", Json.mkObj [
      ("key", toJson "RiemannHypothesis"),
      ("expression", toJson "RiemannHypothesis"),
      ("declaration", toJson "RiemannHypothesis")
    ]),
    ("reductions", toJson reductions),
    ("interface_solver", Json.mkObj [
      ("interfaces_checked", toJson interfaces.size),
      ("interfaces_proven", toJson solvedCount),
      ("max_depth", toJson interfaceSolverMaxDepth),
      ("max_candidates_per_goal", toJson interfaceSolverMaxCandidatesPerGoal),
      ("max_attempts_per_interface", toJson interfaceSolverMaxAttemptsPerInterface),
      ("producer_count", toJson producers.size)
    ])
  ]

syntax (name := exportResearchFrontierCmd)
  "#export_research_frontier" "[" str,* "]" : command

elab_rules : command
  | `(#export_research_frontier [$[$names:str],*]) => do
      let declNames := names.map (·.getString.toName)
      let payload ← liftCoreM <| MetaM.run' <| exportResearchFrontier declNames declNames
      liftIO <| IO.println s!"HGT_FRONTIER_JSON:{payload.compress}"

syntax (name := exportResearchFrontierWithProducersCmd)
  "#export_research_frontier_with_producers"
    "[" str,* "]" "using" "[" str,* "]" : command

elab_rules : command
  | `(#export_research_frontier_with_producers
        [$[$names:str],*] using [$[$producerNames:str],*]) => do
      let declNames := names.map (·.getString.toName)
      let producerDeclNames := producerNames.map (·.getString.toName)
      let payload ← liftCoreM <| MetaM.run' <|
        exportResearchFrontier declNames producerDeclNames
      liftIO <| IO.println s!"HGT_FRONTIER_JSON:{payload.compress}"
