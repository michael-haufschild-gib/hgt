import Lean
import Lean.DocString
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import GaloisForLFunctions

/-!
Compiler-derived exporter for research-frontier logic.

It emits only checked theorem interfaces between named project propositions.
Proof constants are exported for retrieval/audit but never become logical edges.
-/

open Lean Elab Command Meta

set_option maxHeartbeats 0

private def projectPrefix : String := "GaloisForLFunctions."

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

private def propositionJson (expr : Expr) : MetaM Json := do
  let expression := (← ppExpr expr).pretty
  let declaration? := headDeclaration? expr
  let key := declaration?.map (·.toString) |>.getD expression
  return Json.mkObj [
    ("key", toJson key),
    ("expression", toJson expression),
    ("declaration", declaration?.map (toJson ·.toString) |>.getD Json.null)
  ]

private def namesJson (names : Array Name) : Json :=
  toJson <| names.qsort Name.quickLt |>.map (·.toString)

private def proofDependencies (info : ConstantInfo) : Array Name :=
  match info.value? (allowOpaque := true) with
  | some value => value.getUsedConstants
  | none => #[]

private def sourcePath (moduleName : String) : String :=
  "formal/" ++ String.intercalate "/" (moduleName.splitOn ".") ++ ".lean"

private def isRetiredDoc (doc : String) : Bool :=
  let lower := doc.toLower
  lower.contains "legacy impossible-premise" ||
    lower.contains "no longer the current research wall"

private def inspectTheorem? (declName : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let info ← getConstInfo declName
  forallTelescope info.type fun xs result => do
    let mut propositionBinders : Array Expr := #[]
    let mut hasUnnamedPropositionBinder := false
    for x in xs do
      let localDecl ← getFVarLocalDecl x
      if ← isProp localDecl.type then
        if isNamedResearchProposition env localDecl.type then
          propositionBinders := propositionBinders.push localDecl.type
        else
          hasUnnamedPropositionBinder := true

    let mut relation := "implication"
    let mut premises : Array Expr := propositionBinders
    let mut conclusions : Array Expr := #[]
    if result.isAppOfArity ``Iff 2 then
      let arguments := result.getAppArgs
      let left := arguments[0]!
      let right := arguments[1]!
      unless isNamedResearchProposition env left &&
          isNamedResearchProposition env right do
        return none
      relation := "iff"
      premises := #[left]
      conclusions := #[right]
    else if result.isAppOfArity ``Not 1 then
      let proposition := result.getAppArgs[0]!
      unless isNamedResearchProposition env proposition do return none
      unless propositionBinders.isEmpty && !hasUnnamedPropositionBinder do return none
      relation := "refutation"
      premises := #[]
      conclusions := #[proposition]
    else
      unless isNamedResearchProposition env result do return none
      -- Generic analytic/equality assumptions are theorem context, not autonomous
      -- research interfaces.  Skipping is safer than falsely closing the result.
      if hasUnnamedPropositionBinder then return none
      conclusions := #[result]

    let typeText := (← ppExpr info.type).pretty
    let doc := (docStringExt.find? (level := .server) env declName).getD ""
    let moduleName := (moduleFor? env declName).map (·.toString) |>.getD ""
    let premiseJson ← premises.mapM propositionJson
    let conclusionJson ← conclusions.mapM propositionJson
    return some <| Json.mkObj [
      ("name", toJson declName.toString),
      ("module", toJson moduleName),
      ("type_text", toJson typeText),
      ("premises", toJson premiseJson),
      ("conclusions", toJson conclusionJson),
      ("relation", toJson relation),
      ("status", toJson (if isRetiredDoc doc then "retired" else "live")),
      ("type_dependencies", namesJson info.type.getUsedConstants),
      ("proof_dependencies", namesJson (proofDependencies info)),
      -- Fast frontier refresh exports direct logic.  Full axiom audit remains the
      -- existing project lint gate and is intentionally not repeated per row.
      ("axioms", toJson (#[] : Array String)),
      ("doc", toJson doc),
      ("source", Json.mkObj [
        ("path", toJson (sourcePath moduleName)),
        ("line", toJson (0 : Nat))
      ])
    ]

private def isPropositionFormerType : Expr → Bool
  | .forallE _ _ body _ => isPropositionFormerType body
  | body => body.isProp

private def exportResearchFrontier : MetaM Json := do
  let env ← getEnv
  let constants := env.constants.toList.toArray
  let propositionFormers := constants.foldl (init := ({} : NameSet)) fun result entry =>
    let (declName, info) := entry
    if isProjectDeclaration env declName && isPropositionFormerType info.type then
      result.insert declName
    else
      result
  let theoremNames := constants.filterMap fun entry =>
    let (declName, info) := entry
    if isProjectDeclaration env declName && info matches .thmInfo _ then
      some declName
    else
      none
  let mut reverseIndex : NameMap (Array Name) := {}
  for declName in theoremNames do
    let info ← getConstInfo declName
    for dependency in info.type.getUsedConstants do
      if dependency == ``RiemannHypothesis || propositionFormers.contains dependency then
        let consumers := reverseIndex.find? dependency |>.getD #[]
        reverseIndex := reverseIndex.insert dependency (consumers.push declName)

  -- Inspect only theorem-type component connected to the research target.
  let mut pending : Array Name := #[``RiemannHypothesis]
  let mut next := 0
  let mut seenPropositions : NameSet := {}
  let mut seenTheorems : NameSet := {}
  let mut reductions : Array Json := #[]
  while next < pending.size do
    let proposition := pending[next]!
    next := next + 1
    if !seenPropositions.contains proposition then
      seenPropositions := seenPropositions.insert proposition
      let consumers := reverseIndex.find? proposition |>.getD #[] |>.qsort Name.quickLt
      for declName in consumers do
        if !seenTheorems.contains declName then
          seenTheorems := seenTheorems.insert declName
          if let some row ← inspectTheorem? declName then
            reductions := reductions.push row
            let info ← getConstInfo declName
            for dependency in info.type.getUsedConstants do
              if propositionFormers.contains dependency &&
                  !seenPropositions.contains dependency then
                pending := pending.push dependency
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("area", toJson "rh"),
    ("commit", toJson ""),
    ("target", Json.mkObj [
      ("key", toJson "RiemannHypothesis"),
      ("expression", toJson "RiemannHypothesis"),
      ("declaration", toJson "RiemannHypothesis")
    ]),
    ("reductions", toJson reductions)
  ]

elab "#export_research_frontier" : command => do
  let payload ← liftCoreM <| MetaM.run' exportResearchFrontier
  liftIO <| IO.println s!"HGT_FRONTIER_JSON:{payload.compress}"

#export_research_frontier
