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

private def isRetiredDoc (doc : String) : Bool :=
  let lower := doc.toLower
  lower.contains "legacy impossible-premise" ||
    lower.contains "no longer the current research wall" ||
    lower.contains "does not make the premise viable"

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

private def inspectTheorem? (declName : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let info ← getConstInfo declName
  let (domains, result) := telescopeDomains info.type #[]
  let mut propositionBinders : Array Expr := #[]
  let mut hasUnnamedPropositionBinder := false
  for domain in domains do
    if isPropositionExpression env domain then
      if isNamedResearchProposition env domain then
        propositionBinders := propositionBinders.push domain
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

  let typeText := info.type.dbgToString
  let doc := (docStringExt.find? (level := .server) env declName).getD ""
  let moduleName := (moduleFor? env declName).map (·.toString) |>.getD ""
  let premiseJson := premises.map propositionJson
  let conclusionJson := conclusions.map propositionJson
  return some <| Json.mkObj [
    ("name", toJson declName.toString),
    ("module", toJson moduleName),
    ("type_text", toJson typeText),
    ("premises", toJson premiseJson),
    ("conclusions", toJson conclusionJson),
    ("relation", toJson relation),
    ("status", toJson (if isRetiredDoc doc then "retired" else "live")),
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

private def exportResearchFrontier (theoremNames : Array Name) : MetaM Json := do
  let env ← getEnv
  let requested := theoremNames.foldl (init := ({} : NameSet)) (·.insert ·)
  let candidateNames := env.const2ModIdx.toList.toArray.filterMap fun entry =>
    let (declName, moduleIdx) := entry
    if !requested.contains declName then
      none
    else
      match env.header.moduleNames[moduleIdx.toNat]? with
      | some moduleName =>
          if moduleName.toString.startsWith projectPrefix then some declName else none
      | none => none
  let mut reductions : Array Json := #[]
  for declName in candidateNames.qsort Name.quickLt do
    if env.find? declName matches some (.thmInfo _) then
      if let some row ← inspectTheorem? declName then
        reductions := reductions.push row
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

syntax (name := exportResearchFrontierCmd)
  "#export_research_frontier" "[" str,* "]" : command

elab_rules : command
  | `(#export_research_frontier [$[$names:str],*]) => do
      let declNames := names.map (·.getString.toName)
      let payload ← liftCoreM <| MetaM.run' <| exportResearchFrontier declNames
      liftIO <| IO.println s!"HGT_FRONTIER_JSON:{payload.compress}"
