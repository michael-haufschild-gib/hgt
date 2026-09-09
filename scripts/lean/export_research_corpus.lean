import Lean
import Lean.DeclarationRange
import Lean.OriginalConstKind
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
Compiler-derived declaration corpus, independent of any mathematical umbrella.
The driver prepends imports of already compiled modules and appends
`#export_research_corpus ["Module.Name", ...]`. Only declarations owned by those
exact modules are emitted, including private and compiler-generated declarations.

`type_shape` is a JSON-encoded expression tree, not pretty-printed Lean syntax.
Binder names become b0, b1, ... by nesting depth; references use de Bruijn indices.
Universe parameters become u0, u1, ... in declaration parameter order. Constants,
universe structure, binder visibility, applications, quantifiers, literals, and
projections survive unchanged. Only expression metadata and binder names are
discarded; no reduction, sign erasure, or hypothesis filtering is performed.
-/

open Lean Elab Command Meta

set_option maxHeartbeats 8000000

namespace ResearchCorpusExporter

private def binderInfoText : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance_implicit"

private def kindText : ConstantKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .axiom => "axiom"
  | .opaque => "opaque"
  | .quot => "quotient"
  | .induct => "inductive"
  | .ctor => "constructor"
  | .recursor => "recursor"

private def namesJson (names : Array Name) : Json :=
  toJson <| names.qsort Name.quickLt |>.map (·.toString)

private def node (tag : String) (children : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ children)

private def levelShape (params : List Name) : Level → Json
  | .zero => node "zero"
  | .succ level => node "succ" #[levelShape params level]
  | .max left right => node "max" #[levelShape params left, levelShape params right]
  | .imax left right => node "imax" #[levelShape params left, levelShape params right]
  | .param name =>
      -- Preserve unexpected parameters, rather than silently coalescing them.
      let index := params.idxOf name
      node "param" #[toJson (if index < params.length then s!"u{index}" else name.toString)]
  | .mvar id => node "level_mvar" #[toJson id.name.toString]

private def exprShape (params : List Name) (depth : Nat) : Expr → Json
  | .bvar index => node "bvar" #[toJson index]
  | .fvar id => node "fvar" #[toJson id.name.toString]
  | .mvar id => node "mvar" #[toJson id.name.toString]
  | .sort level => node "sort" #[levelShape params level]
  | .const name levels => node "const" #[toJson name.toString, toJson (levels.map (levelShape params))]
  | .app fn arg => node "app" #[exprShape params depth fn, exprShape params depth arg]
  | .lam _ domain body info => node "lambda" #[
      toJson s!"b{depth}", toJson (binderInfoText info),
      exprShape params depth domain, exprShape params (depth + 1) body]
  | .forallE _ domain body info => node "forall" #[
      toJson s!"b{depth}", toJson (binderInfoText info),
      exprShape params depth domain, exprShape params (depth + 1) body]
  | .letE _ type value body nondep => node "let" #[
      toJson s!"b{depth}", toJson nondep, exprShape params depth type,
      exprShape params depth value, exprShape params (depth + 1) body]
  | .lit (.natVal value) => node "nat" #[toJson value]
  | .lit (.strVal value) => node "string" #[toJson value]
  | .mdata _ body => exprShape params depth body
  | .proj name index body => node "proj" #[
      toJson name.toString, toJson index, exprShape params depth body]

private def typeText (expr : Expr) : MetaM String :=
  withOptions (fun options => options
    |>.setBool `pp.fullNames true
    |>.setBool `pp.universes true
    |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.piBinderTypes true
    |>.set `pp.maxSteps (1000000 : Nat)) do
    return (← ppExpr expr).pretty

private partial def binderRows (expr : Expr) : MetaM (Array Json) := do
  match expr with
  | .forallE name domain body info =>
      let row := Json.mkObj [
        ("name", toJson name.toString),
        ("type", toJson (← typeText domain)),
        ("binder_info", toJson (binderInfoText info))]
      withLocalDecl name info domain fun localVar => do
        return #[row] ++ (← binderRows (body.instantiate1 localVar))
  | .mdata _ body => binderRows body
  | _ => return #[]

private def rangeJson (range : DeclarationRange) : Json :=
  -- Lean lines are one-based; columns are zero-based Unicode code points.
  Json.mkObj [
    ("start", Json.mkObj [
      ("line", toJson range.pos.line), ("column", toJson range.pos.column),
      ("column_utf16", toJson range.charUtf16)]),
    ("end", Json.mkObj [
      ("line", toJson range.endPos.line), ("column", toJson range.endPos.column),
      ("column_utf16", toJson range.endCharUtf16)])]

private def sourceJson (path : Json) (name : Name) : MetaM Json := do
  let ranges ← findDeclarationRanges? name
  return Json.mkObj [
    ("path", path),
    ("range", ranges.map (rangeJson ·.range) |>.getD Json.null),
    ("selection_range", ranges.map (rangeJson ·.selectionRange) |>.getD Json.null),
    ("status", toJson (if ranges.isSome then "available" else "unavailable"))]

private def inspectDeclaration (moduleName : Name) (path : Json) (name : Name) : MetaM Json := do
  let env ← getEnv
  let info ← getConstInfo name
  let kernelKind := ConstantKind.ofConstantInfo info
  let kind := (getOriginalConstKind? env name).getD kernelKind
  let value := info.value? (allowOpaque := true)
  let expectsValue := kind == .thm || kind == .defn || kind == .opaque
  let valueStatus :=
    if value.isSome then (if kind == .opaque then "opaque" else "available")
    else if expectsValue then "unavailable" else "not_applicable"
  let proofStatus :=
    if value.isSome then "available"
    else if expectsValue then "unavailable" else "not_applicable"
  let axioms ← collectAxioms name
  -- Hidden theorem/definition bodies can be represented as kernel axioms.
  -- A self-dependency in that case is missing axiom metadata, not a real axiom.
  let axiomsAvailable := !(expectsValue && value.isNone && axioms.contains name)
  return Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson moduleName.toString),
    ("kind", toJson (kindText kind)),
    ("kernel_kind", toJson (kindText kernelKind)),
    ("type_text", toJson (← typeText info.type)),
    ("type_shape", toJson (exprShape info.levelParams 0 info.type).compress),
    ("binders", toJson (← binderRows info.type)),
    ("type_dependencies", namesJson info.type.getUsedConstants),
    -- These are direct constants in the value, including binder annotations.
    -- Definitions have values too; this field does not assert theoremhood.
    ("proof_dependencies", value.map (namesJson ·.getUsedConstants) |>.getD Json.null),
    ("proof_dependencies_status", toJson proofStatus),
    ("value_status", toJson valueStatus),
    ("axioms", if axiomsAvailable then namesJson axioms else Json.null),
    ("axioms_status", toJson (if axiomsAvailable then "available" else "unavailable")),
    ("is_unsafe", toJson info.isUnsafe),
    ("is_partial", toJson info.isPartial),
    ("doc", toJson (← findDocString? env name)),
    ("source", ← sourceJson path name),
    ("compiler_snapshot_status", toJson "compiled_snapshot"),
    ("status", toJson "ok"),
    ("error", Json.null)]

private def modulePath (moduleName : Name) : IO Json := do
  try
    return toJson (← IO.FS.realPath (← findLean (← getSrcSearchPath) moduleName)).toString
  catch _ => return Json.null

private def moduleArtifact (env : Environment) (moduleName : Name) : IO Json := do
  let artifact ← try
      pure <| toJson (← IO.FS.realPath (← findOLean moduleName)).toString
    catch _ => pure Json.null
  let imports : Option (Array String) := do
    let index ← env.header.moduleNames.findIdx? (· == moduleName)
    let data ← env.header.moduleData[index]?
    pure <| data.imports.map (·.module.toString)
  return Json.mkObj [
    ("module", toJson moduleName.toString), ("artifact_path", artifact),
    ("source_path", ← modulePath moduleName), ("direct_imports", toJson imports)]

private def exportModules (modules : Array Name) : MetaM Json := do
  let env ← getEnv
  for moduleName in modules do
    unless env.header.moduleNames.contains moduleName do
      throwError "Requested module is not imported: {moduleName}"
  let mut paths : NameMap Json := {}
  for moduleName in modules do
    paths := paths.insert moduleName (← modulePath moduleName)
  let mut declarations := #[]
  let mut errors : Array String := #[]
  -- const2ModIdx also contains IR-only symbols (e.g. _boxed), which have no
  -- elaborated ConstantInfo. Inventory actual declarations, not linker symbols.
  let names := env.constants.toList.toArray.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    let moduleName ← env.header.moduleNames[index.toNat]?
    if modules.contains moduleName then some (name, moduleName) else none
  for (name, moduleName) in names.qsort (fun a b => Name.quickLt a.1 b.1) do
    try
      declarations := declarations.push (← inspectDeclaration moduleName
        (paths.find? moduleName |>.getD Json.null) name)
    catch exception =>
      let error ← exception.toMessageData.toString
      errors := errors.push s!"{name}: {error}"
      -- Preserve failed declarations, so consumers can never mistake a partial
      -- export for a complete inventory or an inaccessible proof for an empty one.
      declarations := declarations.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("kind", Json.null), ("type_text", Json.null), ("type_shape", Json.null),
        ("binders", Json.null), ("type_dependencies", Json.null),
        ("proof_dependencies", Json.null), ("proof_dependencies_status", toJson "unavailable"),
        ("value_status", toJson "unavailable"), ("axioms", Json.null),
        ("axioms_status", toJson "unavailable"), ("source", Json.null),
        ("status", toJson "error"), ("error", toJson error)]
  return Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("toolchain", toJson s!"leanprover/lean4:v{Lean.versionString}"),
    ("modules", toJson (modules.map (·.toString))),
    ("module_artifacts", toJson (← (modules.mapM (moduleArtifact env) : IO (Array Json)))),
    ("compiler_snapshot_status", toJson "compiled_snapshot"),
    ("type_shape_format", toJson "lean-expr-json-v1"),
    ("declarations", toJson declarations),
    ("status", toJson (if errors.isEmpty then "ok" else "partial")),
    ("error", if errors.isEmpty then Json.null else toJson (String.intercalate "\n" errors.toList))]

syntax (name := exportResearchCorpusCmd)
  "#export_research_corpus" "[" str,* "]" : command

elab_rules : command
  | `(#export_research_corpus [$[$modules:str],*]) => do
      let payload ← liftCoreM <| MetaM.run' <| exportModules (modules.map (·.getString.toName))
      liftIO <| IO.println s!"HGT_CORPUS_JSON:{payload.compress}"

end ResearchCorpusExporter
