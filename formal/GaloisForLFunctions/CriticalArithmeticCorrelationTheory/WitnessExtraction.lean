import Lean

/-!
# Extracting witnesses from existence proofs

`effectivize T` reads the stored proof of a theorem `T : ∀ xs, ∃ x, P xs x` and adds

* `T.witness : ∀ xs, α`, the term that the proof introduces;
* `T.spec : ∀ xs, P xs (T.witness xs)`, checked by the kernel.

The traversal follows `Exists.intro`, eliminations of `∃` and `∧`, `let`, `have`, `id` and matchers. An
elimination of another project theorem recurses into that theorem. Any other existence proof is a *soft
leaf*: its witness is `Classical.choose`, and the command reports it. A witness with no soft leaves is a
closed expression in the definitions it names. The extraction changes no statement and adds no axiom.
-/

open Lean Meta Elab Command

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WitnessExtraction

/-- Theorems of the project are followed; everything else is a leaf. -/
private def isProjectName (n : Name) : Bool :=
  let root := match n with
    | .str (.num (.str _ "_private") _) _ => n
    | _ => n
  let s := root.toString
  "GaloisForLFunctions".isPrefixOf s || "RHTower".isPrefixOf s || "Zeta23".isPrefixOf s ||
    (s.splitOn "GaloisForLFunctions").length > 1

mutual

/-- Witness and proof of an existence proof `e : ∃ x, P x`. -/
private partial def extract (e : Expr) : MetaM (Expr × Expr) := do
  let e := e.consumeMData.headBeta
  match e with
  | .letE _ _ v b _ => extract (b.instantiate1 v)
  | _ =>
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isLambda || fn.isLet then
    return ← extract (fn.betaRev args.reverse).headBeta
  if let .const c us := fn then
    if c == ``Exists.intro && args.size == 4 then
      return (args[2]!, args[3]!)
    if c == ``id && args.size ≥ 2 then
      return ← extract (mkAppN args[1]! args[2:].toArray).headBeta
    if c == ``letFun && args.size ≥ 4 then
      return ← extract (mkAppN (mkApp args[3]! args[2]!) args[4:].toArray).headBeta
    if c == ``Exists.casesOn && args.size ≥ 5 then
      let (w, h) ← extract args[3]!
      return ← extract (mkAppN (mkApp2 args[4]! w h) args[5:].toArray).headBeta
    if c == ``Exists.rec && args.size ≥ 5 then
      let (w, h) ← extract args[4]!
      return ← extract (mkAppN (mkApp2 args[3]! w h) args[5:].toArray).headBeta
    if c == ``And.casesOn && args.size ≥ 5 then
      let t := args[3]!
      let l := mkApp3 (mkConst ``And.left) args[0]! args[1]! t
      let r := mkApp3 (mkConst ``And.right) args[0]! args[1]! t
      return ← extract (mkAppN (mkApp2 args[4]! l r) args[5:].toArray).headBeta
    if c == ``And.rec && args.size ≥ 5 then
      let t := args[4]!
      let l := mkApp3 (mkConst ``And.left) args[0]! args[1]! t
      let r := mkApp3 (mkConst ``And.right) args[0]! args[1]! t
      return ← extract (mkAppN (mkApp2 args[3]! l r) args[5:].toArray).headBeta
    if ← isMatcher c then
      let some info := (← getEnv).find? c | return ← softLeaf e
      let v := info.instantiateValueLevelParams! us
      return ← extract (v.betaRev args.reverse).headBeta
    if isProjectName c then
      let some info := (← getEnv).find? c | return ← softLeaf e
      if info.isTheorem then
        let some (wn, sn) ← ensure c | return ← softLeaf e
        return (mkAppN (mkConst wn us) args, mkAppN (mkConst sn us) args)
  softLeaf e

/-- An existence proof with no visible witness. -/
private partial def softLeaf (e : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnfR (← inferType e)
  let .app (.app (.const ``Exists [u]) α) p := ty
    | throwError "not an existence proof: {ty}"
  logInfo m!"soft leaf: {e.getAppFn}"
  return (mkApp3 (mkConst ``Classical.choose [u]) α p e,
    mkApp3 (mkConst ``Classical.choose_spec [u]) α p e)

/-- Add `T.witness` and `T.spec`, returning their names. Theorems not ending in `∃` return `none`. -/
private partial def ensure (T : Name) : MetaM (Option (Name × Name)) := do
  let wn := T ++ `witness
  let sn := T ++ `spec
  if (← getEnv).contains wn then return some (wn, sn)
  let some info := (← getEnv).find? T | return none
  let some value := info.value? (allowOpaque := true) | return none
  let lps := info.levelParams
  forallTelescope info.type fun xs body => do
    let ty ← whnfR body
    let .app (.app (.const ``Exists [u]) α) p := ty | return none
    let proof := (value.beta xs).headBeta
    let (w, h) ← extract proof
    let wType ← mkForallFVars xs α
    let wVal ← mkLambdaFVars xs w
    addDecl <| .defnDecl {
      name := wn, levelParams := lps, type := wType, value := wVal,
      hints := .regular 1000, safety := .safe }
    setReducibilityStatus wn .semireducible
    let wApp := mkAppN (mkConst wn (lps.map mkLevelParam)) xs
    let sType ← mkForallFVars xs (p.beta #[wApp]).headBeta
    let sVal ← mkLambdaFVars xs h
    addDecl <| .thmDecl { name := sn, levelParams := lps, type := sType, value := sVal }
    let _ := u
    return some (wn, sn)

end

/-- `effectivize T` adds `T.witness` and `T.spec`, following the project theorems that `T` eliminates. -/
elab "effectivize " id:ident : command => do
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    match ← ensure T with
    | some (wn, _) => logInfo m!"witness: {wn}"
    | none => throwError "{T} does not end in an existence statement"

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WitnessExtraction
