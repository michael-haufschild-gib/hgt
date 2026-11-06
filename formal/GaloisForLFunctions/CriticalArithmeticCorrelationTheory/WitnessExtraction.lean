import Lean

/-!
# Extracting witnesses from existence proofs

`effectivize T` reads the stored proof of `T : ∀ xs, ∃ x, P xs x` and adds

* `T.witness : ∀ xs, α`, the term that the proof introduces;
* `T.spec : ∀ xs, P xs (T.witness xs)`, checked by the kernel.

The proof is normalized at its head: `let`, beta, matchers, eliminations of `∃` and `∧`, projections of
`∧`, and project theorems, which are unfolded or effectivized in turn. An existence proof stuck in another
form, such as a Mathlib lemma, becomes a *soft leaf* with witness `Classical.choose`. A witness with no soft
leaf is a closed expression in the definitions it names; `effectivize` lists the soft leaves that reach the
witness. A hand-written `T.witness` and `T.spec` takes precedence over extraction, which is how a soft leaf
is replaced by an explicit value. The extraction changes no statement and adds no axiom.
-/

open Lean Meta Elab Command

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WitnessExtraction

/-- Declarations of this project are followed; everything else is a leaf. -/
private def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`GaloisForLFunctions).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => true

mutual

/-- Head normal form of a proof, up to `Exists.intro` and `And.intro`. -/
private partial def hnf (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then
    return ← hnf (b.instantiate1 v)
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .letE _ _ v b _ => hnf (mkAppN (b.instantiate1 v) args)
  | .lam .. => hnf (fn.betaRev args.reverse)
  | .proj ``And i s => andComponent e s i args
  | .const c us =>
    let env ← getEnv
    if (c == ``Exists.intro || c == ``And.intro) && args.size == 4 then return e
    if c == ``id && args.size ≥ 2 then
      return ← hnf (mkAppN args[1]! args[2:].toArray)
    if c == ``letFun && args.size ≥ 4 then
      return ← hnf (mkAppN (mkApp args[3]! args[2]!) args[4:].toArray)
    if c == ``And.left && args.size ≥ 3 then
      return ← andComponent e args[2]! 0 args[3:].toArray
    if c == ``And.right && args.size ≥ 3 then
      return ← andComponent e args[2]! 1 args[3:].toArray
    if c == ``Exists.casesOn && args.size ≥ 5 then
      let (w, h) ← extract args[3]!
      return ← hnf (mkAppN args[4]! (#[w, h] ++ args[5:].toArray))
    if c == ``Exists.rec && args.size ≥ 5 then
      let (w, h) ← extract args[4]!
      return ← hnf (mkAppN args[3]! (#[w, h] ++ args[5:].toArray))
    if c == ``Exists.elim && args.size ≥ 5 then
      let (w, h) ← extract args[3]!
      return ← hnf (mkAppN args[4]! (#[w, h] ++ args[5:].toArray))
    if (c == ``And.casesOn && args.size ≥ 5) || (c == ``And.rec && args.size ≥ 5) then
      let t := if c == ``And.casesOn then args[3]! else args[4]!
      let f := if c == ``And.casesOn then args[4]! else args[3]!
      let l := mkApp3 (mkConst ``And.left) args[0]! args[1]! t
      let r := mkApp3 (mkConst ``And.right) args[0]! args[1]! t
      return ← hnf (mkAppN f (#[l, r] ++ args[5:].toArray))
    if ← isMatcher c then
      let some info := env.find? c | return e
      return ← hnf ((info.instantiateValueLevelParams! us).betaRev args.reverse)
    if isProject env c then
      let some info := env.find? c | return e
      if info.isTheorem then
        if let some (wn, sn, n) ← ensure c then
          if args.size == n then
            let ty ← whnfR (← inferType e)
            if let .app (.app (.const ``Exists [u]) α) p := ty then
              return mkApp4 (mkConst ``Exists.intro [u]) α p
                (mkAppN (mkConst wn us) args) (mkAppN (mkConst sn us) args)
        return ← hnf ((info.instantiateValueLevelParams! us).betaRev args.reverse)
    return e
  | _ => return e

/-- A component of a conjunction, applied to `rest`. -/
private partial def andComponent (e s : Expr) (i : Nat) (rest : Array Expr) : MetaM Expr := do
  let s' ← hnf s
  if s'.isAppOfArity ``And.intro 4 then
    hnf (mkAppN s'.getAppArgs[2 + i]! rest)
  else
    return e

/-- Witness and proof of an existence proof. -/
private partial def extract (e : Expr) : MetaM (Expr × Expr) := do
  let e' ← hnf e
  if e'.isAppOfArity ``Exists.intro 4 then
    return (e'.getAppArgs[2]!, e'.getAppArgs[3]!)
  let ty ← whnfR (← inferType e')
  let .app (.app (.const ``Exists [u]) α) p := ty
    | throwError "not an existence proof: {ty}"
  return (mkApp3 (mkConst ``Classical.choose [u]) α p e',
    mkApp3 (mkConst ``Classical.choose_spec [u]) α p e')

/-- Add `T.witness` and `T.spec`; returns their names and the arity. `none` if `T` does not end in `∃`. -/
private partial def ensure (T : Name) : MetaM (Option (Name × Name × Nat)) := do
  let wn := T ++ `witness
  let sn := T ++ `spec
  let some info := (← getEnv).find? T | return none
  let some value := info.value? (allowOpaque := true) | return none
  let lps := info.levelParams
  forallTelescope info.type fun xs body => do
    let ty ← whnfR body
    let .app (.app (.const ``Exists _) α) p := ty | return none
    if (← getEnv).contains wn then return some (wn, sn, xs.size)
    let (w, h) ← extract (value.beta xs)
    addDecl <| .defnDecl {
      name := wn, levelParams := lps, type := ← mkForallFVars xs α,
      value := ← mkLambdaFVars xs w, hints := .regular 1000, safety := .safe }
    let wApp := mkAppN (mkConst wn (lps.map mkLevelParam)) xs
    addDecl <| .thmDecl {
      name := sn, levelParams := lps, type := ← mkForallFVars xs (p.beta #[wApp]).headBeta,
      value := ← mkLambdaFVars xs h }
    return some (wn, sn, xs.size)

end

/-- Soft leaves and witness constants that reach a witness value. -/
private partial def scan (e : Expr) :
    StateT (NameSet × Array Expr × ExprSet) MetaM Unit := do
  if (← get).2.2.contains e then return
  modify fun (s, a, v) => (s, a, v.insert e)
  match e.consumeMData with
  | .app f a =>
    if e.getAppFn.consumeMData.isConstOf ``Classical.choose then
      modify fun (s, l, v) => (s, l.push e, v)
    else
      scan f
      scan a
  | .const c _ =>
    if (`witness).isSuffixOf c && !(← get).1.contains c then
      modify fun (s, a, v) => (s.insert c, a, v)
      if let some info := (← getEnv).find? c then
        if let some v := info.value? then scan v
  | .lam _ d b _ | .forallE _ d b _ =>
    scan d
    scan b
  | .letE _ t v b _ =>
    scan t
    scan v
    scan b
  | .proj _ _ s => scan s
  | _ => return

/-- `effectivize T` adds `T.witness` and `T.spec`, following the project theorems that `T` eliminates, and
reports the soft leaves of the witness. -/
elab "effectivize " id:ident : command => do
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    let some (wn, _, _) ← ensure T | throwError "{T} does not end in an existence statement"
    let some info := (← getEnv).find? wn | throwError "missing {wn}"
    let some v := info.value? | throwError "missing value of {wn}"
    let (_, s, leaves, _) ← (scan v).run ({}, #[], {})
    let heads := leaves.map fun l => (l.getAppArgs[2]!).getAppFn
    logInfo m!"{wn}: {s.toList.length} witnesses, soft leaves {heads}"

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WitnessExtraction
