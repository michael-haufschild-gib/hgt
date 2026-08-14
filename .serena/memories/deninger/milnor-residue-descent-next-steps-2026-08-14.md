# Milnor residue: state after Steinberg, and the exact descent obstruction (two attempts recorded)

Date: 2026-08-14. Read this before touching the residue descent again — two designs have already
been tried and reverted.

## Done and green (axioms `propext, Classical.choice, Quot.sound`)

- `MilnorKResidueData.lean` — `ResidueData` (TameData + uniformizer + `oneSub_res`), `unitPart`,
  `residueUnit` and laws.
- `MilnorKResidueStep.lean` — `resSymbol`(+`_one`,`_mul`,`_neg`,`_neg_one_add_self`), `mulSymbol`,
  `mulSymbol_mul`, **`resStepHom`**, **`resStepHom_mul`** (multilinearity of the step), `resPair`,
  **`resFold`**.
- `MilnorKResidueSteinberg.lean` — operator identities, `resStepHom_eq_zero`, the val-zero apply
  lemmas, `residueUnit_eq_neg_of_neg`, **`resStepHom_steinberg`** (all four valuation cases),
  **`resFold_eq_zero_of_steinberg`**.
- `MilnorKGradedRingAssoc.lean` — `milnorDegCongr`, `milnorMul_assoc`, `milnorOne`, unit laws.

## The descent obstruction, and TWO designs that do NOT work

`resFold D l n : (K_n × K_{n-1}) →+ (K_{n + l.length} × K_{n + l.length - 1})`.

**Attempt 1 — state multilinearity on `resFold` directly.** Fails to *typecheck*: with `l₁` a
variable, `(l₁ ++ x :: l₂).length` is stuck, so the three folds have three different (propositionally
equal) target types and `+` cannot be formed.

**Attempt 2 — pass the length as a parameter and match the proof against `rfl`:**
```
noncomputable def resFoldOf : (l : List Kˣ) → (m : ℕ) → l.length = m → (n : ℕ) → …
  | [], _, rfl, _ => AddMonoidHom.id _
  | a :: l, _, rfl, n => (resStepHom D a (n + l.length)).comp (resFoldOf l l.length rfl n)
```
This typechecks, and the **nil** case of the multilinearity induction goes through
(`resStepHom_mul` + `AddMonoidHom.add_comp`). The **cons** case does not: after `subst ha` the two
remaining proofs have type `(l₁ ++ (a*b)::l₂).length = (l₁ ++ a::l₂).length`, whose sides are stuck
on `l₁`. Lean 4's definitional proof irrelevance only makes a proof reduce to `rfl` when its type is
literally `X = X`, so the `rfl` pattern never fires and `resFoldOf` will not unfold. Writing a
`show` with each term at its own length re-introduces the Attempt-1 type mismatch.

**Design to try next (untested).** Define the fold as an explicit transport rather than by
proof-matching:
```
noncomputable def resFoldTo (l : List Kˣ) (m : ℕ) (h : l.length = m) (n : ℕ) :
    (K_n × K_{n-1}) →+ (K_{n+m} × K_{n+m-1}) :=
  (milnorPairDegCongr (by rw [h])).comp (resFold D l n)
```
with `milnorPairDegCongr : i = j → (K_i × K_{i-1}) →+ (K_j × K_{j-1})` built from `milnorDegCongr`,
then push the transports through the induction. Keep the `n + m` argument order throughout:
`n + (k+1)` reduces definitionally to `(n+k)+1`, `(k+1) + n` does not.

## Then

- `resSymbolPair`, `resPre := FreeAbelianGroup.lift`,
  `milnorRelSubgroupDeg K n ≤ (resPre D n).ker` (generator families as in `milnorKDegPreMap_rel`),
  `∂ := QuotientAddGroup.lift` with `∂{π,u₂,…} = {ū₂,…}` and `∂{u₁,…} = 0`;
- a `ResidueData` constructor from a `Valuation` (extend `tameDataOfValuation`; the new `oneSub_res`
  field needs reduction mod the maximal ideal to be a ring hom);
- the Gersten complex `K_n^M(K) → ⊕_v K_{n-1}^M(κ(v))`.

## Standing card-level blockers (unchanged, and NOT reachable by this work)

- Card 2 main claim: `K_2(𝒪_K)` torsion for a number field = Garland 1971 / Quillen + Borel.
  Note the card itself does not prove `(1)`; its proof paragraph cites Gallauer Rem. 6.8 → Borel.
- Card 3: the `∞`-categorical layer (free `E_∞`-algebras, homotopy pushouts, connective
  `t`-structures), absent from mathlib.
