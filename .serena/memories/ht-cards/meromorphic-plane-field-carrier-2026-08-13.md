# The meromorphic plane field carrier (NEW, built 2026-08-13)

A genuine `Field` of meromorphic functions on ℂ, which the corpus previously lacked
(`meroField univ` = fractions of ENTIRE germs does not visibly contain `℘`).

## Modules (all axiom-clean, wired into `GaloisForLFunctions.HTGeometry`)
- `HTGeometry/MeromorphicPlaneField.lean`
  `planeCodiscrete = Filter.codiscreteWithin univ`; `mem_planeCodiscrete` (S ∈ it ↔ ∀x, S ∈ 𝓝[≠]x);
  `eventuallyEq_planeCodiscrete_iff`; `isOpen_of_mem_planeCodiscrete`;
  `meromorphicPlaneSubring : Subring (Germ planeCodiscrete ℂ)`; `exists_inv_of_ne_zero`;
  `MeromorphicPlane` (def) + `CommRing` + `isField_meromorphicPlane` + `Field`;
  `MeromorphicPlane.germ`, `germ_injective`, `ofMeromorphic`, `ofMeromorphic_eq_iff`,
  `MeromorphicPlane.exists_rep`, `germ_add/mul/zero/one`, `ofMeromorphic_add/mul`,
  `weierstrassPElement`, `derivWeierstrassPElement`
- `HTGeometry/MeromorphicPlaneDifferential.lean`
  `planeGermDeriv`, `meromorphicPlaneDeriv`, `meromorphicPlaneDerivation`,
  `instance : Differential MeromorphicPlane`
- `HTGeometry/MeromorphicPlaneTranslation.lean`
  `tendsto_add_const_planeCodiscrete`, `planeTranslate`, `planeTranslateEquiv (c) : ≃+*`,
  `planeTranslate_deriv` (translation commutes with d/dz)
- `HTGeometry/MeromorphicPlaneAlgebra.lean`
  `constPlane : ℂ →+* MeromorphicPlane`, `Algebra ℂ MeromorphicPlane`,
  `meromorphicAt_polyEval`, `aeval_ofMeromorphic`
- `HTGeometry/EllipticPlaneSubfield.lean`
  `periodic_toMeromorphicNFOn_of_eventuallyEq` (germ periodicity ⟹ pointwise periodicity of the NF),
  `ellipticSubfield L : IntermediateField ℂ MeromorphicPlane`,
  `eval_weierstrassP_ne_zero` (℘ transcendental over ℂ; unbounded near 0 vs finite root set),
  `aeval_mem_intermediateField`,
  **`ellipticSubfield_eq_adjoin : ellipticSubfield L = ℂ⟮℘[L], ℘'[L]⟯`**

## Key design facts
- Germ equality along `planeCodiscrete` IS "∀ x, f =ᶠ[𝓝[≠]x] g", the exact form in which the
  elliptic generation theorem is stated — the two fit together with no glue.
- A codiscrete set of ℂ is OPEN (complement closed+discrete): that is why `deriv` descends.
- `Bornology.IsBounded.compl`, `Polynomial.mem_roots'`, `map_inv₀`, `MeromorphicAt.fun_add/fun_mul`,
  `MeromorphicNFAt.comp_analyticAt` are the mathlib names used.
- `IntermediateField` has no `neg_mem'` field; it needs carrier/one/zero/add/mul/inv/algebraMap.

## NEXT (planned)
1. Elliptic isogeny protocol on `MeromorphicPlane`: `planeScale m` (f ↦ f(m·)),
   `PeriodPair` scaling, image of `ellipticSubfield L` under `planeScale m` = elliptic subfield of
   the scaled lattice — the depthwise deck identity, unconditional.
   Faithfulness of the deck group: a period of `℘[L]` lies in `L.lattice` (poles are exactly Λ).
   Degree via Artin (`FixedPoints.finrank_eq_card`).
2. **Jet / generic-reparametrization extension** of a differential field K:
   `T = K(u₀,u₁,…)`, `D|_K = δ(·)·u₀`, `D(u_i) = u_{i+1}`. This makes `(℘,℘')` a
   DIFFERENTIAL-GENERIC point of the elliptic curve and lets `planeTranslate` extend to T fixing
   the `u_i` — so the elliptic deck action needs NO ℘ addition theorem.
   This is the remaining infrastructure for card 4's abelian-variety column and card 6's
   compact-signature protocol presentation.
