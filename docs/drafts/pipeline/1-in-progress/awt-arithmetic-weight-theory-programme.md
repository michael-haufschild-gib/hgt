# Arithmetic weight theory of Spec ℤ (AWT) — programme

- **ID:** awt-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme
- **Source:** docs/reports/review-0911/obstacles-summary.md §2.9
- **Statement:** Develop the field: families of Euler products with monodromy, `ζ` a special fibre, pure generic fibre, specialization of weights; answer Q1–Q3 of §2.9, build its tools.

## Goal
Answer (Q1) which family carries `ζ` with big monodromy; (Q2) the analogue of `H²_c`; (Q3) the topology/direction of weight semicontinuity. Milestones M2–M4.

Lean folder `formal/GaloisForLFunctions/ArithmeticWeightTheory/`, umbrella `ArithmeticWeightTheory.lean`, README there (foundational, rewritten with results).

## Gates
- [x] 0 → 1 in-progress
- [x] contributions 1–6 formalized (clean compiles)
- [ ] contribution 7 (jump locus) — compiling

## Contributions (Lean modules; status)
1. `TheGenericFibreHasUniformWeights` — big monodromy `k!` bound; a.e. uniform tensor moments (M2). **compiled**
2. `TheTrivialFibreIsTheJump` — pole `≫ √p` at `x = 0`; trace-constant sets closed, conull union, miss a nbhd of `0`. **compiled**
3. `EulerDeformationsOfZetaAreIsozeric` — `ζ_x = ζ e^F`; summable perturbations isozeric (analytic order); class Haar-null. **compiled**
4. `TheTensorPowersHaveExactlyTheirWeight` — abscissa of every tensor power `= 1 + 2kb` at attained top; M4 ⇔ RH. **compiled**
5. `ExactMonodromyPricesEveryFibreAtTheTrivialBound` — uncertainty `ν{x₀}#s ≤ 1`; positivity transfer ≥ trivial bound. **compiled**
6. `TheBaireGenericFibreCarriesThePole` — trace-constant sets nowhere dense; no-constant fibres residual & null. **compiled**
7. `TheJumpLocusIsThePretentiousArchimedeanLine` — pole at `1+iτ` ⇔ `Σ_p (1−Re χ_x(p)p^{−iτ})/p < ∞`; archimedean line in locus; locus Haar-null. **compiling**

## Answers recorded in README §6
Q1 none in Deligne's sense (gauge: generic only; any exact family: trivial bound; vertical: AKT; Dirichlet: AGT; Euler deformations: isozeric). Q2 for `M` all of `M^{⊗2k}` (exact weight), for gauge family pairings. Q3 product topology: constants specialize, exponents not (residual vs null); strip: Hurwitz, `ζ` ⇔ RH; direction over ℤ coherent.

## Open (README §8)
Middle extension at `0`; non-geometrically-constant motives; `X^k` (surface, Hodge index); finite top layer; coinvariants not from orthogonality.

## Log
- 2026-11-09 — created; README draft; contributions 1–6 compiled; README rewritten with results; contribution 7 written.
