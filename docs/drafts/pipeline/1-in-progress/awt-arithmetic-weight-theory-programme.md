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
- [x] contributions 1–16 formalized (clean compiles, wired into umbrella; umbrella wired into MainTheorems)

## Contributions (Lean modules; status)
1. `TheGenericFibreHasUniformWeights` — big monodromy `k!` bound; a.e. uniform tensor moments (M2). **compiled**
2. `TheTrivialFibreIsTheJump` — pole `≫ √p` at `x = 0`; trace-constant sets closed, conull union, miss a nbhd of `0`. **compiled**
3. `EulerDeformationsOfZetaAreIsozeric` — `ζ_x = ζ e^F`; summable perturbations isozeric (analytic order); class Haar-null. **compiled**
4. `TheTensorPowersHaveExactlyTheirWeight` — abscissa of every tensor power `= 1 + 2kb` at attained top; M4 ⇔ RH. **compiled**
5. `ExactMonodromyPricesEveryFibreAtTheTrivialBound` — uncertainty `ν{x₀}#s ≤ 1`; positivity transfer ≥ trivial bound. **compiled**
6. `TheBaireGenericFibreCarriesThePole` — trace-constant sets nowhere dense; no-constant fibres residual & null. **compiled**
7. `TheJumpLocusIsThePretentiousArchimedeanLine` — pole at `1+iτ` ⇔ `Σ_p (1−Re χ_x(p)p^{−iτ})/p < ∞`; archimedean line in locus; locus Haar-null; poles simple uniformly. **compiled**
8. `TheEdgeDivisorOfAFibre` — edge zero ⇔ anti-pretentious; zeros simple uniformly; never pole and zero; Liouville zero at 1; edge-zero locus Haar-null. **compiled**
9. `TheEdgeDivisorOfZeta` — `ζ(1+iτ) ≠ 0 ⇔ Σ_p (1+cos(τ log p))/p = ∞`; ζ's edge divisor = one simple pole at 1. **compiled**
10. `TheArchimedeanLineHasTheGenericMoments` — vertical windowed 2k-moment of ζ = generic (gauge) moment below the square-root threshold; ≥ generic at every length (nonneg windows). **compiled**
11. `TheGenericFrobeniusIsGaussian` — `k!(V−kM)^k ≤ E|T|^{2k} ≤ k!V^k`; moment ratio → k! (Sato–Tate law of the gauge family). **compiled**
12. `TheVerticalFrobeniusIsEquidistributed` — prime restriction measure preserving; ζ's vertical window traces have the generic law at every fixed degree (Kronecker–Weyl). **compiled**
13. `TheKunnethFormulaForTheTensorPowers` — `Σ_n Λ(n) t(log n)^m n^{−s} = Σ_{z⃗} Π e_{z_i}·(−ζ′/ζ)(s − Σz_i)` for `Re s > 1 + mb` (geometric constancy as a theorem). **compiled**
14. `AmplifiedMonodromyBreaksOnlyOffTheTrivialFibre` — coherent amplified pricing at `0` vs strict amplified saving `2 < 4` off `0` under exact orthonormality on `{4, 6, 9}`; centred jump cancellation. **compiled**
15. `ProductPositivityCouplingIsOneWay` — Abel–divisor monotonicity under symmetric shifts; simple-pole Euler-factor doubling on `flipPrimes θ` preserves product positivity while shifting `primeWindowOf` by `≫ p^{θ − ½}` (`no_reverse_weight_bound_from_product_positivity`). **compiled**
16. `TheZeroMotiveIsTheFixedPartOfEveryArithmeticFamily` — `(FP)` across all five canonical family classes and mixtures; pushforward realizability; weighted AM–GM tangent coercivity; cover-family sublinear tensor moments ⇔ RH (`zeroMotive_is_fixedPart_of_every_arithmeticFamily`). **compiled**

## No-go closure (family + positivity route to the sixth move)
- **Exact killing theorems:** geometric constancy (`summable_tensorTerm_iff_of_max`, M4 ⇔ RH); pricing (`measureReal_singleton_mul_pow_le`); constants blow up at `ζ` (`trivial_fibre_is_the_jump`); exponents residual vs null (`residual_and_null_of_traceExponent`); isozeric class null (`gaugeHaar_isozericClass_eq_zero`).
- **Strongest positive survivors:** generic uniform weights (M2, `ae_fibreMoment_le`); edge divisor classification by (anti-)pretentious distance with uniform order-one bounds from the Euler product (`pole_iff_pretentious`, `edgeZero_iff_antiPretentious`).
- **New insight:** the sixth move needs coinvariants computed by an identity whose non-invariant part is pole-free (cohomology over `𝔽_q`), not by orthogonality; the gauge family is the Mellin family with jump locus = pretentious archimedean line.
- **Status:** all survivors formalized in Lean (folder above).

## Answers recorded in README §6
Q1 none in Deligne's sense (gauge: generic only; any exact family: trivial bound; vertical: AKT; Dirichlet: AGT; Euler deformations: isozeric). Q2 for `M` all of `M^{⊗2k}` (exact weight), for gauge family pairings. Q3 product topology: constants specialize, exponents not (residual vs null); strip: Hurwitz, `ζ` ⇔ RH; direction over ℤ coherent.

## Open (README §8)
Middle extension at `0`; non-geometrically-constant motives; `X^k` (surface, Hodge index); finite top layer; coinvariants not from orthogonality.

## Log
- 2026-11-09 — created; contributions 1–13 compiled; README rewritten with results, answers, tools and residual open topics.
