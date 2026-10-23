# Premise discharge by connecting corpus results (250 target)

- **ID:** premise-discharge-250-20261023
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Conditional corpus theorems whose premise (named `Prop` interface or explicit
  hypothesis) is proved elsewhere in the corpus get hypothesis-free forms.

## Counting rule

One discharge = one new hypothesis-free Lean theorem obtained by supplying corpus proofs for every
non-typing premise of an existing conditional theorem, where no hypothesis-free form existed.
Not counted: trivial premises (`(0:ℝ) < 1/2`), theorems that keep any non-typing premise,
restatements of an already-welded conclusion. Each module is compiled with
`lake --old env lean <file>` and wired into its umbrella.

**Discharges: 55 compiled, 197 written awaiting compile (252 written) / 250.**

## Candidate finder (scratch, not in repo)

Declaration census of `formal/GaloisForLFunctions` (binders, conclusion, namespace, `open`s,
section variables); closed premises = hypotheses mentioning no bound variable; closure of
proved closed propositions through premise-free theorems, top-level `↔` and `∧`. Traps found:
outer-paren stripping on `(A) ↔ (B)`, namespace collisions (resolve through namespace chain and
`open`s), instance binders `[FiniteDimensional …]` as premises, `autoImplicit` true in many files
(unknown lowercase identifiers are bound variables). Text identity is exhausted after ~45 welds;
further discharges need statement bridging (unfolding, `↔`, weakening) found by corpus search.

## Ledger

| # | module | premise discharged (provider) | theorems |
|---|--------|-------------------------------|----------|
| 1–16 | `RHTower/RiemannGaussian/GaussianPremiseDischarges` ✓ | `ZetaZeroGaussianOrdinateSummable`, `RiemannXiQuadraticGrowth`, `QuarterLineDigammaGaussDifferenceFormula`, `GaussianDigammaScrewTransform`, `GaussianArithmeticExplicitFormulaIdentified`, `ZetaGaussianZeroDivisorSeparation` | 16 `*_unconditional` / `zetaGaussianCoherentKernelSeparation_proved` |
| 17–23 | `HTGeometry/PaperFourierLLogL/GoodBoundUnconditional` ✓ | `GridBound → UnitTreeBound → AffineTreeBound → RealGoodBound`, `GoodBound` (`gridProof`, `maximal_good_sets`) | 3 interface `_holds`, `ae_tail_majorant`, `ae_convergence_of_bounded`, `median_budget_unconditional`, `circle_bill_unconditional` |
| 24–33 | `RHTower/Zeta23InputDischarges` ✓ | `GammaFacts` (`gammaFacts`) + μ-increment constant (`mu_increment_bound`), `PaperInputs ζ` (`paperInputs_zeta`) | 6 trace-layer lemmas (2 with ∃K), 4 Theorem D variants for every valid `P` |
| 34 | `Bottcher/Brolin/RieszDiracUnconditional` ✓ | `FundamentalSolutionProp` | `isRieszMeasureOfSmooth_dirac_unconditional` |
| 35 | `HTGeometry/PaperStableCoordinate/AllFibersNonrectifiable` ✓ | `¬ IsCoordinate f` (`f_not_coordinate`) | `all_fibers_nonrectifiable` |
| 36 | `RHTower/BakerHomogeneousIndependence` ✓ | `BakerTheorem` (`bakerTheorem_holds`) | `baker_homogeneous_linearIndependent` |
| 37–44 | `RHTower/GuthMaynardCorollariesUnconditional` (pending: QuantumAlg IR missing) | `GuthMaynardLargeValuesBound` | almost-all 2/15, sharp π/ψ at 17/30, scaled/dyadic large values, fixed-σ density, class count |
| 45–52 | `RHTower/XiZeroCopyPremiseDischarges` ✓ | `Infinite/Nonempty XiZeroCopy`, `TwistedArcMinimumPrinciple`, `xiEndpointCompletedCurvature < 1` | 7 + `completedRiemannZeta₀_zero_re_lt_half` |
| 53–54 | `RHTower/ModularLambdaCellEnergyBoundUnconditional` ✓ | `Fintype (SL₂ℤ ⧸ Γ(2))`; then (Λ) + finite `[Γ(2):Γ_N]` | cell energy, windowed coset energy |
| 55–57 | `RHTower/CHMDZeroMeasurePositivityUnconditional` (pending) | `Nonempty zetaZeroConfig.carrier` | KG energy, quartic moment, wave at 0 |
| 58–68 | `RHTower/ThetaCuspSteinCertificates` (pending) | Stein ratio bounds → linear Hankel positivity → `↔` certificates | sixth-moment Hankel, three-temperature, first minor, det, aperture, cubic, discriminant, relaxed fourth (+2 forms), upper adjacent ratio, eighth crossing |
| 69 | `RHTower/SuzukiCutoffSimpleCriticalUniqueness` (pending) | positive simple-critical density (`two_thirds_le_liminf_xiSimpleCriticalRatio`) | `suzukiCutoff_eq_zero_of_simpleCritical_vanish` |
| 70–125 | `RHTower/RiemannGaussian/GaussianXiGrowthConstantDischarges` (pending) | ξ growth laws (quadratic, `3/2`, log-linear) as `∃ A` | 56 uniform-constant estimates |
| 126–130 | `ArithmeticCriticalityTheory/UniformConstantDischarges` ✓ | `exists_riemannKernelReal_le_exp_sixteen` | 5 |
| 131–134 | `HTGeometry/UniformConstantDischarges` ✓ | proved `∃`-bounds | 4 |
| 135–243 | `*/UniformConstantDischarges*` (23 modules, pending) | proved `∃`-bounds (ζ/χ strip bounds, Stirling μ, Γ decay, kernel bounds, smooth-transition derivative bound, …) | 109 |

Uniform-constant discharges: a consumer `(C : ℝ) (hC : P C) … ⊢ Q C` with `∃ C, P C` proved becomes
`∃ C, ∀ …, Q C`, or the constant is eliminated when `Q` does not mention it. Drafted by a generator
from the census (consumer binders + provider `∃`-shape), filtered to constant-like witnesses whose
provider is a bound and whose retained hypotheses only constrain data; each module is compiled.

Excluded after audit: the order-24 sixth-trace chain (its moment bounds use `native_decide`);
headline welds the authors already made (Theorem D headline, GM 30/13, Weyl/Riesz support,
q62 Weyl discharge, PNT-power windows).

## Log
- 2026-10-23 — created; candidate finder built; batches through #36 green; concurrent `lake build`s by other agents delete oleans transiently, so compiles of pending modules wait for them.
