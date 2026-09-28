# Möbius reconstruction of the all-sieve theta rate cone — Lean certificate

- **Paper card:** `theta-all-sieve-mobius-rate-reconstruction.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.RateMobiusInversion` (prime transport `A_n`,
  deletion parts, Euler sums, the window condition, the measure classification, rate gap, negative
  moments), `GaloisForLFunctions.RHTower.ThetaRateLaplaceBernstein` (Laplace uniqueness and order
  for rate measures, unbounded Bernstein–Widder, Laplace transforms of dilations and deletions,
  deleted fluxes, no residual at rate zero), `GaloisForLFunctions.RHTower.ThetaRateMobiusSourceTransfer`
  (Gaussian tails of `k`, rate seed ↔ translation measure, Tonelli flux law, dominated mixture,
  representation (7), uniqueness, gap support, charge rigidity, the theta rate measure),
  `GaloisForLFunctions.RHTower.ThetaRateMobiusBoundaryExamples` (gapped Laplace convergence, the
  `3/2` summability boundary, finite smooth stages, `dλ`, the critical ghost); corpus
  `exists_finiteLaplaceMeasure_of_completelyMonotoneOn`, `measure_eq_of_laplace_eq`,
  `le_of_completelyMonotoneOn_laplace_sub` (finite Bernstein–Widder/Laplace), `thetaNormalizedFlux`,
  `thetaNormalizedFlux_comp_add`, `thetaNormalizedFlux_thetaCuspFullSource`,
  `eq_of_thetaNormalizedFlux_eq`, `hasDerivAt_exp_mul_thetaNormalizedFlux` (flux law and recovery),
  `thetaMeasureGauge`, `measure_eq_dirac_of_cosh_half`, `integral_cosh_half_eq`,
  `exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian`, `thetaCuspFullSource_neg`,
  `thetaCuspFullSource_pos_all`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build` of every module; `lake env lean` audit clean on all four
  modules; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 190 theorems of
  these modules; no `sorry`. The only hypotheses are the card's own quantified objects (the rate
  measure and its gap or moment, the source `f` with its complete-monotonicity tests, the mass and
  charge equalities).

Dictionary: `A_n ν = rateDilate n ν`; the positive and negative parts of `D_S ν = ∏_{p∈S}(I - A_p)ν`
are `rateDeletionPart (· ∈ S) true ν` and `rateDeletionPart (· ∈ S) false ν` (sums of `A_{∏T}ν`
over sets `T ⊆ S` of primes of even and odd size), so "`D_S ν` is positive" is
`rateDeletionPart (· ∈ S) false ν ≤ rateDeletionPart (· ∈ S) true ν`;
`Σ_{n≥1} A_n ξ = rateEuler ξ`, `Σ_{m P-free} A_m ξ = rateEulerPart P ξ`;
`M_q(ν) = rateNegMoment q ν`; `∫ e^{-tλ} dν = rateLaplace ν t`;
local finiteness of the Euler/Möbius sums is `RateWindowFinite ν` (`Σ_{m,n} A_{mn}ν(-∞, R] < ∞`);
`b_f = thetaNormalizedFlux f`, "continuous source with finite normalized tail flux" is
`ThetaFluxSource f`; `D_S f = thetaPrimeDeletion S f`; `k = thetaCuspFullSource`;
`∫ k(x+s) dη(s) = thetaMeasureGauge η thetaCuspFullSource x`; `η_ξ = thetaRateTranslation ξ`,
the rate seed of `η` is `thetaRateSeed η`; "the Bernstein measure of `b_f`" is
`IsThetaFluxRateMeasure f ν`; "rate gap or finite `M_q`, `q > 3/2`" is `RateControlled ν`;
`ν_k = thetaRateMeasure`, `ν_P = thetaSmoothStage P`, `dλ = lebesgueRate`,
`λ^{1/2} dλ = criticalGhostRate`.

| Card item | Lean theorem |
|-|-|
| `A_m A_n = A_{mn}`, prime dilations commute | `rateDilate_rateDilate`, `rateEuler_rateDeletionPart` |
| classification: under local finiteness, `D_S ν ≥ 0` for every finite prime set `S` ⇔ `ν = Σ A_n ξ` for a unique positive `ξ` | `rateMobius_classification`, `rateMobius_exists`, `rateMobius_unique` |
| rate gap + finite Laplace transform ⇒ locally finite | `rateWindowFinite_of_gap`, `measure_Iic_ne_top_of_laplace`, `rateDilate_Iic` |
| the seed is supported in `[λ₀, ∞)`; `ξ ≤ ν` | `rateMobius_seed_Iio_of_gap`, `le_rateEuler` |
| (3) `(D_S ν)|_{[λ₀,R]} = ξ|_{[λ₀,R]}` once `S` contains every `p` with `p²λ₀ ≤ R` (also for larger `S`) | `rateDeletion_eq_seed_of_gap` |
| positivity along one increasing cofinal exhaustion suffices | `rateDeletionPart_prime_le_of_exhaustion`, `rateDeletionPart_prime_le_of_cofinal` |
| (4)/(5) cofinal Möbius inverse and Dirichlet convolution | `rateMobius_seed`, `rateMobius_exists`, `tsum_tsum_mul_eq`, `card_even_words_eq` |
| (6) `D_S Σ A_n ξ = Σ_{(n,∏S)=1} A_n ξ ≥ 0` | `rateDeletionPart_rateEuler`, `rateDeletionPart_false_le_rateEuler`, `rateDeletionPart_rateEuler_apply` |
| Laplace integrals of (2) converge in the gapped class | `rateLaplace_rateEuler_ne_top_of_gap`, `rateLaplace_rateEuler` |
| (W1) ⇒ equivalence and uniqueness without a gap | `rateWindowFinite_of_negMoment`, `rateMobius_classification` |
| (W2) `(A_n ν)(E) ≤ b^q M_q(ν) n^{2-2q}` | `rateDilate_le_negMoment`, `measure_Ioc_le_rateNegMoment` |
| finite deletions converge to `ξ` on every set of finite mass | `rateDeletion_tendsto_seed`, `tendsto_rateEulerPart_of_exhaustion` |
| (W3) `M_q(Σ A_n ξ) = (Σ n^{2-2q}) M_q(ξ)` | `rateNegMoment_rateEuler` |
| finite `M_q` bounds every Laplace transform (`e^{-tλ} ≤ C_{t,q} λ^{-q}`) | `lintegral_exp_le_rateNegMoment`, `rpow_mul_exp_neg_le_sharp` |
| `3/2` is the exact summability boundary of the weights `n²` | `summable_eulerWeight_iff` |
| theta rate measure: `ν_k = 2π Σ n² δ_{πn²}` is the Bernstein measure of `b_k`; gap `π`; `M_q(ν_k) = 2π π^{-q} Σ n^{2-2q} < ∞` for `q > 3/2` | `isThetaFluxRateMeasure_thetaCuspFullSource`, `thetaRateSeed_dirac_zero`, `thetaRateMeasure_Iio_pi`, `rateNegMoment_thetaRateMeasure`, `rateControlled_thetaRateMeasure` |
| Bernstein–Widder for `b_f` (no finiteness at `t = 0`) and Laplace uniqueness/order | `exists_rateMeasure_of_completelyMonotoneOn`, `eq_of_rateLaplace_eq`, `le_of_completelyMonotoneOn_rateLaplace_sub` |
| no residual at rate zero: `ν(-∞, 0] = 0` | `rateMeasure_Iic_zero_of_flux`, `tendsto_thetaNormalizedFlux_atTop` |
| deleted fluxes `b_{D_S f}(t) = Σ_{T⊆S} (-1)^{|T|} (∏T)² b_f((∏T)² t)` | `thetaNormalizedFlux_thetaPrimeDeletion_general`, `rateLaplace_rateDeletionPart`, `rateLaplace_rateDilate` |
| complete-monotonicity tests turn into (1) | `rateDeletionPart_le_of_completelyMonotoneOn`, `thetaNormalizedFlux_thetaPrimeDeletion_eq_rateLaplace_sub` |
| (7) `f(x) = ∫ k(x+s) dη(s)` with `η` the push-forward of `(2π e^{5s/2})⁻¹ dξ(λ)` under `λ = π e^{2s}`; `η` unique | `thetaRate_mobius_source_representation`, `existsUnique_thetaTranslationMeasure`, `eq_thetaRateTranslation_of_thetaMeasureGauge`, `thetaRateTranslation_eq_map` |
| `η` supported above `log(λ₀/π)/2` in the gapped case | `thetaTranslationMeasure_Iio_eq_zero_of_gap`, `thetaRateTranslation_Iio_eq_zero` |
| the mixture is pointwise finite and continuous (right Gaussian tail; left tail from evenness) | `thetaRateTranslation_mixture`, `exists_thetaCuspFullSource_le_halfGaussian`, `thetaRateWeight_mul_le_right`, `thetaRateWeight_mul_le_left`, `integrable_thetaRateBound` |
| Tonelli gives the flux of the mixture; `b_k(t) = 2π Σ n² e^{-πn²t}` and the shift law turn (2) into it | `lintegral_Ioi_thetaMixture`, `lintegral_Ioi_thetaMeasureGauge`, `thetaFluxSource_thetaRateTranslation`, `isThetaFluxRateMeasure_thetaMeasureGauge` |
| (8) `f(x) = -e^{-x/2} d/dx[e^{3x} b_f(e^{2x})]`; the flux determines a continuous source | `hasDerivAt_exp_mul_thetaNormalizedFlux`, `eq_of_thetaNormalizedFlux_eq` |
| charge rigidity: same mass and both reflected half-charges ⇒ `η = δ₀`, `f = k` | `thetaMeasureGauge_charge_rigidity`, `eq_thetaCuspFullSource_of_charges`, `lintegral_exp_mul_thetaMeasureGauge`, `lintegral_exp_neg_eq_one_of_charge` |
| evenness plus the positive half-charge supplies the reflected charge | `eq_thetaCuspFullSource_of_even_charges`, `integral_exp_neg_half_mul_of_even` |
| smooth stage `ν_P`: rate gap, survives deletion by primes in `P` | `thetaSmoothStage_Iio_pi`, `thetaSmoothStage_deletion_le`, `rateDeletionPart_rateEulerPart` |
| `q ∉ P`: `D_q ν_P` has coefficient `-2π q²` at rate `π q²`; no finite stage is in the all-sieve cone; the full completion is `ν_k` | `thetaSmoothStage_undeclared_prime`, `thetaSmoothStage_not_deletion_le`, `thetaSmoothStage_finite_not_allSieve`, `thetaSmoothStage_true` |
| `dλ`: `A_p dλ = dλ`, every nonempty deletion is zero, Laplace profile `1/t`, neither control condition | `rateDilate_lebesgueRate`, `rateDeletionPart_lebesgueRate`, `rateLaplace_lebesgueRate`, `not_rateControlled_lebesgueRate`, `rateNegMoment_lebesgueRate` |
| `dλ`: infinitely many dilations reach a bounded window; not an Euler reconstruction | `not_rateWindowFinite_lebesgueRate`, `not_rateEuler_eq_lebesgueRate` |
| (9) ghost: `A_p ν_crit = p⁻¹ ν_crit`, `D_S ν_crit = ∏(1 - 1/p) ν_crit ≥ 0`, `L = Γ(3/2) t^{-3/2}` | `rateDilate_criticalGhostRate`, `rateDeletionPart_criticalGhostRate`, `criticalGhostRate_deletion_le`, `rateLaplace_criticalGhostRate`, `sum_even_inv_prod_eq` |
| ghost: cofinal product tends to zero, the cofinal deleted measure is zero on every window; not an Euler reconstruction; no gap and no (W1) | `tendsto_prod_one_sub_inv_of_exhaustion`, `tendsto_criticalGhost_deletion`, `not_rateEuler_eq_criticalGhostRate`, `not_rateControlled_criticalGhostRate`, `rateNegMoment_criticalGhostRate` |
| ghost flux: `e^{3x} b(e^{2x})` is constant, so (8) gives zero; the tail condition excludes it | `criticalGhost_fluxPotential`, `not_thetaFluxSource_criticalGhost` |

The measure-level Möbius inversion is carried out with positive measures only: the Möbius series
(4) is realised as the cofinal limit of the parity parts of the deletions, and window finiteness
supplies the cancellation. Under (W1) the absolute convergence of the double series is the
window-finiteness statement `Σ_{m,n} A_{mn}ν(-∞, R] < ∞`, proved from (W2) and `2q - 2 > 1`.
