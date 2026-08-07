# Session index: the Halász programme and the product-occupancy layer

- **ID:** halasz-programme-index
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — index card
- **Statement:** Index of the nineteen modules built on 2026-08-07, what each proves, and the two
  honest no-gos that bound the programme.

This card exists so the programme is discoverable as one thing. The mathematics is on
`product-occupancy-dichotomy-euler-edge.md` and `multiplicative-euler-bound-halasz-input.md`; this is the
map. Every module below is `lake build` green, axiom-clean
(`[propext, Classical.choice, Quot.sound]`), and wired into its area umbrella.

## Layer A — the hitting dichotomy of a product of laws on `ℕ`

| Module | Content |
|---|---|
| `HTGeometry/ProductOccupancyDichotomy` | `Π {k \| hit set infinite} = 1 ↔ ∑_i μ_i(t_i) = ∞`, for an arbitrary local target family; independence of the hitting events; `tsum_ofReal_ne_top_iff_summable` |
| `HTGeometry/ProductTailZeroOne` | Kolmogorov's zero-one law for the same product; the hitting event is a tail event |
| `HTGeometry/GeometricTailMass` | `geometricMeasure_Ici` — the geometric tail mass (a mathlib gap) |
| `HTGeometry/PrimeValuationInfiniteSupport` | the sector's occupancy masses are `1/p`; **the integers are null in the sector** |
| `HTGeometry/PrimeValuationLevelStructure` | level masses `p^{-m}`; a.s. squarefree away from a finite set; **the complete carrier: infinitely many prime divisors, almost all simple** |
| `HTGeometry/DiameterCoveringMeasure` | pairwise-close sets are thin; thin-in-every-cell ⇒ thin on `[-T,T]` |
| `RHTower/EulerActivationOccupancyPhaseTransition` | the activation product at every `σ ≥ 0`; **the Euler edge is the sharp occupancy boundary** |
| `RHTower/EulerActivationLevelCascade` | one boundary per level at `1/m`; **the critical line is the level-two boundary**; the critical source is squarefree at infinity |

## Layer B — Halász's method for the actual Dirichlet series

| Module | Content |
|---|---|
| `RHTower/Sieve/MultiplicativeEulerBound` | `‖∑_n f(n)n^{-s}‖ ≤ exp(∑_p Re(f(p)p^{-s}) + 5/2)`; the distance form |
| `RHTower/Sieve/PrimeAbscissaSumBound` | `P(σ) ≤ log(1+1/(σ−1)) + 1`; the Halász input in closed form |
| `RHTower/Sieve/DistanceAbscissaBridge` | the polar split; abscissa-weighted ↔ harmonic distance, free at `σ = 1+1/log z` |
| `RHTower/Sieve/HalaszFullSeriesSum` | trivial size, far-frequency damping, the discrete large-values input |
| `RHTower/Sieve/HalaszLargeValueWindow` | large values confined to one window; the measure bound |
| `RHTower/Sieve/HalaszIntegralBound` | continuity in the frequency; the `t`-integral |
| `RHTower/Sieve/HalaszPerronAssembly` | the Perron assembly; both kernel quantities discharged |
| `RHTower/Sieve/HalaszUniformDistance` | the window-free form under a uniform distance bound — the route's endpoint |
| `RHTower/Sieve/PrimeCosineSumUpper` | the upper-direction passage (mirror of the corpus's lower one) |
| `RHTower/Sieve/CharacterDistanceLower` | the window-free lower bound for `D(n^{it}, n^{iu})²` |

## The two no-gos

1. **The pointwise route is `(log N)²` short of Halász.** With the damped bound holding pointwise (which
   a uniform distance bound gives), `2π‖∑ f(n)w(n)‖ ≤ damped·∫‖W‖ ≍ N(log N)²e^{-M}`, while Halász's
   `(1+M)e^{-M}` has prefactor `log log N`. The deficit is structural: bounding `∫‖F‖‖W‖` by
   `(sup‖F‖)·∫‖W‖` discards all cancellation of `F` across the range. The missing input is a mean-square
   estimate (`DirichletMeasureLargeValues`, `DirichletIntegralMeanValue`), which is a different theorem.
2. **The degree-six Route R endpoint is RH itself.** `R_phys(B_6) = τ_6(B_6)` unfolds, using the corpus's
   own definitions, to `sinh((2Re ρ − 1) log 6) = 0`. The operator side is `ρ`-free; the physical side is
   odd and strictly monotone in `Re ρ − 1/2`. No source-side theorem can supply it, and no strictly
   weaker law can imply it. Details on
   `1-in-progress/route-r-degree-six-bv-green-physical-cyclic-producer.md`.

## What a successor should pick up

The mean-square input of no-go 1, applied to the truncated Dirichlet polynomial rather than the full
series. Everything else in Layer B — Euler bound, trivial size, distance bridge, Perron assembly — is
needed by that route unchanged.

## First brick of the successor task

`RHTower/Sieve/DirichletTruncationError.lean` (9023 jobs, exit 0, axiom-clean, wired):

- `tsum_tail_rpow_neg_le` — `∑_{n > L} n^{-σ} ≤ L^{1-σ}/(σ−1)`, by the integral test from `L`
  (`AntitoneOn.tsum_comp_add_le_integral` + `integral_Ioi_rpow_of_lt`), reusing
  `antitoneOn_rpow_neg_Ici`.
- `norm_tsum_sub_sum_range_le`, `norm_tsum_sub_sum_range_le_pow` — **the truncation error**:

  `‖∑_n f(n)n^{-s} − ∑_{n ≤ L} f(n)n^{-s}‖ ≤ ∑_{n>L} n^{-σ} ≤ L^{1-σ}/(σ−1)`.

Every mean-square estimate in the corpus (`DirichletIntegralMeanValue`,
`DirichletMeasureLargeValues`) is stated for a Dirichlet *polynomial* of finite length, whereas the Euler
bound is about the whole series; this is the passage between them, and it was missing. At
`σ = 1 + A/log L` the error is `e^{-A}(log L)/A`, so the truncation is harmless once the polynomial is
longer than the abscissa's reciprocal scale — which is the regime the mean-square route works in.

## Second brick: the truncation is a Dirichlet polynomial

`RHTower/Sieve/TwistedSeriesAsDirichletPoly.lean` (9071 jobs, exit 0, axiom-clean, wired):

- `twistedTruncCoeff f σ L : Fin L → ℂ` — the coefficients `f(k+1)(k+1)^{-σ}`, with
  `norm_twistedTruncCoeff_le`.
- `sum_range_twistedSummand_eq_dirPoly` — **the identification**:
  `∑_{n ≤ L} f(n)n^{-(σ+it)} = dirPoly L (twistedTruncCoeff f σ L) (-t)`, by the polar split of
  `DistanceAbscissaBridge` (the abscissa goes into the coefficients, the frequency flips sign).
- `sum_norm_sq_twistedTruncCoeff_le` — `∑_k ‖a_k‖² ≤ ∑_n n^{-2σ}`, uniformly in `L`: exactly the
  quantity `volume_largeValues_le` and `DirichletIntegralMeanValue` consume.

With the truncation error of the previous brick, the corpus's mean-square machinery now applies to a
bounded multiplicative Dirichlet series. The remaining step of the successor task is the optimisation
itself — feeding `integral_norm_dirPoly_halasz` the damped sup bound and choosing `V`.
