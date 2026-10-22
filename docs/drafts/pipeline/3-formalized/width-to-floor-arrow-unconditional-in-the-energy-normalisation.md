# The width bounds the Weil floor with no zero-distribution input, at an H¹ cost

- **ID:** width-floor-energy-normalisation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — a zero-hypothesis-free arrow at an `H¹` cost
- **Source:** the width→floor arrow of `ArithmeticContinuationAndCriticalEnergy` /
  `SquareRootThreshold` (previously proved only under a uniform unit-window bound on the number
  of off-line zeros); `BiScaleUncertainty` §2.4 (the Chebyshev gauge) and the Gamma–Lévy form
  `re_weilFullFunctional_eq_of_compact_finite_jump`.
- **Statement.** For every `β > zetaZeroWidth` there is a constant `C ≥ 0` with

  `Ẑ(F) ≥ −C (1+A) e^{2βA} (∫F² + D)`

  for **every** `C²_c` test `F` supported in `[−A, A]` and every `D` bounding the gauge
  derivative `a′ − a/2` of its autocorrelation `a = autocorr F`.  No hypothesis on the
  distribution of the off-line zeros is used.  Consequently, on every class of tests with
  `|a′ − a/2| ≤ K ∫F²` the plain `L²`-normalised floor `Ẑ(F) ≥ −C(1+K)(1+A)e^{2βA}∫F²` holds
  unconditionally at every aperture.

## Goal
The corpus owned the arrow *width `≤ σ` ⟹ ground-energy floor at rate `2σ`* only under a
non-clustering hypothesis: the zero side of the explicit formula is a sum over zeros, and the
only thing that bounds it is how many off-line zeros sit in one unit height window — a residual
the corpus records as the missing input of that arrow. The question answered here is whether the
hypothesis is about the zeros or about the normalisation.

It is about the normalisation. Read through the prime side instead of the zero side, the floor
costs exactly one test datum — the sup of the gauge derivative of the autocorrelation — and
nothing about the zeros beyond their width.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (composition of four owned theorems; see Approach)
- [x] 2 → 3  formalized:
  `formal/GaloisForLFunctions/SquareRootThreshold/TheWidthBoundsTheEnergyNormalisedWeilFloor.lean`,
  wired into `GaloisForLFunctions.SquareRootThreshold`; both capstones depend only on
  `propext, Classical.choice, Quot.sound`.
- [ ] 3 → 4  publication-ready

## Approach
Four owned ingredients compose, with no analytic input of their own:

1. **The exact Gamma–Lévy form.** `fullZeroForm F = Ω(0)·a(0) + 𝒥(F) − 2·fullPairing(a)`
   (`ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional` +
   `BiScaleUncertainty.SignedPrimePolar.re_weilFullFunctional_eq_of_compact_finite_jump`, whose
   integrability hypothesis is `integrableOn_biScaleLevyIntegrand` for `C²_c` sources). The Lévy
   energy is nonnegative and is dropped, so the floor reduces to an **upper bound on the signed
   prime–polar pairing** of the autocorrelation.
2. **The Stieltjes form of the pairing in the Chebyshev gauge.**
   `ChebyshevGauge.pairing_eq_stieltjes_gauge`:
   `pairing N a = a(0) + Ẽ(L)a(L) − ∫_0^L Ẽ·(a′ − a/2) − ∫_0^L e^{−t/2} a`, `L = log(N+2)`.
   Choosing `N = ⌈e^{2A}⌉ + 1` puts `L` past the autocorrelation aperture `2A`, so `a(L) = 0`
   (`autocorr_eq_zero_of_far`) and `fullPairing a = pairing N a`
   (`fullPairing_eq_pairing_of_tail`). The whole prime side is now two integrals of length
   `L ≤ 2A + 4`.
3. **Generalised von Koch in the gauge.**
   `ChebyshevGauge.exists_abs_normalizedLogError_le_of_xiZeroHalfPlaneBound` applied at
   `α = zetaZeroWidth` (`xiZeroHalfPlaneBound_zetaZeroWidth`) gives `|Ẽ(t)| ≤ C₀ e^{βt}` for
   every `β` above the width. This is the only place the zeros enter, and only through the width.
4. **Trivial sup bounds for the test.** `|a| ≤ a(0)` (`abs_autocorr_le_zero`), `e^{−t/2} ≤ 1`,
   and `|a′ − a/2| ≤ D` by hypothesis. The two integrals are then at most
   `L·a(0)` and `L·C₀e^{βL}·D`.

The exponent bookkeeping is `e^{β(2A+4)} = e^{4β}e^{2βA}`, so the rate is `2β` and the loss is
the harmless polynomial factor `1 + A`.

## Exact standing relative to the owned route
The corpus's floor from the width,
`exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineDepthLocallyBounded`, carries the
hypothesis `OffLineDepthLocallyBounded W` — and that hypothesis is **not** unconditionally
available: `exists_unsignedDepthSamplingBound_iff` shows it is equivalent to an unsigned
sampling bound at one aperture, and the unconditional local count
(`RHTower.card_le_of_ordinates_in_window`, `Nd_le_of_local_count`) gives only
`W(T) ≍ log T`, which is height-dependent. So the two statements are incomparable:

| | zero hypothesis | normalisation | tests covered |
|---|---|---|---|
| owned route | `OffLineDepthLocallyBounded W` | `∫F²` | all |
| here | none | `∫F² + sup|a′ − a/2|` | all |
| canonical target | none | `∫F² + 𝒥(F)` | all |

The third line is where both mechanisms actually point, and it is **not** proved here. On the
zero side, replacing the uniform window bound `W` by the unconditional count `≍ log T` turns the
sampling inequality's uniform weight into the weight `log(2+|ξ|)` against `|F̂|²` — which is the
archimedean Lévy energy `𝒥(F)` itself. On the prime side, the discrepancy transform
(`fourierPairing_eq_discrepancy_transform`, `gaugeDerivative_frequencyCharacter`) gives the
pairing at frequency `ξ` as `s(ξ)·Ê_L(ξ)` plus bounded terms, with `s(ξ) = ½ + 2πiξ`; the sup
bound used here pays the whole factor `|s(ξ)| ≍ |ξ|`, and bringing it down to `log|ξ|` needs the
cancellation in `Ê_L` — i.e. `Re(−ζ′/ζ)(½+iξ) ≍ log|ξ|`, which is the Hadamard structure of the
zero side (owned: the sharp Landau bound and Hadamard positivity in the strip), not anything the
gauge alone can supply.

**So the price of the plain `L²` normalisation in the width→floor arrow is exactly a local zero
count, and the price of avoiding any zero input by the gauge alone is a full power of the
frequency instead of its logarithm.**  What is new here is only the unconditional arrow at the
`H¹`-type cost; what it does *not* do is reach the canonical `𝒥`-normalised floor.

A logarithmic loss would be harmless: by `riemannHypothesis_of_subexponential_odd_floor` the RH
criterion tolerates any subexponential-in-aperture defect, and on a fixed-shape test family the
frequency — hence the logarithm — is bounded. The canonical target is therefore worth proving,
and the route is named above.

## Lean (unconditional, standard axioms only)
- `exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt` — the energy-normalised arrow:
  `β > zetaZeroWidth ⟹ ∃C, Ẑ(F) ≥ −C(1+A)e^{2βA}(∫F² + D)` for all `C²_c` `F` of aperture `A`
  with gauge-derivative datum `D`.
- `exists_fullZeroForm_ge_neg_mass_of_zetaZeroWidth_lt` — the `L²` arrow on a
  bounded-gauge-oscillation class, with constant `C(1+K)`.
- Private: `abs_fullPairing_autocorr_le` (the Chebyshev-gauge bound for the pairing — the prime
  side costs one gauge derivative), `gaugeIndex` and its two cutoff estimates.

## Units
The contribution is a discharge, not a number: the arrow from the width to the floor now needs no
zero-distribution input, and the residual that remains is identified exactly (the high-frequency
tail of the `L²`-normalised infimum). Any lane that proves a floor along a fixed-shape family
therefore gains nothing from the width it already has — and conversely, a floor proved at rate
`2σ` with `σ` below the best known width bound is the only kind that can carry information.

## Log
- 2026-10-22 — created at stage 3; module written, compiled, wired into `SquareRootThreshold`.
