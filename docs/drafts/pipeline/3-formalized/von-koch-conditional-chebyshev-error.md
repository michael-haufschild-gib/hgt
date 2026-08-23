# Von Koch: the RH-conditional Chebyshev error bound

- **ID:** `von-koch-conditional-chebyshev-error`
- **Stage:** 1-in-progress
- **Type:** CLASSICAL INPUT / LEAN INFRASTRUCTURE
- **Opened:** 2026-08-23
- **Blocks:** `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/square-aperture-von-mangoldt-correlation-energy.md`

## Target

```lean
theorem chebyshev_error_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |chebyshevPsiReal x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2
```

The consumer card only needs the weaker subpower form `|ψ(x) − x| ≪_ε x^{1/2+ε}`; the sharp
`√x log²x` is the natural statement and costs nothing extra once the contour is in place.

## Why it is needed

`square-aperture-von-mangoldt-correlation-energy` proves `RH ⟹ C_M = O_δ(M^{1+δ})` by inserting
von Koch into the already-formalized exact Abel identity
`W(n) − c√n = R(n)/√n − R(n/2)/√(n/2) + ½∫_{n/2}^n R(t) t^{-3/2} dt`.
Everything else on that card — the finite Fubini identity `C_M = Σ_{m≤M}(W(m²)−cm)²` and the
forward implication to RH — is already Lean-closed in
`RHTower.CCMSharpPrimeWindowSquareCorrelationEnergy`.

## Corpus and Mathlib inventory

Vendored `GaloisForLFunctions/PNTPlus/` already supplies the whole unconditional architecture:

- `PerronFormula.lean` — vertical/rectangle contour calculus, `tendsto_truncated_vertical_shift_with_simple_pole`.
- `ZetaBounds.lean` — `ZetaZeroFree`, `LogDerivZetaBnd`, `LogDerivZetaBndUnif`, `ZetaInvBnd`,
  `LogDerivZetaHolcSmallT`, `LogDerivZetaHolcLargeT`, `ZetaNoZerosInBox`,
  `dlog_riemannZeta_bdd_on_vertical_lines_generalized`.
- `MediumPNT.lean` — `SmoothedChebyshev`, `SmoothedChebyshevDirichlet`, `SmoothedChebyshevClose`,
  `SmoothedChebyshevPull1`, `SmoothedChebyshevPull2`, `ZetaBoxEval`.
- `MellinCalculus.lean`, `ResidueCalcOnRectangles.lean`, `Rectangle.lean`.

The corpus also owns `RHTower.chebyshevPsiReal`, `RHTower.psi_eq_chebyshevPsi_floor`,
`RHTower.chebyshevPsiReal_eq_sum_Icc`, and the whole Xi explicit-formula stack
(`XiExplicitFormulaLogDeriv.xi_explicitFormula_logDeriv`, `XiGuinandWeilExplicitFormula`).

NOT present anywhere: any RH-conditional bound on `ζ'/ζ` or on `ψ(x) − x`.  Searches run:
"RiemannHypothesis implies chebyshev error subpower", "of_riemannHypothesis psi error",
`grep "(hRH : RiemannHypothesis)"` across `RHTower/`.  The only RH-forward theorems found are
spectral (`riemannHypothesis_iff_suzukiExplicitScrewBounded`,
`exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis`), and
`suzukiPsi` is the Xi zero series, not the Chebyshev error.

## Layer plan

1. **(VK1) Zero counting.**  `N(T+1) − N(T) ≪ log(T+2)`, and hence `Σ_{|γ| ≤ T} 1/|ρ| ≪ (log T)²`.
   Route: Jensen / the argument principle on discs of radius `4` around `2 + iT`, with the
   Hadamard-factorization bound `|ξ(s)| ≤ exp(C |s| log |s|)`.
2. **(VK2) RH bound on the logarithmic derivative.**  Under RH,
   `|ζ'/ζ(s)| ≪ (log |t|)²` uniformly for `Re s ≥ 1/2 + 1/log|t|`, `|t| ≥ 2`.
   Route: Borel–Carathéodory plus (VK1); this is where RH enters, through
   `Re s − 1/2 > 0 ⟹ s is not a zero`.
3. **(VK3) Truncated Perron.**  `ψ(x) = (1/2πi)∫_{c−iT}^{c+iT}(−ζ'/ζ)(s) x^s/s ds + O(x log²x / T)`
   with `c = 1 + 1/log x`.  Reuse `PNTPlus/PerronFormula.lean`.
4. **(VK4) Contour shift and assembly.**  Move to `Re s = 1/2 + 1/log x`, pick up the residue `x`
   at `s = 1`, bound the three remaining edges with (VK2), and take `T = √x`.

## Log

- 2026-08-23 -- Opened after `baez-duarte-critical-mobius-beta-wavelet-law` reached stage 3
  (9 / 13 cards of `09-mobius-prime-sums`).  Inventory above completed; no existing RH-conditional
  prime-error bound in Mathlib or the corpus.

## Corpus survey (2026-08-23) — what exists and where the wall is

ASSETS FOUND (do not rebuild):
- `RHTower/RiemannVonMangoldt.lean` — `exists_xiZeroCount_close`: the UNCONDITIONAL Riemann–von
  Mangoldt asymptotic `N(T) = (1/2π) T log T (1 + o(1))`.  This is `VK1`; it is already done.
- `RHTower/Sieve/ZetaLandauWide.lean` — `zeta_landau_wide`: Landau's lemma at the centre
  `9/8 + iγ`.  Zeros are collected in the disc of radius `21/40`; the partial-fraction identity
  `‖ζ'/ζ(z) − ∑_{ρ∈Z} m_ρ/(z−ρ)‖ ≤ (320/21)·wideD·log|γ|` holds only on radius `21/160`.
- `RHTower/Sieve/ZetaZeroCountWide.lean` — `exists_wide_zero_count`: `∑_{ρ∈Z} m_ρ ≤ E log|γ|`.
- `RHTower/Sieve/ZetaLogDerivWidthBound.lean` — `exists_logDeriv_zeta_bound_of_width`: a FULLY
  PARAMETRIC `ζ'/ζ` bound `≤ C log|γ| / w(|γ|+1)` for a zero-free region of arbitrary antitone
  width `w`, valid on `1 − w/2 ≤ σ ≤ 9/8`.
- `PNTPlus/ZetaBounds.lean` — `ZetaUpperBnd`, `ZetaDerivUpperBnd`, `ZetaInvBnd`, `ZetaZeroFree`,
  `LogDerivZetaBnd`, `LogDerivZetaHolcLargeT`, and `ζ` growth bounds for `σ ∈ Ioc 0 2`.
- `PNTPlus/MediumPNT.lean` — the full smoothed-Chebyshev contour-pull apparatus
  (`SmoothedChebyshevPull1/2`, `I1Bound`…`I9Bound`, `ZetaBoxEval`).

THE WALL, precisely.  Feeding `w ≡ 1/2` (the RH zero-free region `σ > 1/2`) into
`exists_logDeriv_zeta_bound_of_width` gives `‖ζ'/ζ‖ ≪ log|γ|` only on `σ ≥ 3/4`, because the
theorem keeps a safety margin of half the width.  Shifting the Perron contour only to `σ = 3/4`
yields `ψ(x) − x ≪ x^{3/4} log^k x`, and then `C_M ≪ M^{3/2}`, which does NOT meet the card's
`O_δ(M^{1+δ})`.  `√x log²x` is genuinely required.

The obstruction is the RADIUS of the Landau disc, not the argument.  Landau's lemma is applied with
identity radius = (zero radius)/4; to reach `σ = 1/2 + δ` from the centre `9/8` the identity radius
must exceed `5/8`, so the zero-collection radius must exceed `5/2`, so the GROWTH bound for `ζ`
must hold on a disc reaching `σ ≈ −11/8`.  The corpus's growth input (`ZetaWideDisc.lean`,
`‖ζ‖ ≤ 91 + 40|γ|` on radius `11/10`) and PNTPlus's bounds both stop at `σ > 0`.

## Revised layer plan

- `VK0` (NEW, the actual gate): `ζ` growth on a disc reaching `σ < 0`.  Via the functional
  equation `ζ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)` (`riemannZeta_one_sub` in mathlib) plus
  the corpus's Stirling ladder for `Γ`, giving `|ζ(σ+it)| ≪ |t|^{1/2−σ}` for `σ ≤ 0`, hence a
  polynomial bound on the disc `|z − (9/8 + iγ)| ≤ 3`.
- `VK1` DONE — `exists_xiZeroCount_close`.
- `VK2`: re-run `zeta_landau_wide` at the larger radius using `VK0`, then re-run
  `exists_logDeriv_zeta_bound_of_width` with the distance-to-zeros hypothesis replaced by
  "all zeros have `Re ρ = 1/2`", giving `‖ζ'/ζ(σ+iγ)‖ ≪ log|γ| / (σ − 1/2)` for `1/2 < σ ≤ 9/8`.
- `VK3`: truncated Perron for `ψ` (PNTPlus `PerronFormula.lean`).
- `VK4`: shift to `σ = 1/2 + 1/log x`, take `T = √x`, conclude `|ψ(x) − x| ≪ √x (log x)²`.

Only an absolute constant is needed — the card's `(7)` uses `O(log n²)`, so Schoenfeld's sharp
`1/(8π)` is NOT required.

## VK0 and VK2 CLOSED (2026-08-23)

`VK0` was already corpus-owned and my first attempt duplicated it.  The corpus's
`RHTower/ZetaVerticalStripPolynomialBound.lean` proves
`exists_bound_norm_riemannZeta_strip (M : ℝ) : ∃ C N, 0 ≤ C ∧ ∀ σ t, |σ| ≤ M → 1 ≤ |t| →
 ‖ζ(σ+it)‖ ≤ C|t|^N` — polynomial growth on ANY vertical strip, via the functional equation, the
`Γ` strip decay of `HTGeometry/GammaVerticalStripDecay.lean`, and `norm_cos_le_exp_abs_im`.
`RHTower/ZetaStripPolynomialBound.lean` supplies `norm_riemannZeta_le_of_two_le_re` and
`norm_riemannZeta_le_quarter`.  My duplicate was discarded.

`VK2` is now Lean-closed in two new modules.

`RHTower/Sieve/ZetaLandauCriticalDisc.lean`
- `critCentre γ = 9/8 + iγ`; `crit_disc_parts` (`|Re w| ≤ 8`, `1 ≤ |Im w| ≤ 2|γ|` on the disc of
  radius 6, for `|γ| ≥ 7`); `exists_crit_disc_bound` (growth on that disc from `VK0`);
  `zeta_analytic_crit`; `crit_disc_ne_one`.
- `exists_crit_landau_data`: Landau's lemma (`Sieve/LandauLemma.lean`, which is FULLY GENERAL in
  `R`, `R₀`, `M`) at radius `R = 5` inside `R₀ = 6`.  Zeros are collected within `5/2`, and the
  partial-fraction identity holds within `5/8` — and `9/8 − 5/8 = 1/2` EXACTLY, so the identity
  reaches the critical line.  The Landau ratio is `1 + C|γ|^N/‖ζ(9/8+iγ)‖`, whose logarithm is
  `≤ D log|γ|` by the de la Vallée Poussin lower bound `neg_log_norm_riemannZeta_le`.
  THIS IS THE STEP THE OLD `zeta_landau_wide` COULD NOT DO: its identity radius `21/160` only
  reached `σ = 159/160`.

`RHTower/Sieve/ZetaLogDerivCriticalBound.lean`
- `crit_re_inv_ge`: `Re((c−ρ)⁻¹) ≥ (1/8)/(5/2)² = 1/50` for every zero of the disc — UNCONDITIONAL
  (only `Re ρ ≤ 1` is used).
- `exists_crit_zero_count`: `∑_{ρ} m_ρ ≤ 50 D log|γ| + 50(8+E)`, by keeping the retained zeros in
  Landau's inequality at the centre, exactly as `exists_wide_zero_count` does at the old radius.
- `re_eq_half_of_rh`: under mathlib's `RiemannHypothesis`, a zero with nonzero ordinate has
  `Re ρ = 1/2` (the trivial zeros and the pole are excluded by the ordinate).
- **`exists_logDeriv_zeta_bound_rh`**:
  ```
  RiemannHypothesis → ∃ C > 0, ∀ σ γ, 7 ≤ |γ| → 1/2 < σ ≤ 9/8 →
      ‖ζ'/ζ(σ + iγ)‖ ≤ C · log|γ| / (σ − 1/2).
  ```
  Under RH every retained zero is at distance `≥ σ − 1/2` from `σ + iγ`, so the partial fraction
  costs `(zero count)/(σ − 1/2)`.  At `σ = 1/2 + 1/log x` this is the classical `O(log²)`.

REMAINING: `VK3` (truncated Perron for `ψ`) and `VK4` (shift to `σ = 1/2 + 1/log x`, `T = √x`).

## VK3 CLOSED (2026-08-23)

`RHTower/Sieve/PerronInfiniteSeries.lean` — the truncated Perron formula for an INFINITE Dirichlet
series.  This is the piece the corpus was missing: `Sieve/PerronFiniteSum.lean` proves it only for a
`Finset`, and its error `∑_{n∈s} ‖c_n‖(x/n)^σ/(πT|log(x/n)|)` cannot be pushed to the full series by
truncating the polynomial — the tail `∑_{n>M}Λ(n)n^{-σ}` is `≍ log x` on the WHOLE line at
`σ = 1 + 1/log x`, so its contribution to the vertical integral is `≫ x log x log T`, hopeless.

- `perronTerm c x σ n t = c_n·(x/n)^{σ+it}/(σ+it)`, `norm_perronTerm_le`, `continuous_perronTerm'`.
- `perron_tsum_integral_eq`: `(1/2π)∫_{-T}^{T} (∑'_n c_n n^{-s})·x^s/s dt = ∑'_n c_n·perronVertical σ T (x/n)`.
  The interchange is `MeasureTheory.hasSum_integral_of_summable_integral_norm`, whose hypothesis
  `Summable (fun n ↦ ∫‖perronTerm n‖)` follows from `‖perronTerm n t‖ ≤ ‖c_n‖(x/n)^σ/σ` and
  `Summable (fun n ↦ ‖c_n‖(x/n)^σ)`.
- `norm_tsum_lt_sub_perron_integral_le`:
  ```
  ‖∑'_{n<x} c_n − (1/2π)∫_{-T}^{T} (∑'_n c_n n^{-s})·x^s/s dt‖
      ≤ ∑'_n ‖c_n‖·(x/n)^σ/(πT|log(x/n)|).
  ```
  The per-term estimates are the corpus's `norm_perronVertical_sub_one_le` (for `n < x`) and
  `norm_perronVertical_le` (for `n > x`), unchanged; only the summability bookkeeping is new.

REMAINING for card 10: `VK4` only — instantiate with `c = Λ`, `x = N + 1/2`, `σ = 1 + 1/log x`,
`T = x`; bound the error sum (`≪ x log²x/T`, splitting at `x/2 < n < 2x` exactly as `(E5)`/`(E6)`
of card 13 do); then shift the contour to `σ = 1/2 + ε` using `exists_logDeriv_zeta_bound_rh`,
picking up the residue `x` at `s = 1`.

## The Perron error is now bounded (2026-08-23)

`RHTower/Sieve/VonMangoldtPerronSeries.lean`
- `tsum_vonMangoldt_cpow_neg : 1 < Re s → ∑'_n Λ(n)·n^{-s} = −ζ'/ζ(s)` — the bridge between
  mathlib's `LSeries` (which divides by `n^s`) and the Perron statement (which multiplies by
  `n^{-s}`); they agree termwise away from `n = 0`, where both vanish.
- `summable_vonMangoldt_perron : 0 < x → 1 < σ → Summable (fun n ↦ ‖Λ(n)‖·(x/n)^σ)` — the
  hypothesis `perron_tsum_integral_eq` needs, obtained from `LSeriesSummable_vonMangoldt` by
  factoring out `x^σ`.

`RHTower/Sieve/PerronErrorSplit.lean`
- `perron_error_far_le`: outside `[x/2, 2x]` the logarithm exceeds `log 2`, so
  `∑'_{far} ‖c_n‖(x/n)^σ/(πT|log(x/n)|) ≤ (1/(πT log 2))·∑'_n ‖c_n‖(x/n)^σ`.
- `sum_inv_dist_halfInt_le (N) (s) : ∑_{n∈s} 1/|N + 1/2 − n| ≤ 4(1 + log |s|)` — at a half-integer
  cutoff the distances are half-odd-integers, all distinct, so the corpus's
  `sum_inv_abs_le_of_injOn` applies after clearing the factor 2.

`RHTower/Sieve/PerronErrorNearHalfInt.lean`
- `perron_error_near_halfInt_le`: with `x = N + 1/2`, `0 < σ ≤ 2` and `‖c_n‖ ≤ B`,
  ```
  ∑'_{x/2 ≤ n ≤ 2x} ‖c_n‖·(x/n)^σ/(πT|log(x/n)|) ≤ (16Bx/(πT))·4(1 + log(2N+2)).
  ```
  The mechanism is card 13's `abs_sub_one_le_two_mul_abs_log`: `|log(x/n)| ≥ |x−n|/(4x)` on the
  window, so the near part is a reciprocal-distance sum, which `sum_inv_dist_halfInt_le` bounds.
  With `σ = 1 + 1/log x` and `B = log(2x)` this is `≪ x log²x / T`, the classical shape.

REMAINING for card 10: the contour shift alone.  Everything it consumes is now in place:
`norm_tsum_lt_sub_perron_integral_le` (the formula), the two error halves above (the error), and
`exists_logDeriv_zeta_bound_rh` (the bound on the shifted line).  PNTPlus's `Rectangle.lean`,
`ResidueCalcOnRectangles.lean` and `PerronFormula.lean` supply the rectangle machinery
(`HolomorphicOn.upperUIntegral_eq_zero`, `RectangleIntegral`, residue extraction).

## VK4: the contour shift, first half (2026-08-23)

`RHTower/Sieve/ContourShiftIdentity.lean`
- `vIntegral_shift (f σ₁ σ₀ T)`:
  ```
  VIntegral f σ₀ (−T) T
    = RectangleIntegral f (σ₁ − iT) (σ₀ + iT) + VIntegral f σ₁ (−T) T
      + HIntegral f σ₁ σ₀ T − HIntegral f σ₁ σ₀ (−T).
  ```
  An IDENTITY, not an estimate — it is `RectangleIntegral` unfolded and rearranged.  PNTPlus's
  `ResidueCalcOnRectangles.lean` supplies `HIntegral`, `VIntegral`, `RectangleIntegral`.

`RHTower/Sieve/PerronIntegrandResidue.lean`
- `differentiableAt_perronKernel`, `perronKernel_at_one` (`x^1/1 = x`),
  `perronKernel_isBigO_one`, `perronKernel_slope_isBigO` (the difference quotient of `x^s/s` at
  `s = 1` is bounded, via `hasDerivAt_iff_tendsto_slope`).
- `perron_integrand_residue`:
  ```
  ((−ζ'/ζ)(s)·x^s/s − x/(s−1)) =O[𝓝[≠] 1] 1,
  ```
  i.e. the integrand has a SIMPLE POLE AT `s = 1` WITH RESIDUE `x`.  The split is
  `[(−ζ'/ζ)(s) − (s−1)^{-1}]·(x^s/s) + (x^s/s − x)/(s−1)`; the first factor of the first term is
  PNTPlus's `riemannZetaLogDerivResidueBigO`, and the second term is the difference quotient.

`RHTower/Sieve/PerronRectangleResidueUnderRH.lean`
- `riemannZeta_ne_zero_of_rh : RiemannHypothesis → 1/2 < Re s → s ≠ 1 → ζ(s) ≠ 0` (the trivial
  zeros are excluded by their real part).
- `rectangleIntegral_perron_eq`: under RH, for `1/2 < σ₁ < 1 < σ₀` and `T > 0`,
  ```
  RectangleIntegral' ((−ζ'/ζ)(s)·x^s/s) (σ₁ − iT) (σ₀ + iT) = x.
  ```
  Via PNTPlus's `ResidueTheoremOnRectangleWithSimplePole'`; RH supplies exactly the holomorphy of
  the integrand on the rectangle minus the pole.

NOTE: a module `GaloisForLFunctions.RHTower.PerronRectangleResidue` already exists (different
namespace path); the new one is `…RHTower.Sieve.PerronRectangleResidueUnderRH`.

REMAINING for card 10: bound the two horizontal segments `HIntegral f σ₁ σ₀ (±T)` and the shifted
vertical `VIntegral f σ₁ (−T) T` using `exists_logDeriv_zeta_bound_rh`, then assemble with
`vIntegral_shift`, `rectangleIntegral_perron_eq`, the Perron formula and its two error halves.

## VK4: the side estimates (2026-08-23)

`RHTower/Sieve/ZetaLogDerivLineBound.lean`
- `continuousOn_logDeriv_zeta_segment`: under RH, `ζ'/ζ` is continuous on `{σ + it : |t| ≤ T}` for
  `1/2 < σ < 1` — `ζ` has no zero there (`riemannZeta_ne_zero_of_rh`) and the pole is to the right.
- `exists_logDeriv_zeta_line_bound`:
  ```
  RiemannHypothesis → 1/2 < σ < 1 → ∃ K > 0, ∀ t, ‖ζ'/ζ(σ+it)‖ ≤ K(1 + log(2 + |t|)).
  ```
  ONE constant for the whole line: `exists_logDeriv_zeta_bound_rh` above height `7`, compactness
  below it.  The `|γ| ≥ 7` restriction of the Landau bound is exactly what this removes.

`RHTower/Sieve/VerticalLogWeight.lean`
- `norm_sigma_add_mul_I_ge`, `abs_le_norm_sigma_add_mul_I`: `‖σ+it‖ ≥ σ` and `≥ |t|`.
- `integral_log_weight_le`:
  ```
  ∫_{-T}^{T} (1 + log(2+|t|))/‖σ+it‖ dt ≤ 2(1+log 3)/σ + 2(1+log(2+T))·log T.
  ```
  Split at `|t| = 1`: on the unit block the denominator is `≥ σ`; outside it the integrand is at
  most `(1+log(2+T))/|t|`, whose integral is `integral_one_div`.  This is the `O(log²T)` that makes
  the shifted vertical side `≪ x^σ log²T`.

REMAINING for card 10: assemble.  Every ingredient is Lean-closed —
`norm_tsum_lt_sub_perron_integral_le` (Perron), `perron_error_far_le` + `perron_error_near_halfInt_le`
(its error), `vIntegral_shift` (the shift), `rectangleIntegral_perron_eq` (the residue `x`),
`exists_logDeriv_zeta_line_bound` + `integral_log_weight_le` (the shifted side), and the same two
for the horizontal sides.

## VK4: all four sides of the contour (2026-08-23)

`RHTower/Sieve/PerronVerticalSide.lean`
- `norm_perron_integrand_line`: `‖(−ζ'/ζ)(σ+it)·x^{σ+it}/(σ+it)‖ ≤ (K x^σ)·(1+log(2+|t|))/‖σ+it‖`.
- `norm_vIntegral_perron_le`: the shifted vertical side is
  `≤ (K x^σ)·(2(1+log 3)/σ + 2(1+log(2+T))·log T)` — `x^σ` times the weight integral.

`RHTower/Sieve/PerronHorizontalSide.lean`
- `norm_hIntegral_perron_le`: each horizontal side is
  `≤ (C log|y|/(σ₁−1/2))·(x^{σ₀}/|y|)·|σ₀−σ₁|` — a factor `1/|y|` smaller than the vertical sides,
  which is what lets the truncation height be taken large.  Uses `exists_logDeriv_zeta_bound_rh`
  UNIFORMLY in `σ ∈ (1/2, 9/8]`, which is exactly the range the Landau disc covers.

`RHTower/Sieve/PerronContourAssembly.lean`
- `norm_two_pi_I_inv : ‖1/(2πi)‖ = 1/(2π)`.
- `norm_vIntegral'_perron_sub_le`: under RH,
  ```
  ‖VIntegral' f σ₀ (−T) T − x‖ ≤ (1/2π)(‖VIntegral f σ₁ (−T) T‖ + ‖HIntegral f σ₁ σ₀ T‖
                                          + ‖HIntegral f σ₁ σ₀ (−T)‖).
  ```
  The shift identity divided by `2πi`, with the rectangle replaced by its residue `x`.  This is the
  contour shift in the form the Perron formula consumes.

REMAINING for card 10: substitute `x = N + 1/2`, `σ₀ = 1 + 1/log x`, `σ₁ = 1/2 + ε`, `T = x`, and
combine `norm_tsum_lt_sub_perron_integral_le` with the above to reach
`|ψ(N) − N| ≤ C_ε N^{1/2+ε}`.  This is bookkeeping — no analytic input is missing.

## The master inequality (2026-08-23)

`RHTower/Sieve/LogDominatedByPower.lean`
- `log_sq_le_rpow_div : 1 ≤ y → 0 < δ → (log y)² ≤ y^δ/(δ/2)²`.  (`Real.log_le_rpow_div` is
  MATHLIB-owned — my first version duplicated it, the fifth duplication caught this session.)

`RHTower/Sieve/PerronChebyshevIdentification.lean`
- `tsum_indicator_vonMangoldt_eq (N) : ∑'_{n < N+1/2} Λ(n) = ∑_{n ∈ [1,N]} Λ(n)` — the Perron sum
  at a half-integer cutoff IS the Chebyshev function.
- `perron_integral_eq_vIntegral' : 1 < σ → (1/2π)∫_{-T}^{T}(∑'_n Λ(n)n^{-s})·x^s/s dt
  = VIntegral' ((−ζ'/ζ)(s)·x^s/s) σ (−T) T` — the Perron integral IS the normalised vertical
  integral.  `(1/(2πi))·i = 1/(2π)`.

`RHTower/Sieve/ChebyshevMasterInequality.lean`
- `summable_perron_error`: the Perron error series converges — near part finitely supported, far
  part dominated by `(1/(πT log 2))·‖c_n‖(x/n)^σ`.
- **`norm_chebyshev_sub_halfInt_le`**: under RH, for `1/2 < σ₁ < 1 < σ₀` and `T > 0`,
  ```
  |∑_{n≤N} Λ(n) − (N + 1/2)|
      ≤ ∑'_n ‖Λ(n)‖·(x/n)^{σ₀}/(πT|log(x/n)|)
        + (1/2π)(‖VIntegral f σ₁ (−T) T‖ + ‖HIntegral f σ₁ σ₀ T‖ + ‖HIntegral f σ₁ σ₀ (−T)‖),
  ```
  with `x = N + 1/2` and `f(s) = (−ζ'/ζ)(s)·x^s/s`.  Perron plus the shifted contour, with nothing
  left implicit; `hne` is discharged by `omega` on `2n = 2N+1`.

REMAINING for card 10: choose `σ₁ = 1/2 + ε/2`, `σ₀ = 1 + 1/log x`, `T = x` and bound each of the
four terms by `C_ε N^{1/2+ε}`, using `exists_pole_bound` for `−ζ'/ζ(σ₀) ≤ log x + A`,
`perron_error_far_le` / `perron_error_near_halfInt_le` for the error, `norm_vIntegral_perron_le` /
`norm_hIntegral_perron_le` for the sides, and `log_sq_le_rpow_div` to absorb the logarithms.

## The Perron error for `ψ`, in closed form (2026-08-23)

`RHTower/Sieve/VonMangoldtPerronMass.lean`
- `tsum_vonMangoldt_mass_le : 0 < x → 1 < σ ≤ 2 → ∑'_n ‖Λ(n)‖(x/n)^σ ≤ x^σ·8/(σ−1)²`.
  The Dirichlet mass factors as `x^σ · ∑'_n Λ(n)n^{-σ}`, and the second factor is the CORPUS-OWNED
  `tsum_vonMangoldt_rpow_neg_le` (`Sieve/ChebyshevSeriesBound.lean`).
- `vonMangoldt_le_log_window : 1 ≤ x → (n:ℝ) ≤ 2x → ‖Λ(n)‖ ≤ log 2x` (from `vonMangoldt_le_log`).

`RHTower/Sieve/PerronErrorTotalChebyshev.lean`
- `perron_error_vonMangoldt_total_le`: for `1 ≤ N`, `1 < σ ≤ 2`, `T > 0`, the WHOLE Perron
  truncation error at `x = N + 1/2` is
  ```
  ≤ (1/(πT log2))·x^σ·8/(σ−1)²  +  (16 log(2x)·x/(πT))·4(1 + log(2N+2)).
  ```
  Far half plus near half, with the tsum split proved by `Summable.tsum_add` and a `split_ifs`
  congruence.

At `σ = 1 + ε/2` and `T = x` this reads `≤ 32 x^{ε/2}/(ε²π log2) + (64/π)log(2x)(1+log(2N+2))` —
polylogarithmic, hence `≪_ε x^{ε}`.  Note this makes `σ₀ = 1 + ε/2` preferable to the classical
`σ₀ = 1 + 1/log x`: it avoids computing `x^{1/log x} = e` altogether.

## The asymptotic layer (2026-08-23)

`RHTower/Sieve/PerronIntegrandContinuity.lean`
- `continuous_perron_integrand_line`: under RH the Perron integrand is continuous along the whole
  line `Re s = σ` for `1/2 < σ < 1` — the hypothesis `norm_vIntegral_perron_le` requires.

`RHTower/Sieve/PowerAbsorbsPolylog.lean`
- `log_pow_isBigO_rpow : 0 < δ → (log y)^k =O[atTop] y^{kδ}` (induction on `k`, using mathlib's
  `isLittleO_log_rpow_atTop`).
- `rpow_mul_log_pow_isBigO : a < b → y^a·(log y)^k =O[atTop] y^b` — choose `δ = (b−a)/(2(k+1))`,
  so `a + kδ ≤ a + (b−a)/2 < b`.

This is the layer that turns the explicit bounds into the card's `O_δ` statement: every term of the
master inequality has the shape `x^a·(log x)^k` with `a ≤ 1/2 + ε/2 < 1/2 + ε`, so the whole bound
is `O(x^{1/2+ε})`, and `x = N + 1/2 ≍ N`.

## CLOSED (2026-08-23)

`VK4` is complete and the consumer card is at stage 3.

`RHTower/Sieve/ChebyshevErrorHalfIntegerBound.lean`
- `exists_chebyshev_error_halfInt_bound`: under RH, for every `ε ∈ (0, 1/4]` there is `C > 0` with
  ```
  |ψ(N) − N| ≤ C·(N+1/2)^{1/2+ε/2}·(1 + log(N+1/2))²   for every N ≥ 7.
  ```
  The instantiation is `σ₁ = 1/2 + ε/2`, `σ₀ = 1 + ε/2`, `T = N + 1/2`.  With that choice each of
  the four terms of the master inequality collapses:
  - Perron far half: `(1/(πT log2))·x^{σ₀}·8/(σ₀−1)²  =  32/(π log2 ε²)·x^{ε/2}` — the height
    cancels a whole power because `T = x`;
  - Perron near half: `(16 log(2x)·x/(πT))·4(1+log(2N+2))  ≤  (192/π)(1+log x)²`;
  - shifted vertical: `(K x^{σ₁})(2(1+log3)/σ₁ + 2(1+log(2+x))log x) ≤ 14K·x^{σ₁}(1+log x)²`;
  - each horizontal: `(C log x/(σ₁−1/2))(x^{σ₀}/x)|σ₀−σ₁| = (C/ε)·log x·x^{ε/2}`.
  Every logarithm is tamed by `log 4 ≤ log x` (valid because `x ≥ 7`), so the only numeric input is
  `Real.log_two_lt_d9`.

`RHTower/Sieve/ChebyshevErrorPowerBound.lean`
- `isBigO_shift_rpow_one_add_log`: `(N+1/2)^a(1+log(N+1/2))^k =O[atTop] N^b` for `a < b`, by
  `1 + log y ≤ 2 log y` past `y = e` and then `ShiftedPolylogTransfer`.
- `chebyshev_error_isBigO_of_riemannHypothesis`, and the explicit forms
  `exists_chebyshev_error_power_bound` (`∀ N ≥ 1`) and
  `exists_chebyshevPsiReal_error_power_bound` (`∀ t ≥ 1`, real variable).
  The step from an eventual `IsBigO` to a bound valid from `1` on is the reusable
  `exists_bound_of_isBigO_natRpow`.

`RHTower/Sieve/DyadicWindowErrorUnderRH.lean`
- `abs_integral_psiWeight_sub_le_power`: the integral term of the Abel identity with a power-law
  error.  The integrand `|ψ(t)−t|/(2t√t)` is `≤ C t^{a−1}/2`, majorised by the CONSTANT
  `C(2X)^a/(2X)` on `[X,2X]`, so the whole integral costs one measure factor `X` — no antitone
  rpow lemma is needed.
- `exists_dyadicSqrtVonMangoldtMass_error_bound`: `|mass(X) − 2(√2−1)√X| ≤ 4C X^a` for `X ≥ 1`.
  The decomposition is exactly `(5)`: two endpoint remainders `(ψ(2X)−2X)/√(2X)`,
  `(ψ(X)−X)/√X`, and the integral remainder.

`RHTower/Sieve/SquareWindowEnergyUnderRH.lean`
- `dyadicSqrtVonMangoldtMass_square_eq`: at `X = m²/2` the dyadic mass IS
  `dyadicWeightedPrimeWindow (m²)` — both floors are exact.
- `sqrt_square_half_centring`: `2(√2−1)√(m²/2) = 2(1−1/√2)m`, the card's constant `c`.
- `exists_squarePrimeWindowCenteredDeviation_bound`: `|W(m²) − c m| ≤ C m^{2a}` for all `m ≥ 1`
  (the aperture `m = 1` is the empty window, `W(1) = 0`, handled separately since `X = 1/2 < 1`).
- `squarePrimeWindowCorrelationEnergySubpower_of_riemannHypothesis` and the equivalence
  `riemannHypothesis_iff_squarePrimeWindowCorrelationEnergySubpower`.  Taking `a = min(δ,1)/4`
  gives `C_M ≤ C²M^{1+4a} ≤ C²M^{1+δ}`.

All declarations audit to `[propext, Classical.choice, Quot.sound]`.
