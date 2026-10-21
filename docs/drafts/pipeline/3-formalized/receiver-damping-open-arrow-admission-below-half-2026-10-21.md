# The receiver damping open arrow: admission of the signed Möbius weight below half damping under a width bound

- **ID:** receiver-damping-open-arrow
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/walls-ledger.md, face 1.8 (the signs); card
  `3-formalized/walls-one-zero-width-dictionary-2026-10-21.md`, round six
- **Statement:** `zetaZeroWidth < ε ⟹ ε ∈ receiverDampings`, i.e. `receiverDampingRate ≤ zetaZeroWidth`;
  with the proved `zetaZeroWidth ≤ receiverDampingRate` this is `receiverDampingRate = zetaZeroWidth`.

## Goal
Face 1.8 proved that the admissible dampings of the damped Möbius receiver read the zero width from
above (`zetaZeroWidth_le_of_accPt_receiverDampings`). The converse arrow is the PM route's open
admission below half damping; at `σ = 0` it is "RH ⟹ the Fermi source is admitted at every damping
`ε > 0`". Closing it makes the receiver damping an exact currency of the width, like the Chebyshev
deficit exponent, and turns the cofinal RH criterion into an equivalence.

## Gates
- [x] 0 → 1  in-progress: well-posed (both sides are Lean objects), attack idea below
- [x] 1 → 2  fully-proven: the sharp arrow is the Mellin–Hardy argument of phase B (below)
- [x] 2 → 3  formalized: phase A `V:LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa`
  (`receiverDampingRate_le_half_zetaZeroAbscissa`); phase B
  `R:TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa` (`isMellinTailHardy_etaZetaQuotient`)
  and `R:AdmissionBelowHalfDampingAboveTheZeroWidth` (`mem_receiverDampings_of_zetaZeroAbscissa_lt`,
  `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `riemannHypothesis_iff_cofinal_budget`); all
  compiled with `lake env lean`, standard axioms
- [ ] 3 → 4  not applicable (no stage 4 for RH work)

## Approach

### Phase A, the elementary partial arrow (Littlewood + rate transfer)
Corpus: `mobiusMertens_subpower_zetaZeroAbscissa` (Littlewood: `|M(N)| ≤ C (N+1)^{Θ+δ}` with
`Θ = zetaZeroAbscissa`, unconditional) and the rate-transfer lemma
`abs_weightCenteredPrefix_dampedSign_le_of_linear` (BVI): if `|M(x)| ≤ L x` for `x ≥ D` then
`|A_ε(n)| ≤ 3 D^{1−ε} + 31 L n D^{−ε}` for `1/4 ≤ ε ≤ 1/2`. With `L = 2C D^{Θ+δ−1}` and
`D ≈ n^{1/(2−Θ−δ)}` this gives `|A_ε(n)| ≤ K n^{(1−ε)/(2−Θ−δ)}`, exponent `< 1/2` iff
`ε > (Θ+δ)/2`. Hence `Ioi (Θ/2) ⊆ receiverDampings` and `receiverDampingRate ≤ Θ/2 = 1/4 +
zetaZeroWidth/2`. Consequences: `receiverDampingRate < 1/2 ↔ zetaZeroAbscissa < 1` (crossing below
half damping is quasi-RH), and under RH admission at every `ε > 1/4`.
Module plan: `BezoutValuationIncidence/LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa.lean`
(BVI chain; cannot import SRT because of the `RHTower.dilationAverage` collision, so
`receiverDampingRate` moves into `RHTower/ReceiverDampingsAccumulateAboveTheZeros`).

### Phase B, the sharp arrow (Burnol's Paley–Wiener identification)
The Fermi source `f_ε = pmPowerDampedFermiSource ε` is supported on `(0, 1]` and
`mellin f_ε s = (1 − 2^{1−s}) ζ(s) / (s ζ(s+ε))` for `1 − ε < Re s < 1`
(`hasMellin_pmPowerDampedFermiSource`). Inversion `g(u) = u^{−1} f_ε(1/u)` turns it into a tail datum
on `(1, ∞)` with `∫_1^∞ u^{−s} g(u) du = mellin f_ε s` and `‖g‖_{L²(1,∞)} = ‖f_ε‖_{L²(0,1)}`.
Obligations, all with corpus tools:
1. `F_ε(s) := (1 − 2^{1−s}) ζ(s)/(s ζ(s+ε))` is holomorphic on `Re s > 1/2` when
   `zetaZeroAbscissa < 1/2 + ε` (pole of `ζ` at `1` removed by the eta factor; `ζ(s+ε) ≠ 0` by
   `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`).
2. Uniform line bounds: `‖ζ(σ+it)‖ ≤ C t^{(1+η−σ)/2}` for `σ ≥ 1/2`, `t ≥ 8`
   (`exists_norm_riemannZeta_le_convexity`); `‖invZeta(s)‖ ≤ K (2+|Im s|)^{η'}` on
   `Θ+δ ≤ Re s ≤ d` (`exists_invZeta_shift_data_of_zeroFree`), trivial bound for `Re s ≥ d`;
   `|1 − 2^{1−s}| ≤ 1 + √2`; `|s|^{−2} ≤ (1/4 + t²)^{−1}`. Hence `∫ |F_ε(σ + it)|² dt ≤ M` uniformly
   in `σ > 1/2`: `IsHalfPlaneHardy (fun w => F_ε (w + 1/2)) M`, i.e. `IsMellinTailHardy 1 F_ε`.
3. `exists_memLp_of_isMellinTailHardy (a := 1)`: a datum `h ∈ L²(1, ∞)` with
   `∫_1^∞ u^{−s} h(u) du = F_ε(s)` for `Re s > 1/2`.
4. Uniqueness: `h = g` a.e. on `(1, ∞)` from equal right Mellin transforms on the strip
   `max(1/2, 1−ε) < Re s < 1` (Laplace/Fourier injectivity on `L¹` after the log chart). Then
   `f_ε ∈ L²(0, 1)`, i.e. `ε ∈ receiverDampings` (`mem_receiverDampings_iff_memLp`).
Conclusion: `Ioi zetaZeroWidth ⊆ receiverDampings`, `receiverDampingRate = zetaZeroWidth`,
`RiemannHypothesis ↔ receiverDampingRate = 0 ↔ AccPt 0 (𝓟 receiverDampings)`.

## Log
- 2026-10-21 — created in 1-in-progress after round six (face 1.8). Corpus searches done for the
  Mellin–Hardy toolkit (`MellinHardyClasses`, `MellinHardyBridge`, `HalfPlaneHardy`,
  `PaleyWienerHalfPlane`), convexity (`ZetaConvexityBound`), reciprocal zeta
  (`InvZetaAbscissaSubpolynomial`), Littlewood (`MobiusMertensAbscissaLittlewood`).
- 2026-10-22 — phase A compiled (Littlewood + rate transfer: `Ioi (Θ/2) ⊆ receiverDampings`,
  `receiverDampingRate ≤ Θ/2`, `receiverDampingRate < ½ ↔ Θ < 1`, RH ⟹ admission above `¼`).
- 2026-10-22 — phase B compiled. B1: `etaSlope := dslope (1 − 2^{1−s}) 1` (entire),
  `etaZetaQuotient ε s := etaSlope s · zetaResidueUnit s · invZeta (s+ε) / s`, line bound
  `‖·‖ ≤ K (1+|Im s|)^{−9/16}` on `Re s ≥ ½` (convexity with `η = 1/8`, `exists_invZeta_shift_data_of_zeroFree`
  with `d = 2` plus `norm_riemannZeta_ge_of_two_le_re`, `|s| ≥ (1+|Im s|)/4`), hence
  `IsMellinTailHardy 1`. B2: `invertedFermiSource ε := 1_{(1,∞)} · u⁻¹ f_ε(u⁻¹)`;
  `mellinTail_invertedFermiSource` by `integral_Ioi_comp_inv` + `ofReal_inv_cpow`;
  `exists_memLp_of_isMellinTailHardy` datum `h`; both `logChart 1` data have the same `laplaceRay` on
  the line `Re w = τ := (max 0 (½−ε) + ½)/2` via `mellinTail_eq_laplaceRay`; `rayDamp` difference has
  zero Fourier transform (`fourierIntegral_rayDamp`), `HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero`
  gives a.e. equality; `memLp_two_logChartInv` + `logChartInv_logChart_one` return to `(1,∞)`;
  the inversion Jacobian (`integrableOn_image_iff_integrableOn_abs_deriv_smul`) returns to `(0,∞)`.
  Result: `receiverDampingRate = zetaZeroAbscissa − ½`, `RiemannHypothesis ↔ receiverDampingRate = 0
  ↔ AccPt 0 (𝓟 receiverDampings) ↔ cofinal budgets`. Moved to 3-formalized.
