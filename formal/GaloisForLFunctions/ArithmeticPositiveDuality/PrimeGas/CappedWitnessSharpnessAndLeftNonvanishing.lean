import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.RankOneOverlapFourthPowerLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.FiniteTests
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.SublinearClock
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.IntrinsicDirichletCutoffMargin

/-!
# Intrinsic dyadic spectral triads, mesoscopic sharpness of the UV-capped zero-bound, and left-strip nonvanishing witnesses

At candidate left-strip parameters `3001 / 24000 ≤ Re s < 1 / 2` above Bohman height `169 / 2 = 84.5`,
we establish the quantitative spectral theory of the UV-capped rank-one nonvanishing test:

1. **Intrinsic dyadic eigenvalue triad continuation and pairwise difference blindness
   (`dyadicSpectralTriad`, `summable_dyadicSpectralTriad`, `tsum_dyadicSpectralTriad_eq`,
   `jointSurvivingPartition_eq_tsum_dyadicSpectralTriad`, `jointSurvivingPartition_sub_eq`)**:
   Every interlacing spectrum `b : SpectralBand r` determines the purely spectral dyadic triad
   `dyadicSpectralTriad b s k = b(2k)^s + b(2k+1)^s - 2^{1-s} b(k)^s`, which is summable across the
   entire right half-plane `Re s > 0` without subtracting `riemannZeta` and sums for `s ≠ 1` to
   `(1 - 2^{1-s}) survivingPartition b s`, yielding an intrinsic eigenvalue-series formula for
   `jointSurvivingPartition b s` throughout `0 < Re s < 1`. By contrast, pairwise differences
   `jointSurvivingPartition b₁ s - jointSurvivingPartition b₂ s` cancel `continued s` identically.

2. **Single-omission certificates at fixed UV cap `Λ` and at sharp exponent `2 / Re s`
   (`uvZeroThresholdFactor`, `exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero`,
   `chordZeroThresholdFactor`, `jointSurviving_chord_bound_of_integral_eq_zero`,
   `exists_chordZeroThreshold_witness_iff_integral_ne_zero`,
   `rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half`,
   `rh_iff_exists_uvRegular_witness_above_eightyFour_and_half`)**:
   For every fixed cap `Λ > 0` and every `0 < Re s < 1`, nonvanishing of the dyadic overlap integral
   is equivalent to the existence of a single conserving rank-one omission `v : MissingWave` within
   `uvRegularRankOne s hs0 Λ` beating `uvZeroThresholdFactor s Λ * lineLoss v.val`. At the sharp
   relative exponent `2 / Re s`, the cap-free chord bound `(‖2^s - 1‖ * ‖s‖ / s.re)^{2 / s.re}` holds
   across all `MissingWave` at every zero and admits a strict single-omission converse.

3. **Mesoscopic phase-coherence saturation and sharpness phase transition at `Re s = 1 / 2`
   (`mesoscopicBlockProfile`, `exists_uvRegularRankOne_exceeding_lt_chordBound_of_re_lt_half`,
   `isLeast_uvRegularRankOne_fourthPower_of_integral_eq_zero`,
   `uvRegularRankOne_saturates_all_caps_iff_re_lt_half`)**:
   On `0 < Re s < 1 / 2`, consecutive interlacing blocks of mesoscopic width
   `⌊c (N + 1)^{(1 + 4 Re s) / 3}⌋₊ = o(N)` freeze imaginary-time phase dispersion at arbitrary
   height `Im s` while saturating the UV cap `R_σ^4 / L → θ Λ`. Consequently, at any hypothetical
   left-strip zero of the dyadic overlap integral, `uvZeroThresholdFactor s Λ` is the **exact least**
   fourth-power bound (`IsLeast`) across `uvRegularRankOne s hs0 Λ`, and linear saturation across all
   `Λ > 0` characterizes `Re s < 1 / 2` within `0 < Re s ≤ 2`.

4. **Sublinear-clock witness loss ceiling and two-sided ground-attenuation depth law
   (`witness_lineLoss_fourth_root_lt_clock_head_tail`, `exists_uvRegular_witness_of_norm_zeta_ge`,
   `groundAttenuation_loss_lt_of_beating_zeroBound`)**:
   Every omission beating `uvZeroThresholdFactor s Λ` obeys the sublinear-clock loss ceiling
   `(Λ · lineLoss v)^{1/4} < (s.re / ‖s‖)(‖ζ(s)‖ + 2N) + (N + 1)^{-s.re}` for all `N : ℕ`, while
   ground-state attenuations `1 - τ^s` beat `uvZeroThresholdFactor s Λ` at small loss if and only if
   `1 - τ^2` scales down to order `‖ζ(s)‖^4 / (Λ (‖s‖ / s.re)^4)`.

5. **Unconditional left-strip nonvanishing and UV-capped witnesses
   (`integral_ne_zero_and_witness_of_left_known_regions`, `moebius_powerSaving_left_strip_witnesses`,
   `ncard_missingLeftCappedWitnessWindow_le`,
   `exists_point_with_left_cappedWitness_of_card_gt`,
   `infinite_left_cappedWitness_on_horizontal_interval`)**:
   Unconditional nonvanishing of the dyadic overlap integral and existence of UV-capped rank-one
   witnesses hold across `0 < Re s < 3001 / 24000` and `|Im s| ≤ 169 / 2`, outside the reflected
   power-saving Möbius exceptional set of measure `O((log U)^5 U^{1 - (1/2 - σ)/5})` above `84.5`,
   and up to `4(1 + h^2)(xiLineTwoLogDerivConstant + log(|τ| + 4))` exceptions in every left-strip
   window `[τ - h, τ + h]`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing

/-! ### Part 1: Intrinsic dyadic eigenvalue triad continuation and pairwise difference blindness -/

private theorem two_cpow_sub_one_ne_zero {s : ℂ} (hs0 : 0 < s.re) :
    (2 : ℂ) ^ s - 1 ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := (ComplementaryHalves.factor_zero_iff s).mp h0
  exact hs0.ne' ((congrArg Complex.re hk).trans (ComplementaryHalves.frequency_re k))

private theorem one_sub_two_cpow_one_sub_ne_zero' {s : ℂ} (hs_re : s.re ≠ 1) :
    1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  intro h0
  have heq : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h0).symm
  have hnorm := congrArg norm heq
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one] at hnorm
  have hexp0 : (1 - s).re = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hlt).ne hnorm
    · exact (Real.one_lt_rpow one_lt_two hgt).ne' hnorm
  rw [Complex.sub_re, Complex.one_re] at hexp0
  exact hs_re (sub_eq_zero.mp hexp0).symm

/-- Purely spectral dyadic eigenvalue triad of an interlacing spectrum `b : SpectralBand r`:
combines the adjacent shell pair `(2k, 2k + 1)` against the dyadically rescaled shell `k` without
referencing `riemannZeta` or `hotEdge`. -/
def dyadicSpectralTriad {r : ℕ} (b : SpectralBand r) (s : ℂ) (k : ℕ) : ℂ :=
  (((b (2 * k)).val : ℂ) ^ s + ((b (2 * k + 1)).val : ℂ) ^ s) -
    (2 : ℂ) ^ (1 - s) * ((b k).val : ℂ) ^ s

private theorem occupationWeight_cpow_eq_neg_cpow (n : ℕ) (s : ℂ) :
    (occupationWeight n : ℂ) ^ s = (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have harg : (((n : ℝ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]
    exact Real.pi_pos.ne
  rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]

private theorem dyadicSpectralTriad_eq_etaTerm_sub_drops {r : ℕ} (b : SpectralBand r) (s : ℂ)
    (k : ℕ) :
    dyadicSpectralTriad b s k =
      _root_.RHTower.etaTerm s k -
        (complexDrop b (2 * k) s + complexDrop b (2 * k + 1) s -
          (2 : ℂ) ^ (1 - s) * complexDrop b k s) := by
  have heven : (occupationWeight (2 * k) : ℂ) ^ s =
      ((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    rw [occupationWeight_cpow_eq_neg_cpow]
    push_cast; ring_nf
  have hodd : (occupationWeight (2 * k + 1) : ℂ) ^ s =
      ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    rw [occupationWeight_cpow_eq_neg_cpow]
    push_cast; ring_nf
  have h2pow : (2 : ℂ) ^ (1 - s) * (occupationWeight k : ℂ) ^ s =
      2 * ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    have hsplit : (2 : ℂ) ^ (1 - s) = (2 : ℂ) * (2 : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
    have hmul : (2 : ℂ) ^ (-s) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
        ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
      have h := (Complex.mul_cpow_ofReal_nonneg zero_le_two
        (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) (-s)).symm
      rw [Complex.ofReal_ofNat] at h
      refine h.trans ?_
      congr 1; push_cast; ring
    rw [occupationWeight_cpow_eq_neg_cpow, hsplit, mul_assoc, hmul]
  unfold dyadicSpectralTriad _root_.RHTower.etaTerm complexDrop
  linear_combination heven + hodd - h2pow

/-- **Uniform right-half-plane summability of the intrinsic dyadic spectral triad:**
for every `r : ℕ`, `b : SpectralBand r`, and `s` with `0 < Re s`, `dyadicSpectralTriad b s` is
summable over `ℕ`. -/
theorem summable_dyadicSpectralTriad {r : ℕ} (b : SpectralBand r) {s : ℂ} (hs0 : 0 < s.re) :
    Summable (dyadicSpectralTriad b s) := by
  have heta : Summable (_root_.RHTower.etaTerm s) := _root_.RHTower.summable_etaTerm s hs0
  have hcd : Summable (fun n : ℕ => complexDrop b n s) := summable_complexDrop b hs0
  have heven : Summable (fun k : ℕ => complexDrop b (2 * k) s) :=
    hcd.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos h
  have hodd : Summable (fun k : ℕ => complexDrop b (2 * k + 1) s) :=
    hcd.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos (Nat.add_right_cancel h)
  have hcomb := heta.sub ((heven.add hodd).sub (hcd.mul_left ((2 : ℂ) ^ (1 - s))))
  exact hcomb.congr fun k => (dyadicSpectralTriad_eq_etaTerm_sub_drops b s k).symm

/-- **Exact intrinsic continuation of `survivingPartition` via the dyadic spectral triad:**
across the entire punctured half-plane `0 < Re s`, `s ≠ 1`, the convergent eigenvalue series
`∑' k, dyadicSpectralTriad b s k` equals `(1 - 2^{1-s}) * survivingPartition b s`. -/
theorem tsum_dyadicSpectralTriad_eq {r : ℕ} (b : SpectralBand r) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    (∑' k : ℕ, dyadicSpectralTriad b s k) =
      (1 - (2 : ℂ) ^ (1 - s)) * survivingPartition b s := by
  let cd : ℕ → ℂ := fun n => complexDrop b n s
  let dropTriad : ℕ → ℂ := fun k =>
    cd (2 * k) + cd (2 * k + 1) - (2 : ℂ) ^ (1 - s) * cd k
  have heta : Summable (_root_.RHTower.etaTerm s) := _root_.RHTower.summable_etaTerm s hs0
  have hcd : Summable cd := summable_complexDrop b hs0
  have heven : Summable (fun k : ℕ => cd (2 * k)) :=
    hcd.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos h
  have hodd : Summable (fun k : ℕ => cd (2 * k + 1)) :=
    hcd.comp_injective fun _ _ h => Nat.mul_left_cancel two_pos (Nat.add_right_cancel h)
  have hpair : Summable (fun k : ℕ => cd (2 * k) + cd (2 * k + 1)) := heven.add hodd
  have hscale : Summable (fun k : ℕ => (2 : ℂ) ^ (1 - s) * cd k) :=
    hcd.mul_left ((2 : ℂ) ^ (1 - s))
  have hdrop_part : Summable dropTriad := hpair.sub hscale
  have hcongr : (∑' k : ℕ, dyadicSpectralTriad b s k) =
      _root_.RHTower.etaPair s - ∑' k : ℕ, dropTriad k := by
    rw [tsum_congr (dyadicSpectralTriad_eq_etaTerm_sub_drops b s),
      Summable.tsum_sub heta hdrop_part]
    rfl
  have heven_odd : (∑' k : ℕ, cd (2 * k)) + (∑' k : ℕ, cd (2 * k + 1)) = ∑' n : ℕ, cd n :=
    tsum_even_add_odd (f := cd) heven hodd
  have hcd_eq : (∑' n : ℕ, cd n) = relativePartition b s := rfl
  have hdrop_tsum : (∑' k : ℕ, dropTriad k) =
      (1 - (2 : ℂ) ^ (1 - s)) * relativePartition b s := by
    dsimp only [dropTriad]
    rw [Summable.tsum_sub hpair hscale, Summable.tsum_add heven hodd, heven_odd,
      tsum_mul_left, hcd_eq]
    ring
  rw [hcongr, _root_.RHTower.etaPair_eq s hs0 hs1, hdrop_tsum, survivingPartition]
  ring

/-- **Intrinsic eigenvalue-series representation of `jointSurvivingPartition` across `0 < Re s < 1`:**
for every `0 < Re s` with `Re s ≠ 1` and every `b : SpectralBand r`, `jointSurvivingPartition b s` is
recovered directly from the surviving spectrum `b` without subtracting `riemannZeta`. -/
theorem jointSurvivingPartition_eq_tsum_dyadicSpectralTriad {r : ℕ} (b : SpectralBand r)
    {s : ℂ} (hs0 : 0 < s.re) (hs_re : s.re ≠ 1) :
    jointSurvivingPartition b s =
      (((2 : ℂ) ^ s - 1) / (1 - (2 : ℂ) ^ (1 - s))) *
        ∑' k : ℕ, dyadicSpectralTriad b s k := by
  have hs1 : s ≠ 1 := fun he => hs_re (by rw [he, Complex.one_re])
  have hden : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := one_sub_two_cpow_one_sub_ne_zero' hs_re
  rw [tsum_dyadicSpectralTriad_eq b hs0 hs1, jointSurvivingPartition]
  field_simp [hden]

/-- **Exact `ζ`-blindness of pairwise differences between conserving omissions:**
for any two interlacing spectra `b₁, b₂ : SpectralBand r`, the difference of their
`jointSurvivingPartition` readings cancels `continued s` identically. -/
theorem jointSurvivingPartition_sub_eq {r : ℕ} (b₁ b₂ : SpectralBand r) (s : ℂ) :
    jointSurvivingPartition b₁ s - jointSurvivingPartition b₂ s =
      -((2 : ℂ) ^ s - 1) * (relativePartition b₁ s - relativePartition b₂ s) := by
  rw [jointSurvivingPartition_eq_continued_sub, jointSurvivingPartition_eq_continued_sub]
  ring

/-! ### Part 2: Single-omission certificates at fixed UV cap `Λ` and at sharp exponent `2 / Re s` -/

/-- Explicit `ζ`-free fourth-power zero-bound coefficient at parameter `s` and UV cap `Λ`:
`‖(2 : ℂ)^s - 1‖^4 * (‖s‖ / s.re)^4 * Λ`. -/
def uvZeroThresholdFactor (s : ℂ) (Λ : ℝ) : ℝ :=
  ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * Λ

/-- **Pointwise single-omission certificate under any fixed UV cap `Λ > 0`:**
across the entire open strip `0 < Re s < 1`, the dyadic overlap integral is nonzero if and only if
there exists at least one conserving rank-one omission `v : MissingWave` within `uvRegularRankOne s hs0 Λ`
whose fourth-power surviving reading strictly exceeds `uvZeroThresholdFactor s Λ * lineLoss v.val`. -/
theorem exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (∃ v : MissingWave, uvRegularRankOne s hs0 Λ v ∧
      uvZeroThresholdFactor s Λ * lineLoss v.val <
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  constructor
  · rintro ⟨v, huv, hgt⟩ hint0
    have hcs : continued s = 0 :=
      (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
    let b := missingWaveSpectrum v
    let β : GibbsExponent := ⟨s.re, hs0⟩
    have hrp := relativePartition_norm_le b β le_rfl
    have hjsp : ‖jointSurvivingPartition b s‖ ≤
        ‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * relativeReading (powerResponse β) b) := by
      rw [jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left hrp (norm_nonneg _)
    have hp4 : ‖jointSurvivingPartition b s‖ ^ 4 ≤
        uvZeroThresholdFactor s Λ * lineLoss v.val := by
      calc ‖jointSurvivingPartition b s‖ ^ 4
          ≤ (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * relativeReading (powerResponse β) b)) ^ 4 :=
            pow_le_pow_left₀ (norm_nonneg _) hjsp 4
        _ = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 *
              relativeReading (powerResponse β) b ^ 4 := by ring
        _ ≤ ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * (Λ * lineLoss v.val) :=
            mul_le_mul_of_nonneg_left huv (by positivity)
        _ = uvZeroThresholdFactor s Λ * lineLoss v.val := by
            unfold uvZeroThresholdFactor; ring
    exact hp4.not_gt hgt
  · intro hne
    by_contra hno
    have hle : ∀ v : MissingWave, uvRegularRankOne s hs0 Λ v →
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤
          uvZeroThresholdFactor s Λ * lineLoss v.val :=
      fun v huv => le_of_not_gt fun hgt => hno ⟨v, huv, hgt⟩
    exact hne ((uvRegularRankOne_fourthPower_iff_integral_eq_zero t j hs0 hs1 hΛ).mp
      ⟨uvZeroThresholdFactor s Λ, hle⟩)

/-- Cap-free chord zero-bound coefficient at the sharp relative trace exponent `2 / s.re`:
`(‖(2 : ℂ)^s - 1‖ * (‖s‖ / s.re))^{2 / s.re}` (polynomial in `‖s‖`, avoiding Gamma's exponential
decay at large height). -/
def chordZeroThresholdFactor (s : ℂ) : ℝ :=
  (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re)) ^ (2 / s.re)

/-- **Cap-free chord bound at exponent `2 / Re s` when the dyadic overlap integral vanishes:**
for `0 < Re s < 1` with `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0`, **every** conserving
rank-one omission `v : MissingWave` (without any UV cap) satisfies
`‖jointSurvivingPartition(missingWaveSpectrum v, s)‖^{2 / Re s} ≤ chordZeroThresholdFactor s * lineLoss v.val`. -/
theorem jointSurviving_chord_bound_of_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0)
    (v : MissingWave) :
    ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re) ≤
      chordZeroThresholdFactor s * lineLoss v.val := by
  have hcs : continued s = 0 :=
    (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
  have hexp_nn : 0 ≤ 2 / s.re := div_nonneg zero_le_two hs0.le
  have hctrl := matched_trace_control 1 hs0 (by linarith : s.re ≤ 2)
    (omitLine v.val) ((missingDimension_one_iff _).mpr ⟨v.val, missingWave_ne_zero v, rfl⟩)
    ((nonzero_line_conserves_iff v.val).mpr v.property).2
  rw [Nat.cast_one, Real.one_rpow, mul_one, traceLoss_omitLine] at hctrl
  change ‖relativePartition (missingWaveSpectrum v) s‖ ^ (2 / s.re) ≤
      (‖s‖ / s.re) ^ (2 / s.re) * lineLoss v.val at hctrl
  rw [jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _), chordZeroThresholdFactor,
    Real.mul_rpow (norm_nonneg _) (div_nonneg (norm_nonneg _) hs0.le), mul_assoc]
  exact mul_le_mul_of_nonneg_left hctrl (by positivity)

/-- **Cap-free single-omission equivalence at the sharp exponent `2 / Re s`:**
for `0 < Re s < 1`, the dyadic overlap integral is nonzero if and only if at least one conserving
rank-one omission `v : MissingWave` beats `chordZeroThresholdFactor s * lineLoss v.val` at power
`2 / Re s`. -/
theorem exists_chordZeroThreshold_witness_iff_integral_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (∃ v : MissingWave,
      chordZeroThresholdFactor s * lineLoss v.val <
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re)) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  constructor
  · rintro ⟨v, hgt⟩ hint0
    exact (jointSurviving_chord_bound_of_integral_eq_zero t j hs0 hs1 hint0 v).not_gt hgt
  · intro hne
    have hcs : continued s ≠ 0 := fun hcs =>
      hne ((continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mpr hcs)
    obtain ⟨P, hd, hc, _, _, hviol⟩ :=
      exists_small_trace_jointSurviving_violation 0 hs0 hcs (div_pos two_pos hs0)
        (chordZeroThresholdFactor s) zero_lt_one
    obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
    let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
    have hspec : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
    rw [hspec, traceLoss_omitLine] at hviol
    exact ⟨v, hviol⟩

/-- **Direct reduction of `RiemannHypothesis` to nonvanishing of the dyadic overlap integral on the
remaining left strip `3001 / 24000 ≤ Re s < 1 / 2` above height `84.5`:** -/
theorem rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  rw [(rh_iff_rankOne_fourthPower_at_left_dyadicOverlap_zeros_above_eightyFour_and_half t j).1]
  refine forall₄_congr fun s hlo hhi _ => ?_
  have hs0 : 0 < s.re := by linarith
  exact rankOne_fourthPower_from_integral_iff_integral_ne_zero t j hs0 hhi

/-- **Direct reduction of `RiemannHypothesis` to one UV-capped rank-one omission beating the
explicit zero-bound per remaining left-strip point above `84.5`:** -/
theorem rh_iff_exists_uvRegular_witness_above_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave),
          uvRegularRankOne s hs0 Λ v ∧
            uvZeroThresholdFactor s Λ * lineLoss v.val <
              ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  rw [rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half t j]
  refine forall₄_congr fun s hlo hhi _ => ?_
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  constructor
  · intro hne
    obtain ⟨v, hv⟩ :=
      (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mpr hne
    exact ⟨hs0, v, hv⟩
  · rintro ⟨_, v, hv⟩
    exact (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mp ⟨v, hv⟩

/-! ### Part 3: Mesoscopic phase-coherence saturation and `IsLeast` sharpness phase transition -/

/-- Consecutive interlacing block profile shifting shells `N, N + 1, …, N + m - 1` to their lower
interlacing endpoints `occupationWeight (k + 1)` while leaving all other shells untouched. -/
def mesoscopicBlockProfile (N m : ℕ) : SpectralBand 1 :=
  finiteProfile ((Finset.range m).map ⟨fun j => N + j, fun _ _ h => Nat.add_left_cancel h⟩)
    (fun k => occupationWeight (k + 1))
    (fun k _ => ⟨le_rfl, occupationWeight_antitone (Nat.le_succ k)⟩)

theorem relativePartition_mesoscopicBlockProfile (N m : ℕ) (z : ℂ) :
    relativePartition (mesoscopicBlockProfile N m) z =
      (occupationWeight N : ℂ) ^ z - (occupationWeight (N + m) : ℂ) ^ z := by
  rw [mesoscopicBlockProfile, finiteProfile_partition, Finset.sum_map]
  have ht := Finset.sum_range_sub' (fun j : ℕ => (occupationWeight (N + j) : ℂ) ^ z) m
  simpa only [Function.Embedding.coeFn_mk, Nat.add_zero, Nat.add_assoc] using ht

theorem relativeReading_power_mesoscopicBlockProfile (N m : ℕ) (β : GibbsExponent) :
    relativeReading (powerResponse β) (mesoscopicBlockProfile N m) =
      occupationWeight N ^ β.val - occupationWeight (N + m) ^ β.val := by
  let F := (Finset.range m).map ⟨fun j => N + j, fun _ _ h => Nat.add_left_cancel h⟩
  change relativeReading (powerResponse β)
    (finiteProfile F (fun k => occupationWeight (k + 1))
      (fun k _ => ⟨le_rfl, occupationWeight_antitone (Nat.le_succ k)⟩)) = _
  unfold relativeReading
  rw [tsum_eq_sum (s := F) (fun k hk => by
    simp only [spectralDrop, finiteProfile, dif_neg hk, hotEdge, sub_self])]
  have hcongr : (∑ k ∈ F, spectralDrop (powerResponse β)
      (finiteProfile F (fun k => occupationWeight (k + 1))
        (fun k _ => ⟨le_rfl, occupationWeight_antitone (Nat.le_succ k)⟩)) k) =
      ∑ k ∈ F, (occupationWeight k ^ β.val - occupationWeight (k + 1) ^ β.val) :=
    Finset.sum_congr rfl fun k hk => by
      simp only [spectralDrop, finiteProfile, dif_pos hk, powerResponse]
  rw [hcongr, Finset.sum_map]
  have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ β.val) m
  simpa only [Function.Embedding.coeFn_mk, Nat.add_zero, Nat.add_assoc] using ht

theorem relativeReading_quadratic_mesoscopicBlockProfile (N m : ℕ) :
    relativeReading quadraticResponse (mesoscopicBlockProfile N m) =
      occupationWeight N ^ 2 - occupationWeight (N + m) ^ 2 := by
  rw [mesoscopicBlockProfile, finiteProfile_quadratic, Finset.sum_map]
  have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ 2) m
  simpa only [Function.Embedding.coeFn_mk, Nat.add_zero, Nat.add_assoc] using ht

private theorem pow_three_mul_div_pow_four {a b c d e : ℝ}
    (he : a / c = e) (hc : c ≠ 0) (hb : 1 - b ^ 2 ≠ 0) :
    e * (1 - b ^ 2) ^ 3 * (d / (1 - b ^ 2)) ^ 4 =
      (a * d ^ 4) / (c * (1 - b ^ 2)) := by
  rw [← he, div_pow]
  field_simp [hc, hb]

/-- **Mesoscopic phase-coherence saturation on `0 < Re s < 1 / 2`:**
at every left-half-plane parameter `0 < Re s < 1 / 2` (independent of imaginary height `Im s`),
every UV cap `Λ > 0`, and every threshold `K < Λ * (‖s‖ / s.re) ^ 4`, there exists a physical
conserving rank-one omission `v : MissingWave` satisfying `uvRegularRankOne s hs0 Λ v` whose pure
relative perturbation `‖relativePartition(missingWaveSpectrum v, s)‖^4` strictly exceeds
`K * lineLoss v.val`. -/
theorem exists_uvRegularRankOne_exceeding_lt_chordBound_of_re_lt_half
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {Λ : ℝ} (hΛ : 0 < Λ)
    {K : ℝ} (hK : K < Λ * (‖s‖ / s.re) ^ 4) :
    ∃ v : MissingWave, uvRegularRankOne s hs0 Λ v ∧
      K * lineLoss v.val < ‖relativePartition (missingWaveSpectrum v) s‖ ^ 4 := by
  have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
  set σ : ℝ := s.re
  have hM_pos : 0 < Λ * (‖s‖ / σ) ^ 4 :=
    mul_pos hΛ (pow_pos (div_pos (norm_pos_iff.mpr hs_ne) hs0) 4)
  set M₀ : ℝ := Λ * (‖s‖ / σ) ^ 4
  set θ : ℝ := (max 0 K + M₀) / (2 * M₀)
  have hmax_lt : max 0 K < M₀ := max_lt hM_pos hK
  have hθ_pos : 0 < θ := div_pos (by linarith [le_max_left (0 : ℝ) K]) (by positivity)
  have hθ_lt1 : θ < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hK_lt_θM : K < θ * M₀ := by
    have hle : K ≤ max 0 K := le_max_right 0 K
    have heq : θ * M₀ = (max 0 K + M₀) / 2 := by
      dsimp only [θ]; field_simp [hM_pos.ne']
    linarith
  set c : ℝ := (2 * θ * Λ / σ ^ 4) ^ (1 / 3 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hc_cube : c ^ 3 = 2 * θ * Λ / σ ^ 4 := by
    dsimp only [c]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity),
      show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  set α : ℝ := (1 + 4 * σ) / 3
  have hα_pos : 0 < α := by dsimp only [α]; linarith
  have hα_lt1 : α < 1 := by dsimp only [α]; linarith
  let y : ℕ → ℝ := fun N => (N : ℝ) + 1
  let m : ℕ → ℕ := fun N => ⌊c * y N ^ α⌋₊
  let x : ℕ → ℝ := fun N => y N / (y N + (m N : ℝ))
  have hy_pos : ∀ N, 0 < y N := fun N => by dsimp only [y]; positivity
  have hy_top : Tendsto y atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hyα_top : Tendsto (fun N => y N ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα_pos).comp hy_top
  have hcyα_top : Tendsto (fun N => c * y N ^ α) atTop atTop :=
    hyα_top.const_mul_atTop hc_pos
  -- Squeeze `m N / y N ^ α → c`.
  have hm_ratio : Tendsto (fun N => (m N : ℝ) / y N ^ α) atTop (𝓝 c) := by
    have hinv0 : Tendsto (fun N => (y N ^ α)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp hyα_top).congr fun _ => rfl
    have hsub : Tendsto (fun N => c - (y N ^ α)⁻¹) atTop (𝓝 c) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := c)).sub hinv0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds (fun N => ?_) (fun N => ?_)
    · have hyα_pos : 0 < y N ^ α := Real.rpow_pos_of_pos (hy_pos N) α
      have hlt : c * y N ^ α - 1 < (m N : ℝ) := by
        linarith [Nat.lt_floor_add_one (c * y N ^ α)]
      calc c - (y N ^ α)⁻¹ = (c * y N ^ α - 1) / y N ^ α := by field_simp [hyα_pos.ne']
        _ ≤ (m N : ℝ) / y N ^ α := div_le_div_of_nonneg_right hlt.le hyα_pos.le
    · have hyα_pos : 0 < y N ^ α := Real.rpow_pos_of_pos (hy_pos N) α
      have hle : (m N : ℝ) ≤ c * y N ^ α :=
        Nat.floor_le (mul_nonneg hc_pos.le (Real.rpow_nonneg (hy_pos N).le α))
      exact (div_le_iff₀ hyα_pos).mpr hle
  -- `m N / y N = (m N / y N ^ α) * y N ^ (α - 1) → 0`.
  have hu_zero : Tendsto (fun N => (m N : ℝ) / y N) atTop (𝓝 0) := by
    have hy_neg : Tendsto (fun N => y N ^ (α - 1)) atTop (𝓝 0) := by
      refine ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)).comp hy_top).congr fun N => ?_
      dsimp only [Function.comp_def]
      congr 1; ring
    have hprod := hm_ratio.mul hy_neg
    rw [mul_zero] at hprod
    refine hprod.congr fun N => ?_
    have hyN := hy_pos N
    calc (m N : ℝ) / y N ^ α * y N ^ (α - 1)
        = (m N : ℝ) * (y N ^ (α - 1) / y N ^ α) := by ring
      _ = (m N : ℝ) * y N ^ ((α - 1) - α) := by rw [← Real.rpow_sub hyN]
      _ = (m N : ℝ) * (y N)⁻¹ := by
          rw [show (α - 1) - α = (-1 : ℝ) by ring, Real.rpow_neg_one]
      _ = (m N : ℝ) / y N := by rw [div_eq_mul_inv]
  -- Hence `x N = 1 / (1 + m N / y N) → 1` strictly from below.
  have hx_lim1 : Tendsto x atTop (𝓝 1) := by
    have hden : Tendsto (fun N => 1 + (m N : ℝ) / y N) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hu_zero
    have hinv : Tendsto (fun N => (1 + (m N : ℝ) / y N)⁻¹) atTop (𝓝 1) := by
      simpa only [inv_one] using hden.inv₀ one_ne_zero
    refine hinv.congr fun N => ?_
    have hyN := hy_pos N
    dsimp only [x]
    field_simp [hyN.ne', (by positivity : (0 : ℝ) < y N + (m N : ℝ)).ne']
  have hm_ge1 : ∀ᶠ N in atTop, 1 ≤ m N := by
    filter_upwards [hcyα_top.eventually_ge_atTop (1 : ℝ)] with N hge
    exact Nat.le_floor (by simpa using hge)
  have hx_mem : ∀ᶠ N in atTop, 0 < x N ∧ x N < 1 := by
    filter_upwards [hm_ge1] with N hm1
    have hyN := hy_pos N
    have hm_pos : (0 : ℝ) < (m N : ℝ) := by exact_mod_cast hm1
    dsimp only [x]
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr (by linarith)⟩
  have hx_nhds : Tendsto x atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx_lim1, hx_mem.mono fun _ h => h.2⟩
  -- Key mesoscopic scale identity: `y N ^ ((2 - 4σ)/3) * (1 - x N ^ 2) → 2 * c`.
  have hscale_lim : Tendsto (fun N => y N ^ ((2 - 4 * σ) / 3) * (1 - x N ^ 2)) atTop (𝓝 (2 * c)) := by
    have h1x : Tendsto (fun N => (1 : ℝ) + x N) atTop (𝓝 2) := by
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hx_lim1
    have hprod := (hm_ratio.mul hx_lim1).mul h1x
    rw [mul_one, mul_comm c 2] at hprod
    refine hprod.congr fun N => ?_
    have hyN := hy_pos N
    have hden_pos : 0 < y N + (m N : ℝ) := by positivity
    have h1mx : 1 - x N = (m N : ℝ) / (y N + (m N : ℝ)) := by
      dsimp only [x]; field_simp [hden_pos.ne']; ring
    have hpow_eq : y N ^ ((2 - 4 * σ) / 3) = (y N ^ α)⁻¹ * y N := by
      calc y N ^ ((2 - 4 * σ) / 3) = y N ^ (-α + 1) := by congr 1; dsimp only [α]; ring
        _ = y N ^ (-α) * y N ^ (1 : ℝ) := Real.rpow_add hyN (-α) 1
        _ = (y N ^ α)⁻¹ * y N := by rw [Real.rpow_neg hyN.le, Real.rpow_one]
    calc (m N : ℝ) / y N ^ α * x N * (1 + x N)
        = ((y N ^ α)⁻¹ * y N) * ((m N : ℝ) / (y N + (m N : ℝ)) * (1 + x N)) := by
          dsimp only [x]; field_simp [hyN.ne', hden_pos.ne', (Real.rpow_pos_of_pos hyN α).ne']
      _ = y N ^ ((2 - 4 * σ) / 3) * ((1 - x N) * (1 + x N)) := by rw [← hpow_eq, ← h1mx]
      _ = y N ^ ((2 - 4 * σ) / 3) * (1 - x N ^ 2) := by ring
  have hcube_lim : Tendsto (fun N => y N ^ (2 - 4 * σ) * (1 - x N ^ 2) ^ 3) atTop
      (𝓝 ((2 * c) ^ 3)) := by
    refine (hscale_lim.pow 3).congr fun N => ?_
    have hyN := hy_pos N
    rw [mul_pow, ← Real.rpow_natCast (y N ^ ((2 - 4 * σ) / 3)) 3, ← Real.rpow_mul hyN.le]
    congr 2; ring
  -- Compose with `ground_chord_slope` at `s` and at `(σ : ℂ)`.
  have hsl_s : Tendsto (fun N => (‖1 - (x N : ℂ) ^ s‖ / (1 - x N ^ 2)) ^ 4) atTop
      (𝓝 ((‖s‖ / 2) ^ 4)) := ((ground_chord_slope hs0).comp hx_nhds).pow 4
  have hsl_r : Tendsto (fun N => ((1 - x N ^ σ) / (1 - x N ^ 2)) ^ 4) atTop
      (𝓝 ((σ / 2) ^ 4)) := by
    have h := ((ground_chord_slope (z := (σ : ℂ)) (by simpa [σ] using hs0)).comp hx_nhds).pow 4
    simp only [Complex.norm_real, Real.norm_of_nonneg hs0.le] at h
    refine h.congr' ?_
    filter_upwards [hx_mem] with N hxN
    have hp : 0 ≤ 1 - x N ^ σ := sub_nonneg.mpr (Real.rpow_le_one hxN.1.le hxN.2.le hs0.le)
    dsimp only [Function.comp_def]
    rw [← Complex.ofReal_cpow hxN.1.le, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg hp]
  let β : GibbsExponent := ⟨σ, hs0⟩
  have huv_lim : Tendsto (fun N =>
      relativeReading (powerResponse β) (mesoscopicBlockProfile N (m N)) ^ 4 /
        relativeReading quadraticResponse (mesoscopicBlockProfile N (m N))) atTop (𝓝 (θ * Λ)) := by
    have hmul := hcube_lim.mul hsl_r
    have hval : (2 * c) ^ 3 * (σ / 2) ^ 4 = θ * Λ := by
      calc (2 * c) ^ 3 * (σ / 2) ^ 4 = 8 * c ^ 3 * (σ ^ 4 / 16) := by ring
        _ = 8 * (2 * θ * Λ / σ ^ 4) * (σ ^ 4 / 16) := by rw [hc_cube]
        _ = θ * Λ := by field_simp [hs0.ne']; ring
    rw [hval] at hmul
    refine hmul.congr' ?_
    filter_upwards [hx_mem] with N hxN
    have hyN := hy_pos N
    have hd_pos : 0 < 1 - x N ^ 2 := by nlinarith [hxN.1, hxN.2]
    have hocc_N : occupationWeight N = (y N)⁻¹ := by simp [occupationWeight_eq, y]
    have hocc_Nm : occupationWeight (N + m N) = (y N)⁻¹ * x N := by
      have hden_pos : 0 < y N + (m N : ℝ) := by positivity
      rw [occupationWeight_eq]
      dsimp only [y, x]
      push_cast
      field_simp [hyN.ne', hden_pos.ne']
      ring
    rw [relativeReading_power_mesoscopicBlockProfile,
      relativeReading_quadratic_mesoscopicBlockProfile]
    dsimp only [β]
    rw [hocc_N, hocc_Nm, Real.mul_rpow (inv_nonneg.mpr hyN.le) hxN.1.le, mul_pow]
    have hr1 : ((y N)⁻¹ ^ σ - (y N)⁻¹ ^ σ * x N ^ σ) ^ 4 =
        y N ^ (-4 * σ) * (1 - x N ^ σ) ^ 4 := by
      have hsub : (y N)⁻¹ ^ σ - (y N)⁻¹ ^ σ * x N ^ σ = (y N)⁻¹ ^ σ * (1 - x N ^ σ) := by ring
      rw [hsub, mul_pow, Real.inv_rpow hyN.le, ← Real.rpow_neg hyN.le,
        ← Real.rpow_natCast _ 4, ← Real.rpow_mul hyN.le]
      congr 2; ring
    have hr2 : (y N)⁻¹ ^ 2 - (y N)⁻¹ ^ 2 * x N ^ 2 = y N ^ (-2 : ℝ) * (1 - x N ^ 2) := by
      have hsub : (y N)⁻¹ ^ 2 - (y N)⁻¹ ^ 2 * x N ^ 2 = (y N)⁻¹ ^ 2 * (1 - x N ^ 2) := by ring
      rw [hsub, inv_pow, ← Real.rpow_two, ← Real.rpow_neg hyN.le]
    rw [hr1, hr2]
    have hy_comb : y N ^ (-4 * σ) / y N ^ (-2 : ℝ) = y N ^ (2 - 4 * σ) := by
      rw [← Real.rpow_sub hyN]; congr 1; ring
    have hy2_ne : y N ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hyN _).ne'
    exact pow_three_mul_div_pow_four hy_comb hy2_ne hd_pos.ne'
  have hpart_lim : Tendsto (fun N =>
      ‖relativePartition (mesoscopicBlockProfile N (m N)) s‖ ^ 4 /
        relativeReading quadraticResponse (mesoscopicBlockProfile N (m N))) atTop
      (𝓝 (θ * M₀)) := by
    have hmul := hcube_lim.mul hsl_s
    have hval : (2 * c) ^ 3 * (‖s‖ / 2) ^ 4 = θ * M₀ := by
      dsimp only [M₀]
      calc (2 * c) ^ 3 * (‖s‖ / 2) ^ 4 = 8 * c ^ 3 * (‖s‖ ^ 4 / 16) := by ring
        _ = 8 * (2 * θ * Λ / σ ^ 4) * (‖s‖ ^ 4 / 16) := by rw [hc_cube]
        _ = θ * (Λ * (‖s‖ / σ) ^ 4) := by field_simp [hs0.ne']; ring
    rw [hval] at hmul
    refine hmul.congr' ?_
    filter_upwards [hx_mem] with N hxN
    have hyN := hy_pos N
    have hd_pos : 0 < 1 - x N ^ 2 := by nlinarith [hxN.1, hxN.2]
    have hocc_N : occupationWeight N = (y N)⁻¹ := by simp [occupationWeight_eq, y]
    have hocc_Nm : occupationWeight (N + m N) = (y N)⁻¹ * x N := by
      have hden_pos : 0 < y N + (m N : ℝ) := by positivity
      rw [occupationWeight_eq]
      dsimp only [y, x]
      push_cast
      field_simp [hyN.ne', hden_pos.ne']
      ring
    rw [relativePartition_mesoscopicBlockProfile,
      relativeReading_quadratic_mesoscopicBlockProfile, hocc_N, hocc_Nm]
    have hc_mul : (((y N)⁻¹ * x N : ℝ) : ℂ) ^ s = (((y N)⁻¹ : ℝ) : ℂ) ^ s * (x N : ℂ) ^ s := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hyN.le) hxN.1.le]
    have hnorm_num : ‖(((y N)⁻¹ : ℝ) : ℂ) ^ s - (((y N)⁻¹ * x N : ℝ) : ℂ) ^ s‖ ^ 4 =
        y N ^ (-4 * σ) * ‖1 - (x N : ℂ) ^ s‖ ^ 4 := by
      rw [hc_mul, ← mul_one_sub, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hyN), mul_pow,
        Real.inv_rpow hyN.le, ← Real.rpow_neg hyN.le, ← Real.rpow_natCast _ 4,
        ← Real.rpow_mul hyN.le]
      congr 2; dsimp only [σ]; ring
    have hr2 : (y N)⁻¹ ^ 2 - ((y N)⁻¹ * x N) ^ 2 = y N ^ (-2 : ℝ) * (1 - x N ^ 2) := by
      rw [mul_pow, ← mul_one_sub, inv_pow, ← Real.rpow_two, ← Real.rpow_neg hyN.le]
    rw [hnorm_num, hr2]
    have hy_comb : y N ^ (-4 * σ) / y N ^ (-2 : ℝ) = y N ^ (2 - 4 * σ) := by
      rw [← Real.rpow_sub hyN]; congr 1; ring
    have hy2_ne : y N ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hyN _).ne'
    exact pow_three_mul_div_pow_four hy_comb hy2_ne hd_pos.ne'
  have hθΛ_lt : θ * Λ < Λ := by nlinarith [hθ_lt1, hΛ]
  obtain ⟨N, hxN, huv_N, hpart_N⟩ :=
    (hx_mem.and ((huv_lim.eventually (gt_mem_nhds hθΛ_lt)).and
      (hpart_lim.eventually (lt_mem_nhds hK_lt_θM)))).exists
  let b₀ := mesoscopicBlockProfile N (m N)
  have hq_pos : 0 < relativeReading quadraticResponse b₀ := by
    have hyN := hy_pos N
    have hd_pos : 0 < 1 - x N ^ 2 := by nlinarith [hxN.1, hxN.2]
    have hocc_N : occupationWeight N = (y N)⁻¹ := by simp [occupationWeight_eq, y]
    have hocc_Nm : occupationWeight (N + m N) = (y N)⁻¹ * x N := by
      have hden_pos : 0 < y N + (m N : ℝ) := by positivity
      rw [occupationWeight_eq]; dsimp only [y, x]; push_cast
      field_simp [hyN.ne', hden_pos.ne']; ring
    rw [show b₀ = mesoscopicBlockProfile N (m N) from rfl,
      relativeReading_quadratic_mesoscopicBlockProfile, hocc_N, hocc_Nm, mul_pow, ← mul_one_sub]
    positivity
  have hb₀_uv : relativeReading (powerResponse β) b₀ ^ 4 <
      Λ * relativeReading quadraticResponse b₀ := (div_lt_iff₀ hq_pos).mp huv_N
  have hb₀_viol : K * relativeReading quadraticResponse b₀ <
      ‖relativePartition b₀ s‖ ^ 4 := (lt_div_iff₀ hq_pos).mp hpart_N
  let U : Set (SpectralBand 1) :=
    {b | relativeReading (powerResponse β) b ^ 4 < Λ * relativeReading quadraticResponse b ∧
      K * relativeReading quadraticResponse b < ‖relativePartition b s‖ ^ 4}
  have hU_open : IsOpen U :=
    (isOpen_lt ((continuous_relativeReading (powerResponse β) 1).pow 4)
      (continuous_const.mul (continuous_relativeReading quadraticResponse 1))).inter
    (isOpen_lt (continuous_const.mul (continuous_relativeReading quadraticResponse 1))
      ((continuous_relativePartition_spectrum hs0 1).norm.pow 4))
  have hb₀_cl : b₀ ∈ closure (physicalSpectra 1) := by
    rw [closure_rank_one_spectra]; exact mem_univ b₀
  obtain ⟨_, hb_U, ⟨P, hd, hc, rfl⟩⟩ :=
    mem_closure_iff.mp hb₀_cl U hU_open ⟨hb₀_uv, hb₀_viol⟩
  obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
  let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
  have hspec : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
  rw [hspec] at hb_U
  refine ⟨v, ?_, ?_⟩
  · unfold uvRegularRankOne
    rw [← relativeReading_quadratic_missingWaveSpectrum]
    exact hb_U.1.le
  · rw [← relativeReading_quadratic_missingWaveSpectrum]
    exact hb_U.2

/-- **Exact `IsLeast` optimality of `uvZeroThresholdFactor s Λ` at any left-strip zero:**
whenever `0 < Re s < 1 / 2` and `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0`,
`uvZeroThresholdFactor s Λ` is the **exact least** fourth-power constant controlling
`‖jointSurvivingPartition(missingWaveSpectrum v, s)‖^4` across `uvRegularRankOne s hs0 Λ`
(high-ordinate oscillation does not reduce the zero-bound by any positive amount). -/
theorem isLeast_uvRegularRankOne_fourthPower_of_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0) :
    IsLeast {K : ℝ | ∀ v : MissingWave, uvRegularRankOne s hs0 Λ v →
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val}
      (uvZeroThresholdFactor s Λ) := by
  have hs1 : s.re < 1 := by linarith
  have hcs : continued s = 0 :=
    (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
  refine ⟨fun v huv => ?_, fun K hK => ?_⟩
  · by_contra! hgt
    exact ((exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mp
      ⟨v, huv, hgt⟩) hint0
  · by_contra! hlt
    have hf4_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ ^ 4 := pow_pos (norm_pos_iff.mpr (two_cpow_sub_one_ne_zero hs0)) 4
    have hdiv_lt : K / ‖(2 : ℂ) ^ s - 1‖ ^ 4 < Λ * (‖s‖ / s.re) ^ 4 := by
      rw [div_lt_iff₀' hf4_pos]
      unfold uvZeroThresholdFactor at hlt
      linarith
    obtain ⟨v, huv, hviol⟩ :=
      exists_uvRegularRankOne_exceeding_lt_chordBound_of_re_lt_half hs0 hhi hΛ hdiv_lt
    have hjsp : ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 =
        ‖(2 : ℂ) ^ s - 1‖ ^ 4 * ‖relativePartition (missingWaveSpectrum v) s‖ ^ 4 := by
      rw [jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul, mul_pow]
    rw [div_mul_eq_mul_div, div_lt_iff₀' hf4_pos, ← hjsp] at hviol
    exact (hK v huv).not_gt hviol

/-- **Sharpness phase transition at the critical line `Re s = 1 / 2`:**
within `0 < Re s ≤ 2`, the UV-capped fourth-power relative trace constant equals `Λ * (‖s‖ / Re s)^4`
for **every** `Λ > 0` if and only if `Re s < 1 / 2`. -/
theorem uvRegularRankOne_saturates_all_caps_iff_re_lt_half
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re ≤ 2) :
    (∀ Λ : ℝ, 0 < Λ →
      IsLeast {K : ℝ | ∀ v : MissingWave, uvRegularRankOne s hs0 Λ v →
        ‖relativePartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val}
        (Λ * (‖s‖ / s.re) ^ 4)) ↔
      s.re < 1 / 2 := by
  constructor
  · intro hall
    by_contra! hge
    have h2 := hall 2 two_pos
    have h1_mem : (‖s‖ / s.re) ^ 4 ∈
        {K : ℝ | ∀ v : MissingWave, uvRegularRankOne s hs0 2 v →
          ‖relativePartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val} := by
      intro v _
      let b := missingWaveSpectrum v
      let β : GibbsExponent := ⟨s.re, hs0⟩
      have hrp := pow_le_pow_left₀ (norm_nonneg _) (relativePartition_norm_le b β le_rfl) 4
      have huv1 : relativeReading (powerResponse β) b ^ 4 ≤ lineLoss v.val := by
        simpa only [uvRegularRankOne, one_mul] using uvRegularRankOne_of_half_le_re hs0 hge hhi v
      calc ‖relativePartition b s‖ ^ 4
          ≤ ((‖s‖ / s.re) * relativeReading (powerResponse β) b) ^ 4 := hrp
        _ = (‖s‖ / s.re) ^ 4 * relativeReading (powerResponse β) b ^ 4 := by ring
        _ ≤ (‖s‖ / s.re) ^ 4 * lineLoss v.val := mul_le_mul_of_nonneg_left huv1 (by positivity)
    have hle := h2.2 h1_mem
    have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
    have hpos : 0 < (‖s‖ / s.re) ^ 4 := pow_pos (div_pos (norm_pos_iff.mpr hs_ne) hs0) 4
    linarith
  · intro hlt Λ hΛ
    refine ⟨fun v huv => ?_, fun K hK => ?_⟩
    · let b := missingWaveSpectrum v
      let β : GibbsExponent := ⟨s.re, hs0⟩
      have hrp := pow_le_pow_left₀ (norm_nonneg _) (relativePartition_norm_le b β le_rfl) 4
      calc ‖relativePartition b s‖ ^ 4
          ≤ ((‖s‖ / s.re) * relativeReading (powerResponse β) b) ^ 4 := hrp
        _ = (‖s‖ / s.re) ^ 4 * relativeReading (powerResponse β) b ^ 4 := by ring
        _ ≤ (‖s‖ / s.re) ^ 4 * (Λ * lineLoss v.val) :=
            mul_le_mul_of_nonneg_left huv (by positivity)
        _ = (Λ * (‖s‖ / s.re) ^ 4) * lineLoss v.val := by ring
    · by_contra! hlt_K
      obtain ⟨v, huv, hviol⟩ :=
        exists_uvRegularRankOne_exceeding_lt_chordBound_of_re_lt_half hs0 hlt hΛ hlt_K
      exact (hK v huv).not_gt hviol

/-! ### Part 4: Sublinear-clock witness loss ceiling and two-sided ground-attenuation depth law -/

private theorem jointSurvivingPartition_norm_eq_factor_mul {r : ℕ} (b : SpectralBand r)
    (s : ℂ) :
    ‖jointSurvivingPartition b s‖ =
      ‖(2 : ℂ) ^ s - 1‖ * ‖riemannZeta s - relativePartition b s‖ := by
  rw [jointSurvivingPartition, survivingPartition, norm_mul]

/-- **Universal sublinear-clock loss ceiling for any rank-one omission beating `uvZeroThresholdFactor`:**
whenever `0 < Re s < 1`, `Λ > 0`, and `v : MissingWave` beats `uvZeroThresholdFactor s Λ * lineLoss v.val`,
its fourth-trace loss obeys `(Λ * lineLoss v.val)^{1/4} < (s.re / ‖s‖)(‖ζ(s)‖ + 2N) + (N + 1)^{-s.re}`
for **every** cutoff `N : ℕ`. -/
theorem witness_lineLoss_fourth_root_lt_clock_head_tail
    {s : ℂ} (hs0 : 0 < s.re) (_hs1 : s.re < 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (v : MissingWave)
    (hgt : uvZeroThresholdFactor s Λ * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4) (N : ℕ) :
    (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) <
      (s.re / ‖s‖) * (‖riemannZeta s‖ + 2 * (N : ℝ)) + occupationWeight N ^ s.re := by
  have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
  have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ := norm_pos_iff.mpr (two_cpow_sub_one_ne_zero hs0)
  have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs_ne
  have hratio_pos : 0 < ‖s‖ / s.re := div_pos hnorm_pos hs0
  have hL_pos : 0 < Λ * lineLoss v.val := mul_pos hΛ (line_loss_bounds v).1
  set r4 : ℝ := (Λ * lineLoss v.val) ^ (1 / 4 : ℝ)
  have hr4_pow : r4 ^ 4 = Λ * lineLoss v.val := by
    dsimp only [r4]
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hL_pos.le,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hlhs_eq : (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) * r4) ^ 4 =
      uvZeroThresholdFactor s Λ * lineLoss v.val := by
    rw [mul_pow, mul_pow, hr4_pow, uvZeroThresholdFactor]; ring
  rw [← hlhs_eq] at hgt
  have h1 : ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / s.re) * r4 <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
    by_contra! hle
    exact hgt.not_ge (pow_le_pow_left₀ (norm_nonneg _) hle 4)
  rw [jointSurvivingPartition_norm_eq_factor_mul _ s, mul_assoc] at h1
  have h2 : (‖s‖ / s.re) * r4 < ‖riemannZeta s - relativePartition (missingWaveSpectrum v) s‖ :=
    lt_of_mul_lt_mul_left h1 hf_pos.le
  have h3 : ‖riemannZeta s - relativePartition (missingWaveSpectrum v) s‖ ≤
      ‖riemannZeta s‖ + 2 * (N : ℝ) + (‖s‖ / s.re) * occupationWeight N ^ s.re := by
    have htri := norm_sub_le (riemannZeta s) (relativePartition (missingWaveSpectrum v) s)
    have hht := clock_partition_head_tail (missingWaveSpectrum v) hs0 N
    rw [Nat.cast_one, one_mul] at hht
    linarith
  have h4 : (‖s‖ / s.re) * r4 <
      ‖riemannZeta s‖ + 2 * (N : ℝ) + (‖s‖ / s.re) * occupationWeight N ^ s.re := h2.trans_le h3
  have h5 := (lt_div_iff₀' hratio_pos).mpr h4
  calc r4 < (‖riemannZeta s‖ + 2 * (N : ℝ) + (‖s‖ / s.re) * occupationWeight N ^ s.re) /
        (‖s‖ / s.re) := h5
    _ = (s.re / ‖s‖) * (‖riemannZeta s‖ + 2 * (N : ℝ)) + occupationWeight N ^ s.re := by
        field_simp [hnorm_pos.ne', hs0.ne']

/-- **Quantitative constructive ground-attenuation witness scale from a `|ζ(s)|` lower bound:**
whenever `0 < Re s < 1`, `Λ > 0`, and `0 < μ ≤ ‖ζ(s)‖`, every target loss `δ` satisfying
`0 < δ < 1`, `δ^3 < Λ`, and `16 * Λ * (‖s‖ / s.re)^4 * δ < μ^4` produces a physical conserving
rank-one omission `v : MissingWave` within any `ε > 0` of `lineLoss v.val = δ` that satisfies
`uvRegularRankOne s hs0 Λ v` and strictly beats `uvZeroThresholdFactor s Λ * lineLoss v.val`. -/
theorem exists_uvRegular_witness_of_norm_zeta_ge
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {Λ μ δ ε : ℝ}
    (hΛ : 0 < Λ) (hμ : 0 < μ) (hζ : μ ≤ ‖riemannZeta s‖)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδ_uv : δ ^ 3 < Λ)
    (hδ_marg : 16 * Λ * (‖s‖ / s.re) ^ 4 * δ < μ ^ 4) (hε : 0 < ε) :
    ∃ v : MissingWave,
      |lineLoss v.val - δ| < ε ∧
      uvRegularRankOne s hs0 Λ v ∧
      uvZeroThresholdFactor s Λ * lineLoss v.val <
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ := norm_pos_iff.mpr (two_cpow_sub_one_ne_zero hs0)
  have hratio_pos : 0 < ‖s‖ / s.re := div_pos (norm_pos_iff.mpr hs_ne) hs0
  set τ : ℝ := Real.sqrt (1 - δ)
  have h1mδ : 0 < 1 - δ := by linarith
  have hτ_pos : 0 < τ := Real.sqrt_pos.mpr h1mδ
  have hτ_sq : τ ^ 2 = 1 - δ := Real.sq_sqrt h1mδ.le
  have hτ_lt1 : τ < 1 := by
    have hsq : τ ^ 2 < 1 ^ 2 := by rw [hτ_sq]; linarith
    exact (sq_lt_sq₀ hτ_pos.le zero_le_one).mp hsq
  have h1mτ2 : 1 - τ ^ 2 = δ := by linarith
  obtain ⟨b₀, hb₀_cl, hb₀_eq⟩ := exists_ground_attenuation 0 ⟨τ, hτ_pos, hτ_lt1.le⟩
  let β : GibbsExponent := ⟨s.re, hs0⟩
  have hb₀_q : relativeReading quadraticResponse b₀ = δ := by
    have h := hb₀_eq (z := 2) (by norm_num)
    rw [partition_at_two, show (τ : ℂ) ^ (2 : ℂ) = ((τ ^ 2 : ℝ) : ℂ) by
      rw [Complex.ofReal_pow, ← Complex.cpow_natCast]; rfl,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, h1mτ2] at h
    exact Complex.ofReal_injective h
  have hb₀_β : relativeReading (powerResponse β) b₀ = 1 - τ ^ s.re := by
    have h := hb₀_eq (z := (s.re : ℂ)) (by simpa using hs0)
    have hrp := relativePartition_real b₀ β
    dsimp only [β] at hrp
    rw [hrp, ← Complex.ofReal_cpow hτ_pos.le, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
    exact Complex.ofReal_injective h
  have hb₀_β_le_δ : relativeReading (powerResponse β) b₀ ≤ δ := by
    rw [hb₀_β, ← h1mτ2]
    have hle : τ ^ (2 : ℝ) ≤ τ ^ s.re :=
      Real.rpow_le_rpow_of_exponent_ge hτ_pos hτ_lt1.le (by linarith)
    rw [Real.rpow_two] at hle
    linarith
  have hb₀_uv : relativeReading (powerResponse β) b₀ ^ 4 <
      Λ * relativeReading quadraticResponse b₀ := by
    have hp4 : relativeReading (powerResponse β) b₀ ^ 4 ≤ δ ^ 4 :=
      pow_le_pow_left₀ (relativeReading_bounds (powerResponse β) b₀).1 hb₀_β_le_δ 4
    have hd4 : δ ^ 4 < Λ * δ := by
      calc δ ^ 4 = δ ^ 3 * δ := by ring
        _ < Λ * δ := mul_lt_mul_of_pos_right hδ_uv hδ0
    rw [hb₀_q]
    exact hp4.trans_lt hd4
  set r4 : ℝ := (Λ * δ) ^ (1 / 4 : ℝ)
  have hΛδ_pos : 0 < Λ * δ := mul_pos hΛ hδ0
  have hr4_pos : 0 < r4 := Real.rpow_pos_of_pos hΛδ_pos _
  have hr4_pow : r4 ^ 4 = Λ * δ := by
    dsimp only [r4]
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hΛδ_pos.le,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hδ_lt_r4 : δ < r4 := by
    by_contra! hle
    have hp := pow_le_pow_left₀ hr4_pos.le hle 4
    rw [hr4_pow] at hp
    have hd4 : δ ^ 4 < Λ * δ := by
      calc δ ^ 4 = δ ^ 3 * δ := by ring
        _ < Λ * δ := mul_lt_mul_of_pos_right hδ_uv hδ0
    exact hd4.not_ge hp
  have hterm_lt : 2 * (‖s‖ / s.re) * r4 < μ := by
    by_contra! hle
    have hp := pow_le_pow_left₀ hμ.le hle 4
    have heq : (2 * (‖s‖ / s.re) * r4) ^ 4 = 16 * Λ * (‖s‖ / s.re) ^ 4 * δ := by
      calc (2 * (‖s‖ / s.re) * r4) ^ 4 = 16 * (‖s‖ / s.re) ^ 4 * r4 ^ 4 := by ring
        _ = 16 * (‖s‖ / s.re) ^ 4 * (Λ * δ) := by rw [hr4_pow]
        _ = 16 * Λ * (‖s‖ / s.re) ^ 4 * δ := by ring
    rw [heq] at hp
    exact hδ_marg.not_ge hp
  have hrp_b₀ : ‖relativePartition b₀ s‖ ≤ (‖s‖ / s.re) * δ :=
    (relativePartition_norm_le b₀ β le_rfl).trans
      (mul_le_mul_of_nonneg_left hb₀_β_le_δ hratio_pos.le)
  have hdiff_gt : (‖s‖ / s.re) * r4 < ‖riemannZeta s - relativePartition b₀ s‖ := by
    have hδ_mul : (‖s‖ / s.re) * δ < (‖s‖ / s.re) * r4 :=
      mul_lt_mul_of_pos_left hδ_lt_r4 hratio_pos
    linarith [norm_sub_norm_le (riemannZeta s) (relativePartition b₀ s)]
  have hb₀_viol : uvZeroThresholdFactor s Λ * relativeReading quadraticResponse b₀ <
      ‖jointSurvivingPartition b₀ s‖ ^ 4 := by
    rw [hb₀_q, jointSurvivingPartition_norm_eq_factor_mul b₀ s]
    have hmul_gt : ‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4) <
        ‖(2 : ℂ) ^ s - 1‖ * ‖riemannZeta s - relativePartition b₀ s‖ :=
      mul_lt_mul_of_pos_left hdiff_gt hf_pos
    have hp4 := pow_lt_pow_left₀ hmul_gt (by positivity) (by norm_num : 4 ≠ 0)
    have hlhs : (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4)) ^ 4 = uvZeroThresholdFactor s Λ * δ := by
      calc (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4)) ^ 4
          = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * r4 ^ 4 := by ring
        _ = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * (Λ * δ) := by rw [hr4_pow]
        _ = uvZeroThresholdFactor s Λ * δ := by unfold uvZeroThresholdFactor; ring
    rwa [hlhs] at hp4
  have hcont_jsp4 : Continuous (fun b : SpectralBand 1 => ‖jointSurvivingPartition b s‖ ^ 4) := by
    have hc1 : Continuous (fun b : SpectralBand 1 => jointSurvivingPartition b s) := by
      simp_rw [jointSurvivingPartition_eq_continued_sub]
      exact Continuous.sub continuous_const (continuous_const.mul
        (continuous_relativePartition_spectrum hs0 1))
    exact hc1.norm.pow 4
  let U : Set (SpectralBand 1) :=
    {b | |relativeReading quadraticResponse b - δ| < ε ∧
      relativeReading (powerResponse β) b ^ 4 < Λ * relativeReading quadraticResponse b ∧
      uvZeroThresholdFactor s Λ * relativeReading quadraticResponse b <
        ‖jointSurvivingPartition b s‖ ^ 4}
  have hU_open : IsOpen U :=
    (isOpen_lt (((continuous_relativeReading quadraticResponse 1).sub continuous_const).abs)
      continuous_const).inter
    ((isOpen_lt ((continuous_relativeReading (powerResponse β) 1).pow 4)
      (continuous_const.mul (continuous_relativeReading quadraticResponse 1))).inter
    (isOpen_lt (continuous_const.mul (continuous_relativeReading quadraticResponse 1))
      hcont_jsp4))
  have hb₀_in_U : b₀ ∈ U := by
    refine ⟨?_, hb₀_uv, hb₀_viol⟩
    rw [hb₀_q, sub_self, abs_zero]
    exact hε
  obtain ⟨_, hb_U, ⟨P, hd, hc, rfl⟩⟩ :=
    mem_closure_iff.mp hb₀_cl U hU_open hb₀_in_U
  obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
  let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
  have hspec : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
  rw [hspec] at hb_U
  rw [Set.mem_setOf_eq, relativeReading_quadratic_missingWaveSpectrum] at hb_U
  exact ⟨v, hb_U.1, hb_U.2.1.le, hb_U.2.2⟩

/-- **Converse `|ζ(s)|^4` attenuation bottleneck for ground-state witnesses:**
for any ground-mode attenuation `b₀ : SpectralBand 1` with `relativePartition b₀ z = 1 - τ^z`
(`0 < τ < 1`) in the regime `16 * (1 - τ^2)^3 ≤ Λ`, beating the zero-bound
`uvZeroThresholdFactor s Λ * (1 - τ^2)` forces `1 - τ^2 < 16 * ‖ζ(s)‖^4 / (Λ * (‖s‖ / s.re)^4)`. -/
theorem groundAttenuation_loss_lt_of_beating_zeroBound
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {Λ τ : ℝ} (hΛ : 0 < Λ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (b₀ : SpectralBand 1)
    (hb₀ : ∀ {z : ℂ}, 0 < z.re → relativePartition b₀ z = 1 - (τ : ℂ) ^ z)
    (hsmall : 16 * (1 - τ ^ 2) ^ 3 ≤ Λ)
    (hgt : uvZeroThresholdFactor s Λ * (1 - τ ^ 2) < ‖jointSurvivingPartition b₀ s‖ ^ 4) :
    1 - τ ^ 2 < 16 * ‖riemannZeta s‖ ^ 4 / (Λ * (‖s‖ / s.re) ^ 4) := by
  have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ := norm_pos_iff.mpr (two_cpow_sub_one_ne_zero hs0)
  have hratio_pos : 0 < ‖s‖ / s.re := div_pos (norm_pos_iff.mpr hs_ne) hs0
  set δ : ℝ := 1 - τ ^ 2
  have hδ_pos : 0 < δ := by dsimp only [δ]; nlinarith [hτ0, hτ1]
  have hΛδ_pos : 0 < Λ * δ := mul_pos hΛ hδ_pos
  set r4 : ℝ := (Λ * δ) ^ (1 / 4 : ℝ)
  have hr4_pos : 0 < r4 := Real.rpow_pos_of_pos hΛδ_pos _
  have hr4_pow : r4 ^ 4 = Λ * δ := by
    dsimp only [r4]
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hΛδ_pos.le,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
  have h2δ_le_r4 : 2 * δ ≤ r4 := by
    by_contra! hlt
    have hp := pow_lt_pow_left₀ hlt hr4_pos.le (by norm_num : 4 ≠ 0)
    have heq : (2 * δ) ^ 4 = 16 * δ ^ 3 * δ := by ring
    rw [hr4_pow, heq] at hp
    have hle := mul_le_mul_of_nonneg_right hsmall hδ_pos.le
    exact hp.not_ge hle
  let β : GibbsExponent := ⟨s.re, hs0⟩
  have hb₀_β_le_δ : relativeReading (powerResponse β) b₀ ≤ δ := by
    have h := hb₀ (z := (s.re : ℂ)) (by simpa using hs0)
    have hrp := relativePartition_real b₀ β
    dsimp only [β] at hrp
    rw [hrp, ← Complex.ofReal_cpow hτ0.le, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
    have heq : relativeReading (powerResponse β) b₀ = 1 - τ ^ s.re := Complex.ofReal_injective h
    rw [heq]
    have hle : τ ^ (2 : ℝ) ≤ τ ^ s.re :=
      Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1.le (by linarith)
    rw [Real.rpow_two] at hle
    dsimp only [δ]; linarith
  have hrp_le : ‖relativePartition b₀ s‖ ≤ (‖s‖ / s.re) * δ :=
    (relativePartition_norm_le b₀ β le_rfl).trans
      (mul_le_mul_of_nonneg_left hb₀_β_le_δ hratio_pos.le)
  have hlhs_eq : (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4)) ^ 4 = uvZeroThresholdFactor s Λ * δ := by
    calc (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4)) ^ 4
        = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * r4 ^ 4 := by ring
      _ = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * (Λ * δ) := by rw [hr4_pow]
      _ = uvZeroThresholdFactor s Λ * δ := by unfold uvZeroThresholdFactor; ring
  change uvZeroThresholdFactor s Λ * δ < _ at hgt
  rw [← hlhs_eq] at hgt
  have h1 : ‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * r4) < ‖jointSurvivingPartition b₀ s‖ := by
    by_contra! hle
    exact hgt.not_ge (pow_le_pow_left₀ (norm_nonneg _) hle 4)
  rw [jointSurvivingPartition_norm_eq_factor_mul b₀ s] at h1
  have h2 : (‖s‖ / s.re) * r4 < ‖riemannZeta s - relativePartition b₀ s‖ :=
    lt_of_mul_lt_mul_left h1 hf_pos.le
  have h3 : ‖riemannZeta s - relativePartition b₀ s‖ ≤ ‖riemannZeta s‖ + (‖s‖ / s.re) * δ := by
    linarith [norm_sub_le (riemannZeta s) (relativePartition b₀ s), hrp_le]
  have h4 : (1 / 2 : ℝ) * (‖s‖ / s.re) * r4 < ‖riemannZeta s‖ := by
    have hhalf : (‖s‖ / s.re) * δ ≤ (1 / 2 : ℝ) * (‖s‖ / s.re) * r4 := by
      have := mul_le_mul_of_nonneg_left h2δ_le_r4 hratio_pos.le
      linarith
    linarith [h2.trans_le h3]
  have hp4 := pow_lt_pow_left₀ h4 (by positivity) (by norm_num : 4 ≠ 0)
  have heq4 : ((1 / 2 : ℝ) * (‖s‖ / s.re) * r4) ^ 4 =
      (Λ * (‖s‖ / s.re) ^ 4) * δ / 16 := by
    calc ((1 / 2 : ℝ) * (‖s‖ / s.re) * r4) ^ 4
        = (‖s‖ / s.re) ^ 4 * r4 ^ 4 / 16 := by ring
      _ = (‖s‖ / s.re) ^ 4 * (Λ * δ) / 16 := by rw [hr4_pow]
      _ = (Λ * (‖s‖ / s.re) ^ 4) * δ / 16 := by ring
  rw [heq4] at hp4
  have hden_pos : 0 < Λ * (‖s‖ / s.re) ^ 4 := mul_pos hΛ (pow_pos hratio_pos 4)
  rw [lt_div_iff₀ hden_pos]
  linarith

/-! ### Part 5: Unconditional left-strip nonvanishing and UV-capped rank-one witnesses -/

private theorem integral_ne_zero_and_witness_of_zeta_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hζ : riemannZeta s ≠ 0) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 ∧
      ∃ v : MissingWave, uvRegularRankOne s hs0 Λ v ∧
        uvZeroThresholdFactor s Λ * lineLoss v.val <
          ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  have hcs : continued s ≠ 0 := fun h0 =>
    hζ ((ComplementaryHalves.positive_zero_iff ⟨s, hs0⟩).mp h0)
  have hne : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := fun hint0 =>
    hcs ((continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0)
  exact ⟨hne,
    (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mpr hne⟩

/-- **Unconditional nonvanishing and UV-capped witnesses across `0 < Re s < 3001 / 24000` and
across `0 < Re s < 1 / 2`, `|Im s| ≤ 169 / 2`:** -/
theorem integral_ne_zero_and_witness_of_left_known_regions
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    (hreg : s.re < 3001 / 24000 ∨ |s.im| ≤ 169 / 2) {Λ : ℝ} (hΛ : 0 < Λ) :
    (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 ∧
      ∃ v : MissingWave, uvRegularRankOne s hs0 Λ v ∧
        uvZeroThresholdFactor s Λ * lineLoss v.val <
          ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  have hs1 : s.re < 1 := by linarith
  have hζ : riemannZeta s ≠ 0 := by
    rcases hreg with hleft | hlow
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_one_eighth
        hs0 hleft
    · intro hz
      have hz1s : riemannZeta (1 - s) = 0 :=
        _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hz hs0 hs1
      have hlo' : 1 / 2 < (1 - s).re := by simp; linarith
      have hhi' : (1 - s).re < 1 := by simp; linarith
      have him' : |(1 - s).im| ≤ 169 / 2 := by simpa using hlow
      exact CutoffSeparation.riemannZeta_ne_zero_of_strip_abs_im_le_eightyFour_and_half
        hlo' hhi' him' hz1s
  exact integral_ne_zero_and_witness_of_zeta_ne_zero t j hs0 hs1 hζ hΛ

/-- **Reflected high-ordinate power-saving nonvanishing and UV-capped witnesses above `84.5`:**
there exists `B_mob > 0` such that for every left-strip abscissa `0 < σ < 1 / 2` (including every
`3001 / 24000 ≤ σ < 1 / 2`), every dyadic scale `U ≥ exp 100`, and every `[T₁, T₂] ⊂ (U / 4, U / 2)`,
outside a measurable exceptional set `badSet ⊆ [T₁, T₂]` of measure at most
`4 * B_mob * (log U + 2)^5 * U^{1 - (1 / 2 - σ) / 5}`, both conjugate left-strip points `σ ± i γ`
lie strictly above Bohman height `84.5`, have nonzero dyadic overlap integral, and admit a
UV-capped rank-one witness beating `uvZeroThresholdFactor` for every `Λ > 0`. -/
theorem moebius_powerSaving_left_strip_witnesses (tc : ExceptionalTime) (j : ℕ) :
    ∃ B_mob : ℝ, 0 < B_mob ∧
      ∀ {σ U T₁ T₂ : ℝ}, 0 < σ → σ < 1 / 2 →
        Real.exp 100 ≤ U → U / 4 < T₁ → T₁ ≤ T₂ → T₂ < U / 2 →
        let M : ℕ := ⌊U ^ (1 / 4 : ℝ)⌋₊
        let badSet : Set ℝ := {γ ∈ Icc T₁ T₂ |
          (1 / 2 : ℝ) < ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) *
            CutoffSeparation.dirichletSurgPoly M CutoffSeparation.moebiusReal
              (((1 - σ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - 1‖}
        MeasurableSet badSet ∧
        (volume badSet).toReal ≤
          4 * B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (1 / 2 - σ) / 5) ∧
        ∀ γ ∈ Icc T₁ T₂ \ badSet, ∀ {Λ : ℝ}, 0 < Λ →
          let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
          let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
          169 / 2 < |sPos.im| ∧ 169 / 2 < |sNeg.im| ∧
          (∫ u : ℝ in Ioi 0, dyadicOverlapContrast tc j sPos u / (u : ℂ)) ≠ 0 ∧
          (∫ u : ℝ in Ioi 0, dyadicOverlapContrast tc j sNeg u / (u : ℂ)) ≠ 0 ∧
          (∃ (hsPos : 0 < sPos.re) (v : MissingWave),
            uvRegularRankOne sPos hsPos Λ v ∧
              uvZeroThresholdFactor sPos Λ * lineLoss v.val <
                ‖jointSurvivingPartition (missingWaveSpectrum v) sPos‖ ^ 4) ∧
          (∃ (hsNeg : 0 < sNeg.re) (v : MissingWave),
            uvRegularRankOne sNeg hsNeg Λ v ∧
              uvZeroThresholdFactor sNeg Λ * lineLoss v.val <
                ‖jointSurvivingPartition (missingWaveSpectrum v) sNeg‖ ^ 4) := by
  obtain ⟨B_mob, hB_pos, hmob⟩ := CutoffSeparation.moebius_powerSaving_intrinsic_linear_margin
  refine ⟨B_mob, hB_pos, fun {σ U T₁ T₂} hσ0 hσ_half hU hT₁ hT hT₂ => ?_⟩
  have h1σ_lo : 1 / 2 < 1 - σ := by linarith
  have h1σ_hi : 1 - σ ≤ 1 := by linarith
  obtain ⟨hmeas, hvol, _⟩ := hmob h1σ_lo h1σ_hi hU hT₁ hT hT₂
  have hexp_eq : (1 : ℝ) - (1 - σ - 1 / 2) / 5 = 1 - (1 / 2 - σ) / 5 := by ring
  rw [hexp_eq] at hvol
  refine ⟨hmeas, hvol, fun γ hγ {Λ} hΛ => ?_⟩
  have hexp10 : (11 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have hpow10 : (11 : ℝ) ^ 10 ≤ Real.exp 100 := by
    have heq : Real.exp 100 = (Real.exp 10) ^ 10 := by norm_num [← Real.exp_nat_mul]
    rw [heq]
    exact pow_le_pow_left₀ (by positivity) hexp10 10
  have hU_gt : (338 : ℝ) < U := by linarith [show (338 : ℝ) < (11 : ℝ) ^ 10 by norm_num, hpow10, hU]
  have hγ_gt : 169 / 2 < γ := by linarith [hU_gt, hT₁, hγ.1.1]
  set w : ℂ := ((1 - σ : ℝ) : ℂ) + (γ : ℂ) * Complex.I
  have hw_ne0 : riemannZeta w ≠ 0 := by
    intro hzw
    have hnot : ¬(1 / 2 : ℝ) < ‖riemannZeta w *
        CutoffSeparation.dirichletSurgPoly ⌊U ^ (1 / 4 : ℝ)⌋₊ CutoffSeparation.moebiusReal w - 1‖ :=
      fun hgt => hγ.2 ⟨hγ.1, hgt⟩
    rw [hzw, zero_mul, zero_sub, norm_neg, norm_one] at hnot
    norm_num at hnot
  set sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
  set sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
  have hsPos_re : sPos.re = σ := by simp [sPos]
  have hsNeg_re : sNeg.re = σ := by simp [sNeg]
  have hsPos_im : sPos.im = γ := by simp [sPos]
  have hsNeg_im : sNeg.im = -γ := by simp [sNeg]
  have hsPos0 : 0 < sPos.re := by rw [hsPos_re]; exact hσ0
  have hsPos1 : sPos.re < 1 := by rw [hsPos_re]; linarith
  have hsNeg0 : 0 < sNeg.re := by rw [hsNeg_re]; exact hσ0
  have hsNeg1 : sNeg.re < 1 := by rw [hsNeg_re]; linarith
  have h1sNeg : 1 - sNeg = w := by
    dsimp only [sNeg, w]; push_cast; ring
  have hζ_neg : riemannZeta sNeg ≠ 0 := by
    intro hz
    have hz1 := _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hz hsNeg0 hsNeg1
    rw [h1sNeg] at hz1
    exact hw_ne0 hz1
  have hconj_pos : conj sPos = sNeg := by
    apply Complex.ext <;> simp [sPos, sNeg]
  have hζ_pos : riemannZeta sPos ≠ 0 := by
    intro hz
    apply hζ_neg
    rw [← hconj_pos, riemannZeta_conj, hz, map_zero]
  obtain ⟨hne_pos, hv_pos⟩ :=
    integral_ne_zero_and_witness_of_zeta_ne_zero tc j hsPos0 hsPos1 hζ_pos hΛ
  obtain ⟨hne_neg, hv_neg⟩ :=
    integral_ne_zero_and_witness_of_zeta_ne_zero tc j hsNeg0 hsNeg1 hζ_neg hΛ
  refine ⟨?_, ?_, hne_pos, hne_neg, ⟨hsPos0, hv_pos⟩, ⟨hsNeg0, hv_neg⟩⟩
  · rw [hsPos_im, abs_of_pos (by linarith)]; exact hγ_gt
  · rw [hsNeg_im, abs_neg, abs_of_pos (by linarith)]; exact hγ_gt

/-- Set of points in `{3001 / 24000 ≤ Re s < 1 / 2 ∧ |Im s - τ| ≤ h}` lacking a UV-capped
rank-one omission beating `uvZeroThresholdFactor s Λ`. -/
def missingLeftCappedWitnessWindow (Λ h τ : ℝ) : Set ℂ :=
  {s : ℂ | 3001 / 24000 ≤ s.re ∧ s.re < 1 / 2 ∧ |s.im - τ| ≤ h ∧
    ¬∃ (hs0 : 0 < s.re) (v : MissingWave),
      uvRegularRankOne s hs0 Λ v ∧
        uvZeroThresholdFactor s Λ * lineLoss v.val <
          ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4}

/-- **Lorentzian ordinate-window exception bound on the left strip at every height `τ`:**
for every `Λ > 0`, `h : ℝ`, and `τ : ℝ` (including all `|τ| > 84.5`),
`missingLeftCappedWitnessWindow Λ h τ` is finite of cardinality at most
`4 * (1 + h^2) * (xiLineTwoLogDerivConstant + log(|τ| + 4))`. -/
theorem ncard_missingLeftCappedWitnessWindow_le {Λ : ℝ} (hΛ : 0 < Λ) (h τ : ℝ) :
    (missingLeftCappedWitnessWindow Λ h τ).Finite ∧
      ((missingLeftCappedWitnessWindow Λ h τ).ncard : ℝ) ≤
        4 * (1 + h ^ 2) * (_root_.RHTower.xiLineTwoLogDerivConstant + Real.log (|τ| + 4)) := by
  let tc₀ : ExceptionalTime := halfTurnClock
  obtain ⟨hR_fin, hR_le⟩ :=
    CutoffSeparation.ncard_missingZetaFreeMarginWindow_le tc₀ 0 h τ
  let φ : ℂ → ℂ := fun s => conj (1 - s)
  have hφ_inj : Function.Injective φ := by
    intro s₁ s₂ heq
    have h1 : 1 - s₁ = 1 - s₂ := by
      simpa [φ] using congrArg (starRingEnd ℂ) heq
    linear_combination -h1
  have hmaps : MapsTo φ (missingLeftCappedWitnessWindow Λ h τ)
      (CutoffSeparation.missingZetaFreeMarginWindow tc₀ 0 h τ) := by
    rintro s ⟨hlo, hhi, him, hno⟩
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hint0 : (∫ u : ℝ in Ioi 0,
        dyadicOverlapContrast tc₀ 0 s u / (u : ℂ)) = 0 := by
      by_contra hne
      obtain ⟨v, hv⟩ :=
        (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero
          tc₀ 0 hs0 hs1 hΛ).mpr hne
      exact hno ⟨hs0, v, hv⟩
    have hcs : continued s = 0 :=
      (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero
        tc₀ 0 hs0 hs1.ne).mp hint0
    have hζs : riemannZeta s = 0 := (positive_zero_iff ⟨s, hs0⟩).mp hcs
    have hζ1s : riemannZeta (1 - s) = 0 :=
      _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζs hs0 hs1
    have hζφ : riemannZeta (φ s) = 0 := by
      dsimp only [φ]; rw [riemannZeta_conj, hζ1s, map_zero]
    have hφ_lo : 1 / 2 < (φ s).re := by simp [φ]; linarith
    have hφ_hi : (φ s).re ≤ 20999 / 24000 := by simp [φ]; linarith
    have hφ_im : |(φ s).im - τ| ≤ h := by simpa [φ] using him
    have hφ0 : 0 < (φ s).re := by linarith
    have hφ_ne1 : φ s ≠ 1 := fun he => (by linarith : (φ s).re < 1).ne (by rw [he, Complex.one_re])
    refine ⟨hφ_lo, hφ_hi, hφ_im, fun hex => ?_⟩
    exact ((CutoffSeparation.exists_zetaFree_margin_iff_zeta_ne_zero
      tc₀ 0 hφ0 hφ_ne1).mp hex) hζφ
  have hL_fin : (missingLeftCappedWitnessWindow Λ h τ).Finite :=
    (hR_fin.preimage hφ_inj.injOn).subset hmaps
  have hncard_le : (missingLeftCappedWitnessWindow Λ h τ).ncard ≤
      (CutoffSeparation.missingZetaFreeMarginWindow tc₀ 0 h τ).ncard := by
    calc (missingLeftCappedWitnessWindow Λ h τ).ncard
        = (φ '' missingLeftCappedWitnessWindow Λ h τ).ncard :=
          (Set.ncard_image_of_injective _ hφ_inj).symm
      _ ≤ (CutoffSeparation.missingZetaFreeMarginWindow tc₀ 0 h τ).ncard :=
          Set.ncard_le_ncard (Set.image_subset_iff.mpr hmaps) hR_fin
  have hcast : ((missingLeftCappedWitnessWindow Λ h τ).ncard : ℝ) ≤
      ((CutoffSeparation.missingZetaFreeMarginWindow tc₀ 0 h τ).ncard : ℝ) := by
    exact_mod_cast hncard_le
  exact ⟨hL_fin, hcast.trans hR_le⟩

/-- **Unconditional pigeonhole nonvanishing and UV-capped witness law at every height `τ`:**
out of every finite probe set `S ⊆ {3001 / 24000 ≤ Re s < 1 / 2 ∧ |Im s - τ| ≤ h}` of size
exceeding `4 * (1 + h^2) * (xiLineTwoLogDerivConstant + log(|τ| + 4))`, at least one point `s ∈ S`
has nonzero dyadic overlap integral and admits a UV-capped rank-one witness beating
`uvZeroThresholdFactor s Λ`. -/
theorem exists_point_with_left_cappedWitness_of_card_gt
    (t : ExceptionalTime) (j : ℕ) {Λ h τ : ℝ} (hΛ : 0 < Λ) {S : Finset ℂ}
    (hS : ∀ s ∈ S, 3001 / 24000 ≤ s.re ∧ s.re < 1 / 2 ∧ |s.im - τ| ≤ h)
    (hcard : 4 * (1 + h ^ 2) * (_root_.RHTower.xiLineTwoLogDerivConstant + Real.log (|τ| + 4)) <
      (S.card : ℝ)) :
    ∃ s ∈ S, (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 ∧
      ∃ (hs0 : 0 < s.re) (v : MissingWave),
        uvRegularRankOne s hs0 Λ v ∧
          uvZeroThresholdFactor s Λ * lineLoss v.val <
            ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  by_contra hno
  obtain ⟨hL_fin, hL_le⟩ := ncard_missingLeftCappedWitnessWindow_le hΛ h τ
  have hsub : (S : Set ℂ) ⊆ missingLeftCappedWitnessWindow Λ h τ := by
    intro s hs
    refine ⟨(hS s hs).1, (hS s hs).2.1, (hS s hs).2.2, ?_⟩
    rintro ⟨hs0, v, hv⟩
    have hs1 : s.re < 1 := by linarith [(hS s hs).2.1]
    have hne := (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mp
      ⟨v, hv⟩
    exact hno ⟨s, hs, hne, hs0, v, hv⟩
  have hle_ncard : S.card ≤ (missingLeftCappedWitnessWindow Λ h τ).ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub hL_fin
  have hle_r : (S.card : ℝ) ≤ ((missingLeftCappedWitnessWindow Λ h τ).ncard : ℝ) := by
    exact_mod_cast hle_ncard
  linarith

/-- **Horizontal density at every height `τ` (including all `|τ| > 84.5`):**
on every nonempty open subinterval `(a, b) ⊆ [3001 / 24000, 1 / 2]`, infinitely many points
`σ + i τ` unconditionally have nonzero dyadic overlap integral and admit a UV-capped rank-one
omission beating `uvZeroThresholdFactor`. -/
theorem infinite_left_cappedWitness_on_horizontal_interval
    (t : ExceptionalTime) (j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (τ : ℝ)
    {a b : ℝ} (hab : a < b) (ha : 3001 / 24000 ≤ a) (hb : b ≤ 1 / 2) :
    {σ : ℝ | a < σ ∧ σ < b ∧
      (∫ u : ℝ in Ioi 0,
        dyadicOverlapContrast t j ((σ : ℂ) + (τ : ℂ) * Complex.I) u / (u : ℂ)) ≠ 0 ∧
      ∃ (hs0 : 0 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re) (v : MissingWave),
        uvRegularRankOne ((σ : ℂ) + (τ : ℂ) * Complex.I) hs0 Λ v ∧
          uvZeroThresholdFactor ((σ : ℂ) + (τ : ℂ) * Complex.I) Λ * lineLoss v.val <
            ‖jointSurvivingPartition (missingWaveSpectrum v)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 4}.Infinite := by
  have hIoo_inf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  obtain ⟨hL_fin, _⟩ := ncard_missingLeftCappedWitnessWindow_le hΛ 0 τ
  let emb : ℝ → ℂ := fun σ => (σ : ℂ) + (τ : ℂ) * Complex.I
  have hemb_inj : Function.Injective emb := fun x y hxy => by
    simpa [emb] using congrArg Complex.re hxy
  have hbad_fin : {σ : ℝ | a < σ ∧ σ < b ∧
      ¬∃ (hs0 : 0 < (emb σ).re) (v : MissingWave),
        uvRegularRankOne (emb σ) hs0 Λ v ∧
          uvZeroThresholdFactor (emb σ) Λ * lineLoss v.val <
            ‖jointSurvivingPartition (missingWaveSpectrum v) (emb σ)‖ ^ 4}.Finite := by
    refine (hL_fin.preimage hemb_inj.injOn).subset ?_
    rintro σ ⟨hσa, hσb, hnot⟩
    exact ⟨by simp [emb]; linarith, by simp [emb]; linarith, by simp [emb], hnot⟩
  refine (hIoo_inf.sdiff hbad_fin).mono ?_
  rintro σ ⟨⟨hσa, hσb⟩, hnot_bad⟩
  have hwit : ∃ (hs0 : 0 < (emb σ).re) (v : MissingWave),
      uvRegularRankOne (emb σ) hs0 Λ v ∧
        uvZeroThresholdFactor (emb σ) Λ * lineLoss v.val <
          ‖jointSurvivingPartition (missingWaveSpectrum v) (emb σ)‖ ^ 4 := by
    by_contra hno
    exact hnot_bad ⟨hσa, hσb, hno⟩
  obtain ⟨hs0, v, hv⟩ := hwit
  have hs1 : (emb σ).re < 1 := by simp [emb]; linarith
  have hne := (exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ).mp
    ⟨v, hv⟩
  exact ⟨hσa, hσb, hne, hs0, v, hv⟩

#print axioms summable_dyadicSpectralTriad
#print axioms tsum_dyadicSpectralTriad_eq
#print axioms jointSurvivingPartition_eq_tsum_dyadicSpectralTriad
#print axioms jointSurvivingPartition_sub_eq
#print axioms exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero
#print axioms jointSurviving_chord_bound_of_integral_eq_zero
#print axioms exists_chordZeroThreshold_witness_iff_integral_ne_zero
#print axioms rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half
#print axioms rh_iff_exists_uvRegular_witness_above_eightyFour_and_half
#print axioms exists_uvRegularRankOne_exceeding_lt_chordBound_of_re_lt_half
#print axioms isLeast_uvRegularRankOne_fourthPower_of_integral_eq_zero
#print axioms uvRegularRankOne_saturates_all_caps_iff_re_lt_half
#print axioms witness_lineLoss_fourth_root_lt_clock_head_tail
#print axioms exists_uvRegular_witness_of_norm_zeta_ge
#print axioms groundAttenuation_loss_lt_of_beating_zeroBound
#print axioms integral_ne_zero_and_witness_of_left_known_regions
#print axioms moebius_powerSaving_left_strip_witnesses
#print axioms ncard_missingLeftCappedWitnessWindow_le
#print axioms exists_point_with_left_cappedWitness_of_card_gt
#print axioms infinite_left_cappedWitness_on_horizontal_interval

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
