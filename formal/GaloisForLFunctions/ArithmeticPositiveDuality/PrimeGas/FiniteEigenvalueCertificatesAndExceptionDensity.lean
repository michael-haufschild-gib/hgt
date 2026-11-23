import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CappedWitnessSharpnessAndLeftNonvanishing
import GaloisForLFunctions.RHTower.XiLocalWindowDensity
import GaloisForLFunctions.RHTower.SpeiserCleanHeights
import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw

/-!
# Finite surviving-eigenvalue prefix certificates, high-ordinate witness degeneration, clean-height lines, and sublinear left-strip exception density

We advance the single-omission nonvanishing theory on `{3001 / 24000 ≤ Re s < 1 / 2 ∧ 169 / 2 < |Im s|}`
without taking `riemannZeta` as input to the spectral reading:

1. **Uniform `ζ`-free triad tail bound and finite-eigenvalue prefix certificates
   (`finiteTriadReading`, `triadTailBound`, `norm_jointSurviving_sub_finiteTriadReading_le`,
   `tendsto_triadTailBound_zero`, `exists_finite_capped_witness_iff_integral_ne_zero`,
   `exists_finite_uncapped_witness_iff_integral_ne_zero`,
   `rh_iff_exists_finite_eigenvalue_witness_above_eightyFour_and_half`)**:
   Every rank-one interlacing spectrum `b : SpectralBand 1` satisfies the uniform `ζ`-free bound
   `‖jointSurvivingPartition b s - finiteTriadReading b K s‖ ≤ triadTailBound K s`, where
   `finiteTriadReading b K s` depends only on the first `2 K` surviving eigenvalues `b(0), …, b(2K - 1)`.
   Both the UV-capped fourth-power witness test and the uncapped `(2 / Re s)`-power witness test
   become exact finite-eigenvalue equivalences (`↔`).

2. **Uniform sublinear partition growth and high-ordinate witness degeneration
   (`highOrdinateWitnessConstant`, `norm_jointSurvivingPartition_le_rpow_im_uniform`,
   `capped_witness_lineLoss_lt_rpow_neg`, `uncapped_witness_lineLoss_lt_rpow_neg`,
   `uncapped_witness_operator_sq_dist_le_rpow_neg`,
   `eventually_no_finset_witness_at_high_ordinates`)**:
   Splitting `dyadicSpectralTriad` at `K = ⌊|t|^{1 / (1 + σ)}⌋₊` bounds `‖jointSurvivingPartition b (σ + i t)‖`
   by `O_σ(|t|^{1 / (1 + σ)})` uniformly across **all** `b : SpectralBand 1`. Since both explicit
   zero-thresholds grow linearly in `|t|` at fixed `lineLoss`, every high-ordinate witness is forced
   into polynomial fourth-trace collapse (`|t|^{-4σ / (1 + σ)}` under cap `Λ`; `|t|^{-2 / (1 + σ)}`
   without cap, forcing `‖D^2 - G_v^2‖ ≤ O_σ(|t|^{-1 / (1 + σ)})`), ruling out any fixed omission or
   finite omission bank across unbounded heights even under `RiemannHypothesis`.

3. **Clean-height zero-exception horizontal lines in every `T^{24 / 25}` window above `84.5`
   (`speiserClean_full_left_strip_witnesses`,
   `eventually_volume_clean_zero_exception_heights_window_ge`)**:
   At every `SpeiserUnshadowed γ` with `γ ≥ 101`, every `σ ∈ (0, 1 / 2)` at `±γ` (`|±γ| > 84.5`)
   carries both capped and uncapped finite-eigenvalue witnesses with zero exceptions across the
   entire horizontal segment and a uniform horizontal attenuation scale on every `[a, b] ⊂ (0, 1 / 2)`.
   These zero-exception heights occupy measure at least `(14 / 25) H - 3` in every window
   `[T + 3 / 2, T + H - 3 / 2]` (`T^{24 / 25} ≤ H ≤ T`) for large `T`.

4. **Sublinear power-saving exception bounds on dyadic left-strip boxes
   (`missingLeftWitnessBox`, `ncard_missingLeftWitnessBox_le_two_mul_zeroHeightBox`,
   `exists_ncard_missingLeftWitnessBox_le_one_sub_four_thirds_uniform`,
   `exists_ncard_missingLeftWitnessBox_le_density_hypothesis`)**:
   Whereas the local Lorentzian bound allows `O(log T)` exceptions per unit height (`O(T log T)` on
   `[T, 2T]`), reflecting `missingLeftWitnessBox Λ σ₀ T` into `zeroHeightBox (1 - σ₀) T` proves
   `O((1 + log T)^B T^{1 - (4/3 - δ)(1/2 - σ₀)}) = o(T)` across `3001 / 24000 ≤ Re s ≤ 1 / 2 - θ`
   and `O_ε((1 + log T)^{dhLogExponent ε + 4} T^{(2 + ε) σ₀})` across `3001 / 24000 ≤ Re s ≤ 1 / 6`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing

/-! ### Part 1: Uniform `ζ`-free triad tail bound and finite-eigenvalue prefix certificates -/

private theorem two_cpow_sub_one_ne_zero' {s : ℂ} (hs0 : 0 < s.re) :
    (2 : ℂ) ^ s - 1 ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := (factor_zero_iff s).mp h0
  exact hs0.ne' ((congrArg Complex.re hk).trans (frequency_re k))

private theorem one_sub_two_cpow_one_sub_ne_zero'' {s : ℂ} (hs_re : s.re ≠ 1) :
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

/-- Finite `K`-triad surviving spectral reading using only the first `2 K` surviving eigenvalues
`b(0), …, b(2K - 1)` of `b : SpectralBand r`, with no `riemannZeta` input. -/
def finiteTriadReading {r : ℕ} (b : SpectralBand r) (K : ℕ) (s : ℂ) : ℂ :=
  (((2 : ℂ) ^ s - 1) / (1 - (2 : ℂ) ^ (1 - s))) *
    ∑ k ∈ Finset.range K, dyadicSpectralTriad b s k

/-- Explicit `ζ`-free uniform tail bound for `finiteTriadReading` across all `b : SpectralBand 1`. -/
def triadTailBound (K : ℕ) (s : ℂ) : ℝ :=
  (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖) *
    ((4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re)

private theorem two_cpow_one_sub_mul_ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    (2 : ℂ) ^ (1 - s) * (x : ℂ) ^ s = 2 * ((x / 2 : ℝ) : ℂ) ^ s := by
  have hmul : ((x / 2 : ℝ) : ℂ) ^ s * (2 : ℂ) ^ s = (x : ℂ) ^ s := by
    have h := (Complex.mul_cpow_ofReal_nonneg (div_nonneg hx zero_le_two) zero_le_two s).symm
    rw [Complex.ofReal_ofNat] at h
    refine h.trans ?_
    congr 1; push_cast; ring
  have h2s_ne : (2 : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_ne_zero]
    exact Complex.exp_ne_zero _
  rw [Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one, ← hmul]
  field_simp [h2s_ne]

private theorem norm_cpow_sub_le_window {a b u w : ℝ} (ha : 0 < a) (hb1 : b ≤ 1)
    (hu : u ∈ Icc a b) (hw : w ∈ Icc a b) {s : ℂ} (hs0 : 0 < s.re) :
    ‖(u : ℂ) ^ s - (w : ℂ) ^ s‖ ≤ (‖s‖ / s.re) * (b ^ s.re - a ^ s.re) := by
  have ha_le : a ^ s.re ≤ b ^ s.re := Real.rpow_le_rpow ha.le (hu.1.trans hu.2) hs0.le
  rcases le_total w u with hwu | huw
  · have hch := norm_thermal_chord (ha.trans_le hw.1) hwu (hu.2.trans hb1) hs0 le_rfl
    have hsub : u ^ s.re - w ^ s.re ≤ b ^ s.re - a ^ s.re :=
      sub_le_sub (Real.rpow_le_rpow (ha.trans_le hu.1).le hu.2 hs0.le)
        (Real.rpow_le_rpow ha.le hw.1 hs0.le)
    exact hch.trans (mul_le_mul_of_nonneg_left hsub (div_nonneg (norm_nonneg s) hs0.le))
  · rw [norm_sub_rev]
    have hch := norm_thermal_chord (ha.trans_le hu.1) huw (hw.2.trans hb1) hs0 le_rfl
    have hsub : w ^ s.re - u ^ s.re ≤ b ^ s.re - a ^ s.re :=
      sub_le_sub (Real.rpow_le_rpow (ha.trans_le hw.1).le hw.2 hs0.le)
        (Real.rpow_le_rpow ha.le hu.1 hs0.le)
    exact hch.trans (mul_le_mul_of_nonneg_left hsub (div_nonneg (norm_nonneg s) hs0.le))

/-- Pointwise two-step telescoping bound on `dyadicSpectralTriad b s k` for every `b : SpectralBand 1`. -/
theorem norm_dyadicSpectralTriad_le (b : SpectralBand 1) {s : ℂ} (hs0 : 0 < s.re) (k : ℕ) :
    ‖dyadicSpectralTriad b s k‖ ≤
      (2 * ‖s‖ / s.re) *
        (occupationWeight (2 * k) ^ s.re - occupationWeight (2 * (k + 2)) ^ s.re) := by
  set lo : ℝ := occupationWeight (2 * (k + 2))
  set hi : ℝ := occupationWeight (2 * k)
  have hlo_pos : 0 < lo := occupationWeight_pos _
  have hhi_le1 : hi ≤ 1 := (occupation_in_unit (2 * k)).2
  have hu2k : (b (2 * k)).val ∈ Icc lo hi := by
    refine ⟨(occupationWeight_antitone (by omega : 2 * k + 1 ≤ 2 * (k + 2))).trans (b (2 * k)).property.1,
      (b (2 * k)).property.2⟩
  have hu2k1 : (b (2 * k + 1)).val ∈ Icc lo hi := by
    refine ⟨(occupationWeight_antitone (by omega : 2 * k + 2 ≤ 2 * (k + 2))).trans
        (b (2 * k + 1)).property.1,
      (b (2 * k + 1)).property.2.trans (occupationWeight_antitone (by omega : 2 * k ≤ 2 * k + 1))⟩
  have huk_half : (b k).val / 2 ∈ Icc lo hi := by
    have hlo_half : occupationWeight (2 * k + 3) = occupationWeight (k + 1) / 2 := by
      simp only [occupationWeight_eq]; push_cast; field_simp; ring
    have hhi_half : occupationWeight (2 * k + 1) = occupationWeight k / 2 := by
      simp only [occupationWeight_eq]; push_cast; field_simp; ring
    refine ⟨?_, ?_⟩
    · calc lo ≤ occupationWeight (2 * k + 3) :=
            occupationWeight_antitone (by omega : 2 * k + 3 ≤ 2 * (k + 2))
        _ = occupationWeight (k + 1) / 2 := hlo_half
        _ ≤ (b k).val / 2 := div_le_div_of_nonneg_right (b k).property.1 zero_le_two
    · calc (b k).val / 2 ≤ occupationWeight k / 2 :=
            div_le_div_of_nonneg_right (b k).property.2 zero_le_two
        _ = occupationWeight (2 * k + 1) := hhi_half.symm
        _ ≤ hi := occupationWeight_antitone (by omega : 2 * k ≤ 2 * k + 1)
  have hsplit : dyadicSpectralTriad b s k =
      (((b (2 * k)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s) +
        (((b (2 * k + 1)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s) := by
    unfold dyadicSpectralTriad
    rw [two_cpow_one_sub_mul_ofReal_cpow (band_pos b k).le s]
    ring
  have h1 := norm_cpow_sub_le_window hlo_pos hhi_le1 hu2k huk_half hs0
  have h2 := norm_cpow_sub_le_window hlo_pos hhi_le1 hu2k1 huk_half hs0
  rw [hsplit]
  calc ‖(((b (2 * k)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s) +
          (((b (2 * k + 1)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s)‖
      ≤ ‖((b (2 * k)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s‖ +
          ‖((b (2 * k + 1)).val : ℂ) ^ s - (((b k).val / 2 : ℝ) : ℂ) ^ s‖ := norm_add_le _ _
    _ ≤ (‖s‖ / s.re) * (hi ^ s.re - lo ^ s.re) + (‖s‖ / s.re) * (hi ^ s.re - lo ^ s.re) :=
        add_le_add h1 h2
    _ = (2 * ‖s‖ / s.re) * (hi ^ s.re - lo ^ s.re) := by ring

private theorem tsum_triad_tail_le (b : SpectralBand 1) {s : ℂ} (hs0 : 0 < s.re) (K : ℕ) :
    ‖∑' j : ℕ, dyadicSpectralTriad b s (j + K)‖ ≤
      (4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := by
  let g : ℕ → ℝ := fun m => occupationWeight (2 * m) ^ s.re
  have hg_nn : ∀ m, 0 ≤ g m := fun m => Real.rpow_nonneg (occupationWeight_pos _).le _
  have hg_anti : ∀ m₁ m₂, m₁ ≤ m₂ → g m₂ ≤ g m₁ := fun m₁ m₂ hm =>
    Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (by omega : 2 * m₁ ≤ 2 * m₂)) hs0.le
  let d : ℕ → ℝ := fun j => g (j + K) - g (j + K + 2)
  have hd_nn : ∀ j, 0 ≤ d j := fun j => sub_nonneg.mpr (hg_anti _ _ (by omega))
  have hd_sum_le : ∀ M : ℕ, (∑ j ∈ Finset.range M, d j) ≤ 2 * g K := by
    intro M
    have hsplit : ∀ j : ℕ, d j =
        (g (K + j) - g (K + (j + 1))) + (g (K + 1 + j) - g (K + 1 + (j + 1))) := fun j => by
      dsimp only [d]
      have h1 : j + K = K + j := Nat.add_comm j K
      have h2 : K + j + 2 = K + 1 + (j + 1) := by omega
      have h3 : K + (j + 1) = K + 1 + j := by omega
      rw [h1, h2, h3]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun j => g (K + j)) M,
      Finset.sum_range_sub' (fun j => g (K + 1 + j)) M, Nat.add_zero, Nat.add_zero]
    have hle1 : g (K + 1) ≤ g K := hg_anti K (K + 1) (Nat.le_succ K)
    linarith [hg_nn (K + M), hg_nn (K + 1 + M)]
  have hd_summable : Summable d := summable_of_sum_range_le hd_nn hd_sum_le
  have hd_tsum_le : (∑' j : ℕ, d j) ≤ 2 * g K :=
    le_of_tendsto hd_summable.hasSum.tendsto_sum_nat (Eventually.of_forall hd_sum_le)
  have hnorm_sum : Summable (fun j : ℕ => ‖dyadicSpectralTriad b s (j + K)‖) :=
    ((summable_nat_add_iff K).mpr (summable_dyadicSpectralTriad b hs0)).norm
  have hmaj_sum : Summable (fun j : ℕ => (2 * ‖s‖ / s.re) * d j) :=
    hd_summable.mul_left (2 * ‖s‖ / s.re)
  have hterm_le : ∀ j : ℕ, ‖dyadicSpectralTriad b s (j + K)‖ ≤ (2 * ‖s‖ / s.re) * d j := by
    intro j
    simpa only [d, g, Nat.add_assoc] using norm_dyadicSpectralTriad_le b hs0 (j + K)
  calc ‖∑' j : ℕ, dyadicSpectralTriad b s (j + K)‖
      ≤ ∑' j : ℕ, ‖dyadicSpectralTriad b s (j + K)‖ := norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' j : ℕ, (2 * ‖s‖ / s.re) * d j := hnorm_sum.tsum_le_tsum hterm_le hmaj_sum
    _ = (2 * ‖s‖ / s.re) * ∑' j : ℕ, d j := tsum_mul_left
    _ ≤ (2 * ‖s‖ / s.re) * (2 * g K) :=
        mul_le_mul_of_nonneg_left hd_tsum_le (div_nonneg (by positivity) hs0.le)
    _ = (4 * ‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := by dsimp only [g]; ring

/-- **Uniform `ζ`-free finite-eigenvalue truncation bound across `SpectralBand 1`:**
for every `b : SpectralBand 1`, every `K : ℕ`, and every `s` with `0 < Re s` and `Re s ≠ 1`,
`‖jointSurvivingPartition b s - finiteTriadReading b K s‖ ≤ triadTailBound K s`. -/
theorem norm_jointSurviving_sub_finiteTriadReading_le (b : SpectralBand 1) (K : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (hs_re : s.re ≠ 1) :
    ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ ≤ triadTailBound K s := by
  have hsplit := (summable_dyadicSpectralTriad b hs0).sum_add_tsum_nat_add K
  rw [jointSurvivingPartition_eq_tsum_dyadicSpectralTriad b hs0 hs_re, ← hsplit,
    finiteTriadReading, mul_add, add_sub_cancel_left, norm_mul, norm_div]
  exact mul_le_mul_of_nonneg_left (tsum_triad_tail_le b hs0 K) (by positivity)

/-- For every `s` with `0 < Re s`, `triadTailBound K s → 0` as `K → ∞`. -/
theorem tendsto_triadTailBound_zero {s : ℂ} (hs0 : 0 < s.re) :
    Tendsto (fun K : ℕ => triadTailBound K s) atTop (𝓝 0) := by
  have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => by omega : ∀ K : ℕ, K ≤ 2 * K) tendsto_id
  have hocc0 : Tendsto (fun K : ℕ => occupationWeight (2 * K) ^ s.re) atTop (𝓝 0) := by
    have h := ((Real.continuous_rpow_const hs0.le).tendsto 0).comp (occupationWeight_tendsto.comp h2K)
    simpa only [Function.comp_def, Real.zero_rpow hs0.ne'] using h
  have hmul := (hocc0.const_mul (4 * ‖s‖ / s.re)).const_mul
    (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖)
  simpa only [mul_zero, triadTailBound] using hmul

/-- **Exact finite-eigenvalue certificate under a fixed UV cap `Λ > 0` (power `4`):**
for `0 < Re s < 1`, nonvanishing of the dyadic overlap integral is equivalent to the existence of a
conserving rank-one omission `v : MissingWave` in `uvRegularRankOne s hs0 Λ` and a finite prefix
length `K : ℕ` whose `2 K`-eigenvalue reading `finiteTriadReading` strictly beats
`(uvZeroThresholdFactor s Λ * lineLoss v.val)^{1/4} + triadTailBound K s`. -/
theorem exists_finite_capped_witness_iff_integral_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (∃ (v : MissingWave) (K : ℕ), uvRegularRankOne s hs0 Λ v ∧
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  rw [← exists_uvRegularRankOne_beating_zeroBound_iff_integral_ne_zero t j hs0 hs1 hΛ]
  constructor
  · rintro ⟨v, K, huv, hgt⟩
    let b := missingWaveSpectrum v
    have hL_pos : 0 < uvZeroThresholdFactor s Λ * lineLoss v.val := by
      unfold uvZeroThresholdFactor
      have hs_ne : s ≠ 0 := fun h => hs0.ne' (by rw [h, Complex.zero_re])
      have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ := norm_pos_iff.mpr (two_cpow_sub_one_ne_zero' hs0)
      have hsr_pos : 0 < ‖s‖ / s.re := div_pos (norm_pos_iff.mpr hs_ne) hs0
      have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
      positivity
    have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
    have htri : ‖finiteTriadReading b K s‖ ≤
        ‖jointSurvivingPartition b s‖ + ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ := by
      have h := norm_add_le (jointSurvivingPartition b s)
        (finiteTriadReading b K s - jointSurvivingPartition b s)
      simpa only [add_sub_cancel, norm_sub_rev] using h
    have hbase_lt : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) <
        ‖jointSurvivingPartition b s‖ := by linarith
    have hp4 := pow_lt_pow_left₀ hbase_lt (Real.rpow_nonneg hL_pos.le _) (by norm_num : 4 ≠ 0)
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hL_pos.le,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one] at hp4
    exact ⟨v, huv, hp4⟩
  · rintro ⟨v, huv, hgt⟩
    let b := missingWaveSpectrum v
    set A : ℝ := uvZeroThresholdFactor s Λ * lineLoss v.val
    have hA_nn : 0 ≤ A := by
      dsimp only [A]; unfold uvZeroThresholdFactor
      exact mul_nonneg (by positivity) (line_loss_bounds v).1.le
    have hr4_pow : (A ^ (1 / 4 : ℝ)) ^ 4 = A := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hA_nn,
        show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
    have hbase_lt : A ^ (1 / 4 : ℝ) < ‖jointSurvivingPartition b s‖ := by
      by_contra! hle
      have hp := pow_le_pow_left₀ (norm_nonneg _) hle 4
      rw [hr4_pow] at hp
      exact hgt.not_ge hp
    set gap : ℝ := (‖jointSurvivingPartition b s‖ - A ^ (1 / 4 : ℝ)) / 2
    have hgap : 0 < gap := by dsimp only [gap]; linarith
    obtain ⟨K, hK⟩ := ((tendsto_triadTailBound_zero hs0).eventually (gt_mem_nhds hgap)).exists
    have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
    have htri : ‖jointSurvivingPartition b s‖ ≤
        ‖finiteTriadReading b K s‖ + ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ := by
      have h := norm_add_le (finiteTriadReading b K s)
        (jointSurvivingPartition b s - finiteTriadReading b K s)
      simpa only [add_sub_cancel] using h
    refine ⟨v, K, huv, ?_⟩
    dsimp only [A, gap] at hK ⊢
    linarith

/-- **Exact finite-eigenvalue certificate without UV cap (sharp power `2 / Re s`):**
for `0 < Re s < 1`, nonvanishing of the dyadic overlap integral is equivalent to the existence of a
conserving rank-one omission `v : MissingWave` and a finite prefix `K : ℕ` whose `2 K`-eigenvalue
reading beats `(chordZeroThresholdFactor s * lineLoss v.val)^{s.re / 2} + triadTailBound K s`. -/
theorem exists_finite_uncapped_witness_iff_integral_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (∃ (v : MissingWave) (K : ℕ),
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  rw [← exists_chordZeroThreshold_witness_iff_integral_ne_zero t j hs0 hs1]
  have hexp_pos : 0 < 2 / s.re := div_pos two_pos hs0
  constructor
  · rintro ⟨v, K, hgt⟩
    let b := missingWaveSpectrum v
    set A : ℝ := chordZeroThresholdFactor s * lineLoss v.val
    have hA_nn : 0 ≤ A := by
      dsimp only [A, chordZeroThresholdFactor]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (line_loss_bounds v).1.le
    have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
    have htri : ‖finiteTriadReading b K s‖ ≤
        ‖jointSurvivingPartition b s‖ + ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ := by
      have h := norm_add_le (jointSurvivingPartition b s)
        (finiteTriadReading b K s - jointSurvivingPartition b s)
      simpa only [add_sub_cancel, norm_sub_rev] using h
    have hbase_lt : A ^ (s.re / 2) < ‖jointSurvivingPartition b s‖ := by linarith
    have hrpow := Real.rpow_lt_rpow (Real.rpow_nonneg hA_nn _) hbase_lt hexp_pos
    rw [← Real.rpow_mul hA_nn, show (s.re / 2) * (2 / s.re) = 1 by field_simp [hs0.ne'],
      Real.rpow_one] at hrpow
    exact ⟨v, hrpow⟩
  · rintro ⟨v, hgt⟩
    let b := missingWaveSpectrum v
    set A : ℝ := chordZeroThresholdFactor s * lineLoss v.val
    have hA_nn : 0 ≤ A := by
      dsimp only [A, chordZeroThresholdFactor]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (line_loss_bounds v).1.le
    have hpow_cancel : (A ^ (s.re / 2)) ^ (2 / s.re) = A := by
      rw [← Real.rpow_mul hA_nn, show (s.re / 2) * (2 / s.re) = 1 by field_simp [hs0.ne'],
        Real.rpow_one]
    have hbase_lt : A ^ (s.re / 2) < ‖jointSurvivingPartition b s‖ := by
      by_contra! hle
      have hp := Real.rpow_le_rpow (norm_nonneg _) hle hexp_pos.le
      rw [hpow_cancel] at hp
      exact hgt.not_ge hp
    set gap : ℝ := (‖jointSurvivingPartition b s‖ - A ^ (s.re / 2)) / 2
    have hgap : 0 < gap := by dsimp only [gap]; linarith
    obtain ⟨K, hK⟩ := ((tendsto_triadTailBound_zero hs0).eventually (gt_mem_nhds hgap)).exists
    have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
    have htri : ‖jointSurvivingPartition b s‖ ≤
        ‖finiteTriadReading b K s‖ + ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ := by
      have h := norm_add_le (finiteTriadReading b K s)
        (jointSurvivingPartition b s - finiteTriadReading b K s)
      simpa only [add_sub_cancel] using h
    refine ⟨v, K, ?_⟩
    dsimp only [A, gap] at hK ⊢
    linarith

/-- **Unconditional reduction of `RiemannHypothesis` to finite surviving-eigenvalue witnesses
(both UV-capped at power `4` and uncapped at power `2 / Re s`) above height `84.5`:** -/
theorem rh_iff_exists_finite_eigenvalue_witness_above_eightyFour_and_half
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        ∃ (v : MissingWave) (K : ℕ),
          (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
            ‖finiteTriadReading (missingWaveSpectrum v) K s‖) := by
  let tc₀ : ExceptionalTime := halfTurnClock
  refine ⟨?_, ?_⟩
  · rw [rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half tc₀ 0]
    refine forall₄_congr fun s hlo hhi _ => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    constructor
    · intro hne
      obtain ⟨v, K, hv⟩ :=
        (exists_finite_capped_witness_iff_integral_ne_zero tc₀ 0 hs0 hs1 hΛ).mpr hne
      exact ⟨hs0, v, K, hv⟩
    · rintro ⟨_, v, K, hv⟩
      exact (exists_finite_capped_witness_iff_integral_ne_zero tc₀ 0 hs0 hs1 hΛ).mp ⟨v, K, hv⟩
  · rw [rh_iff_dyadicOverlap_integral_ne_zero_left_strip_above_eightyFour_and_half tc₀ 0]
    refine forall₄_congr fun s hlo hhi _ => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    exact (exists_finite_uncapped_witness_iff_integral_ne_zero tc₀ 0 hs0 hs1).symm

/-! ### Part 2: Sublinear partition growth and high-ordinate witness degeneration -/

private theorem norm_dyadicSpectralTriad_le_four (b : SpectralBand 1) {s : ℂ}
    (hs0 : 0 < s.re) (_hs1 : s.re < 1) (k : ℕ) :
    ‖dyadicSpectralTriad b s k‖ ≤ 4 := by
  have hb_le1 : ∀ n : ℕ, ‖((b n).val : ℂ) ^ s‖ ≤ 1 := fun n => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (band_pos b n)]
    exact Real.rpow_le_one (band_in_unit b n).1 (band_in_unit b n).2 hs0.le
  have h2_le2 : ‖(2 : ℂ) ^ (1 - s)‖ ≤ 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.sub_re, Complex.one_re]
    calc (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_lt_two.le (by linarith)
      _ = 2 := Real.rpow_one 2
  unfold dyadicSpectralTriad
  calc ‖(((b (2 * k)).val : ℂ) ^ s + ((b (2 * k + 1)).val : ℂ) ^ s) -
          (2 : ℂ) ^ (1 - s) * ((b k).val : ℂ) ^ s‖
      ≤ (‖((b (2 * k)).val : ℂ) ^ s‖ + ‖((b (2 * k + 1)).val : ℂ) ^ s‖) +
          ‖(2 : ℂ) ^ (1 - s)‖ * ‖((b k).val : ℂ) ^ s‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul _ _).le)
    _ ≤ (1 + 1) + 2 * 1 :=
        add_le_add (add_le_add (hb_le1 _) (hb_le1 _))
          (mul_le_mul h2_le2 (hb_le1 _) (norm_nonneg _) zero_le_two)
    _ = 4 := by norm_num

private theorem factor_norm_bounds {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    0 < (2 : ℝ) ^ s.re - 1 ∧
      (2 : ℝ) ^ s.re - 1 ≤ ‖(2 : ℂ) ^ s - 1‖ ∧
      ‖(2 : ℂ) ^ s - 1‖ ≤ (2 : ℝ) ^ s.re + 1 ∧
      0 < (2 : ℝ) ^ (1 - s.re) - 1 ∧
      (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
  have h2s : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
  have h2_1s : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.sub_re, Complex.one_re]
  have hpos1 : 0 < (2 : ℝ) ^ s.re - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hs0)
  have hpos2 : 0 < (2 : ℝ) ^ (1 - s.re) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hs1))
  have hlo1 : (2 : ℝ) ^ s.re - 1 ≤ ‖(2 : ℂ) ^ s - 1‖ := by
    have h := norm_sub_norm_le ((2 : ℂ) ^ s) 1
    rwa [h2s, norm_one] at h
  have hhi1 : ‖(2 : ℂ) ^ s - 1‖ ≤ (2 : ℝ) ^ s.re + 1 := by
    have h := norm_sub_le ((2 : ℂ) ^ s) 1
    rwa [h2s, norm_one] at h
  have hlo2 : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    rw [norm_sub_rev]
    have h := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
    rwa [h2_1s, norm_one] at h
  exact ⟨hpos1, hlo1, hhi1, hpos2, hlo2⟩

/-- Explicit abscissa-dependent constant governing high-ordinate witness degeneration on `0 < σ < 1`. -/
def highOrdinateWitnessConstant (σ : ℝ) : ℝ :=
  (((2 : ℝ) ^ σ + 1) / (((2 : ℝ) ^ σ - 1) * ((2 : ℝ) ^ (1 - σ) - 1))) * (8 * (σ + 1))

theorem highOrdinateWitnessConstant_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < highOrdinateWitnessConstant σ := by
  have h1 : 0 < (2 : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hσ0)
  have h2 : 0 < (2 : ℝ) ^ (1 - σ) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hσ1))
  unfold highOrdinateWitnessConstant
  positivity

/-- **Uniform sublinear height bound on `jointSurvivingPartition` across all `SpectralBand 1`:**
for every `s` with `0 < Re s < 1` and `1 ≤ |Im s|`, and **every** `b : SpectralBand 1` (with no UV
cap and no hypothesis on `ζ`), `‖jointSurvivingPartition b s‖` grows at most as `|Im s|^{1 / (1 + Re s)}`. -/
theorem norm_jointSurvivingPartition_le_rpow_im_uniform (b : SpectralBand 1)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) :
    ‖jointSurvivingPartition b s‖ ≤
      (((2 : ℝ) ^ s.re + 1) / ((2 : ℝ) ^ (1 - s.re) - 1)) *
        (8 * (s.re + 1) / s.re) * |s.im| ^ (1 / (1 + s.re)) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  obtain ⟨_, _, h2_hi, h12_pos, h12_lo⟩ := factor_norm_bounds hs0 hs1
  set K : ℕ := ⌊t ^ (1 / (1 + σ))⌋₊
  have hexp_pos : 0 < 1 / (1 + σ) := by positivity
  have htr_ge1 : 1 ≤ t ^ (1 / (1 + σ)) := Real.one_le_rpow him hexp_pos.le
  have hK_le : (K : ℝ) ≤ t ^ (1 / (1 + σ)) := Nat.floor_le (zero_le_one.trans htr_ge1)
  have hK_gt : t ^ (1 / (1 + σ)) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hocc_le : occupationWeight (2 * K) ^ σ ≤ t ^ (-σ / (1 + σ)) := by
    have hinv_le : occupationWeight (2 * K) ≤ (t ^ (1 / (1 + σ)))⁻¹ := by
      rw [occupationWeight_eq]
      push_cast
      exact inv_anti₀ (zero_lt_one.trans_le htr_ge1) (by linarith)
    calc occupationWeight (2 * K) ^ σ
        ≤ ((t ^ (1 / (1 + σ)))⁻¹) ^ σ :=
          Real.rpow_le_rpow (occupationWeight_pos _).le hinv_le hs0.le
      _ = t ^ (-σ / (1 + σ)) := by
          rw [Real.inv_rpow (zero_le_one.trans htr_ge1), ← Real.rpow_neg (zero_le_one.trans htr_ge1),
            ← Real.rpow_mul ht_pos.le]
          congr 1; ring
  have hnorm_s : ‖s‖ ≤ (σ + 1) * t := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h
    have hσt : σ ≤ σ * t := le_mul_of_one_le_right hs0.le him
    dsimp only [σ, t] at hσt ⊢
    linarith
  have hhead_le : ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ ≤
      (4 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) := by
    have hsum4 : ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ ≤ 4 * (K : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc (∑ k ∈ Finset.range K, ‖dyadicSpectralTriad b s k‖)
          ≤ ∑ _k ∈ Finset.range K, (4 : ℝ) :=
            Finset.sum_le_sum fun k _ => norm_dyadicSpectralTriad_le_four b hs0 hs1 k
        _ = 4 * (K : ℝ) := by simp [mul_comm]
    have hfac_ge1 : 1 ≤ (σ + 1) / σ := (one_le_div hs0).mpr (by linarith)
    calc ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖
        ≤ 4 * t ^ (1 / (1 + σ)) := by linarith
      _ ≤ 4 * (((σ + 1) / σ) * t ^ (1 / (1 + σ))) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (Real.rpow_nonneg ht_pos.le _) hfac_ge1) (by norm_num)
      _ = (4 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) := by ring
  have htail_core : (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ ≤
      (4 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) := by
    have h4s : 4 * ‖s‖ / σ ≤ (4 * (σ + 1) / σ) * t := by
      rw [div_le_iff₀ hs0]
      calc 4 * ‖s‖ ≤ 4 * ((σ + 1) * t) := by linarith
        _ = (4 * (σ + 1) / σ * t) * σ := by field_simp [hs0.ne']
    calc (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ
        ≤ ((4 * (σ + 1) / σ) * t) * t ^ (-σ / (1 + σ)) :=
          mul_le_mul h4s hocc_le (Real.rpow_nonneg (occupationWeight_pos _).le _) (by positivity)
      _ = (4 * (σ + 1) / σ) * (t ^ (1 : ℝ) * t ^ (-σ / (1 + σ))) := by
          rw [Real.rpow_one]; ring
      _ = (4 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) := by
          rw [← Real.rpow_add ht_pos]
          congr 2; field_simp [(by positivity : (0 : ℝ) < 1 + σ).ne']; ring
  have hpre_le : ‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖ ≤
      ((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1) := by
    have hden_pos : 0 < ‖1 - (2 : ℂ) ^ (1 - s)‖ := lt_of_lt_of_le h12_pos h12_lo
    exact div_le_div₀ (by positivity) h2_hi h12_pos h12_lo
  have htri : ‖jointSurvivingPartition b s‖ ≤
      ‖finiteTriadReading b K s‖ + triadTailBound K s := by
    have h1 := norm_add_le (finiteTriadReading b K s)
      (jointSurvivingPartition b s - finiteTriadReading b K s)
    rw [add_comm (finiteTriadReading b K s), sub_add_cancel] at h1
    exact h1.trans (add_le_add_right (norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne) _) |>
      fun h => by linarith [norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne,
        norm_add_le (finiteTriadReading b K s) (jointSurvivingPartition b s - finiteTriadReading b K s),
        show finiteTriadReading b K s + (jointSurvivingPartition b s - finiteTriadReading b K s) =
          jointSurvivingPartition b s by ring]
  have hftr_norm : ‖finiteTriadReading b K s‖ =
      (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖) *
        ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ := by
    rw [finiteTriadReading, norm_mul, norm_div]
  calc ‖jointSurvivingPartition b s‖
      ≤ ‖finiteTriadReading b K s‖ + triadTailBound K s := htri
    _ = (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖) *
          (‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ +
            (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ) := by
        rw [hftr_norm, triadTailBound]; ring
    _ ≤ (((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) *
          ((4 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) + (4 * (σ + 1) / σ) * t ^ (1 / (1 + σ))) :=
        mul_le_mul hpre_le (add_le_add hhead_le htail_core)
          (add_nonneg (norm_nonneg _)
            (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) hs0.le)
              (Real.rpow_nonneg (occupationWeight_pos _).le _)))
          (div_nonneg (by positivity) h12_pos.le)
    _ = (((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) *
          (8 * (σ + 1) / σ) * t ^ (1 / (1 + σ)) := by ring

/-- **Mandatory polynomial `lineLoss` collapse for UV-capped fourth-power witnesses at high ordinates:**
for `0 < Re s < 1`, `1 ≤ |Im s|`, and `Λ > 0`, every conserving rank-one omission `v : MissingWave`
beating `uvZeroThresholdFactor s Λ * lineLoss v.val` satisfies
`lineLoss v.val < (highOrdinateWitnessConstant s.re ^ 4 / Λ) * |s.im| ^ (-4 * s.re / (1 + s.re))`. -/
theorem capped_witness_lineLoss_lt_rpow_neg
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) {Λ : ℝ} (hΛ : 0 < Λ)
    (v : MissingWave)
    (hgt : uvZeroThresholdFactor s Λ * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4) :
    lineLoss v.val <
      (highOrdinateWitnessConstant s.re ^ 4 / Λ) * |s.im| ^ (-4 * s.re / (1 + s.re)) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  obtain ⟨h2_pos, h2_lo, _, h12_pos, _⟩ := factor_norm_bounds hs0 hs1
  have him_le_norm : t ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hub := norm_jointSurvivingPartition_le_rpow_im_uniform (missingWaveSpectrum v) hs0 hs1 him
  have hub4 := pow_le_pow_left₀ (norm_nonneg _) hub 4
  have hlo_base : ((2 : ℝ) ^ σ - 1) * (t / σ) ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) :=
    mul_le_mul h2_lo (div_le_div_of_nonneg_right him_le_norm hs0.le)
      (div_nonneg ht_pos.le hs0.le) (norm_nonneg _)
  have hlo4 : (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ 4 * (Λ * lineLoss v.val) ≤
      uvZeroThresholdFactor s Λ * lineLoss v.val := by
    have hp := pow_le_pow_left₀ (by positivity) hlo_base 4
    have heq : (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) ^ 4 * (Λ * lineLoss v.val) =
        uvZeroThresholdFactor s Λ * lineLoss v.val := by
      dsimp only [σ]; unfold uvZeroThresholdFactor; ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_right hp (mul_nonneg hΛ.le (line_loss_bounds v).1.le)
  have hlt_comb : (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ 4 * (Λ * lineLoss v.val) <
      ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) *
        (8 * (σ + 1) / σ) * t ^ (1 / (1 + σ))) ^ 4 :=
    (hlo4.trans_lt hgt).trans_le hub4
  have hden_pos : 0 < (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ 4 * Λ := by positivity
  rw [← mul_assoc] at hlt_comb
  have hdiv := (lt_div_iff₀' hden_pos).mpr hlt_comb
  refine hdiv.trans_eq ?_
  have ht_pow4 : (t ^ (1 / (1 + σ))) ^ 4 / t ^ 4 = t ^ (-4 * σ / (1 + σ)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul ht_pos.le, ← Real.rpow_natCast t 4,
      ← Real.rpow_sub ht_pos]
    congr 1; push_cast
    field_simp [(by positivity : (0 : ℝ) < 1 + σ).ne']; ring
  have hconst_eq :
      ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) * (8 * (σ + 1) / σ)) ^ 4 /
        ((((2 : ℝ) ^ σ - 1) / σ) ^ 4 * Λ) =
      highOrdinateWitnessConstant σ ^ 4 / Λ := by
    unfold highOrdinateWitnessConstant
    field_simp [hs0.ne', h2_pos.ne', h12_pos.ne', hΛ.ne']
  calc ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1) * (8 * (σ + 1) / σ) *
          t ^ (1 / (1 + σ))) ^ 4) / ((((2 : ℝ) ^ σ - 1) * (t / σ)) ^ 4 * Λ)
      = (((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) * (8 * (σ + 1) / σ)) ^ 4 /
          ((((2 : ℝ) ^ σ - 1) / σ) ^ 4 * Λ)) * ((t ^ (1 / (1 + σ))) ^ 4 / t ^ 4) := by
        rw [mul_pow, show ((2 : ℝ) ^ σ - 1) * (t / σ) = (((2 : ℝ) ^ σ - 1) / σ) * t by ring,
          mul_pow]
        field_simp [hs0.ne', h2_pos.ne', ht_pos.ne', hΛ.ne']
    _ = (highOrdinateWitnessConstant σ ^ 4 / Λ) * t ^ (-4 * σ / (1 + σ)) := by
        rw [hconst_eq, ht_pow4]

/-- **Mandatory polynomial `lineLoss` collapse for uncapped `(2 / Re s)`-power witnesses at high ordinates:**
for `0 < Re s < 1` and `1 ≤ |Im s|`, every conserving rank-one omission `v : MissingWave` beating
`chordZeroThresholdFactor s * lineLoss v.val` satisfies
`lineLoss v.val < highOrdinateWitnessConstant s.re ^ (2 / s.re) * |s.im| ^ (-2 / (1 + s.re))`. -/
theorem uncapped_witness_lineLoss_lt_rpow_neg
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|)
    (v : MissingWave)
    (hgt : chordZeroThresholdFactor s * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re)) :
    lineLoss v.val <
      highOrdinateWitnessConstant s.re ^ (2 / s.re) * |s.im| ^ (-2 / (1 + s.re)) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  have hexp_pos : 0 < 2 / σ := div_pos two_pos hs0
  obtain ⟨h2_pos, h2_lo, _, h12_pos, _⟩ := factor_norm_bounds hs0 hs1
  have him_le_norm : t ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hub := norm_jointSurvivingPartition_le_rpow_im_uniform (missingWaveSpectrum v) hs0 hs1 him
  have hub_p := Real.rpow_le_rpow (norm_nonneg _) hub hexp_pos.le
  have hlo_base : ((2 : ℝ) ^ σ - 1) * (t / σ) ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) :=
    mul_le_mul h2_lo (div_le_div_of_nonneg_right him_le_norm hs0.le)
      (div_nonneg ht_pos.le hs0.le) (norm_nonneg _)
  have hlo_p : (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ (2 / σ) * lineLoss v.val ≤
      chordZeroThresholdFactor s * lineLoss v.val :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hlo_base hexp_pos.le)
      (line_loss_bounds v).1.le
  have hlt_comb := (hlo_p.trans_lt hgt).trans_le hub_p
  have hden_pos : 0 < (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ (2 / σ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hdiv := (lt_div_iff₀' hden_pos).mpr hlt_comb
  refine hdiv.trans_eq ?_
  have hnum_split :
      ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) *
        (8 * (σ + 1) / σ) * t ^ (1 / (1 + σ))) ^ (2 / σ) =
      ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) * (8 * (σ + 1) / σ)) ^ (2 / σ) *
        t ^ (2 / (σ * (1 + σ))) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht_pos.le _), ← Real.rpow_mul ht_pos.le]
    congr 2; field_simp [hs0.ne', (by positivity : (0 : ℝ) < 1 + σ).ne']
  have hden_split :
      (((2 : ℝ) ^ σ - 1) * (t / σ)) ^ (2 / σ) =
      (((2 : ℝ) ^ σ - 1) / σ) ^ (2 / σ) * t ^ (2 / σ) := by
    rw [show ((2 : ℝ) ^ σ - 1) * (t / σ) = (((2 : ℝ) ^ σ - 1) / σ) * t by ring,
      Real.mul_rpow (by positivity) ht_pos.le]
  have hconst_div :
      ((((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) * (8 * (σ + 1) / σ)) ^ (2 / σ) /
        (((2 : ℝ) ^ σ - 1) / σ) ^ (2 / σ) =
      highOrdinateWitnessConstant σ ^ (2 / σ) := by
    rw [← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    unfold highOrdinateWitnessConstant
    field_simp [hs0.ne', h2_pos.ne', h12_pos.ne']
  have ht_div : t ^ (2 / (σ * (1 + σ))) / t ^ (2 / σ) = t ^ (-2 / (1 + σ)) := by
    rw [← Real.rpow_sub ht_pos]
    congr 1; field_simp [hs0.ne', (by positivity : (0 : ℝ) < 1 + σ).ne']; ring
  rw [hnum_split, hden_split, mul_div_mul_comm, hconst_div, ht_div]

/-- **High-ordinate operator-norm collapse of uncapped witness propagators:**
every conserving rank-one omission `v : MissingWave` beating `chordZeroThresholdFactor s` at
`0 < Re s < 1`, `1 ≤ |Im s|` satisfies
`‖criticalOperator^2 - (projected (omitLine v.val))^2‖ ≤ highOrdinateWitnessConstant s.re ^ (1 / s.re) * |s.im| ^ (-1 / (1 + s.re))`. -/
theorem uncapped_witness_operator_sq_dist_le_rpow_neg
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|)
    (v : MissingWave)
    (hgt : chordZeroThresholdFactor s * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re)) :
    ‖criticalOperator ^ 2 - (projected (omitLine v.val)) ^ 2‖ ≤
      highOrdinateWitnessConstant s.re ^ (1 / s.re) * |s.im| ^ (-1 / (1 + s.re)) := by
  have hcons := ((nonzero_line_conserves_iff v.val).mpr v.property).2
  obtain ⟨hop_le, hhs_le, _⟩ := norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect hcons
  change _ ≤ Real.sqrt (traceLoss (projected (omitLine v.val))) at hhs_le
  rw [traceLoss_omitLine] at hhs_le
  have hloss_lt := uncapped_witness_lineLoss_lt_rpow_neg hs0 hs1 him v hgt
  have hM_pos := highOrdinateWitnessConstant_pos hs0 hs1
  have ht_pos : 0 < |s.im| := zero_lt_one.trans_le him
  calc ‖criticalOperator ^ 2 - (projected (omitLine v.val)) ^ 2‖
      ≤ Real.sqrt (lineLoss v.val) := hop_le.trans hhs_le
    _ ≤ Real.sqrt (highOrdinateWitnessConstant s.re ^ (2 / s.re) * |s.im| ^ (-2 / (1 + s.re))) :=
        Real.sqrt_le_sqrt hloss_lt.le
    _ = (highOrdinateWitnessConstant s.re ^ (2 / s.re) *
          |s.im| ^ (-2 / (1 + s.re))) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ = highOrdinateWitnessConstant s.re ^ (1 / s.re) * |s.im| ^ (-1 / (1 + s.re)) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hM_pos.le _) (Real.rpow_nonneg ht_pos.le _),
          ← Real.rpow_mul hM_pos.le, ← Real.rpow_mul ht_pos.le]
        congr 2 <;> field_simp [hs0.ne', (by positivity : (0 : ℝ) < 1 + s.re).ne']

/-- **No finite bank of conserving rank-one omissions works across unbounded heights:**
for every `0 < σ < 1`, every `Λ > 0`, and every finite set `F : Finset MissingWave`, eventually as
`t → +∞` (even assuming `RiemannHypothesis`), **no** `v ∈ F` beats either `uvZeroThresholdFactor` or
`chordZeroThresholdFactor` at `σ ± i t`. -/
theorem eventually_no_finset_witness_at_high_ordinates
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {Λ : ℝ} (hΛ : 0 < Λ) (F : Finset MissingWave) :
    ∀ᶠ t : ℝ in atTop, ∀ v ∈ F,
      let sPos : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      let sNeg : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I
      ‖jointSurvivingPartition (missingWaveSpectrum v) sPos‖ ^ 4 ≤
        uvZeroThresholdFactor sPos Λ * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sNeg‖ ^ 4 ≤
        uvZeroThresholdFactor sNeg Λ * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sPos‖ ^ (2 / σ) ≤
        chordZeroThresholdFactor sPos * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sNeg‖ ^ (2 / σ) ≤
        chordZeroThresholdFactor sNeg * lineLoss v.val := by
  classical
  have hsingle : ∀ v : MissingWave, ∀ᶠ t : ℝ in atTop,
      let sPos : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      let sNeg : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I
      ‖jointSurvivingPartition (missingWaveSpectrum v) sPos‖ ^ 4 ≤
        uvZeroThresholdFactor sPos Λ * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sNeg‖ ^ 4 ≤
        uvZeroThresholdFactor sNeg Λ * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sPos‖ ^ (2 / σ) ≤
        chordZeroThresholdFactor sPos * lineLoss v.val ∧
      ‖jointSurvivingPartition (missingWaveSpectrum v) sNeg‖ ^ (2 / σ) ≤
        chordZeroThresholdFactor sNeg * lineLoss v.val := by
    intro v
    have hL_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
    have h1_neg : 0 < 4 * σ / (1 + σ) := by positivity
    have h2_neg : 0 < 2 / (1 + σ) := by positivity
    have hlim1 : Tendsto (fun t : ℝ =>
        (highOrdinateWitnessConstant σ ^ 4 / Λ) * t ^ (-4 * σ / (1 + σ))) atTop (𝓝 0) := by
      have hr : Tendsto (fun t : ℝ => t ^ (-4 * σ / (1 + σ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop h1_neg).congr fun t => by congr 1; ring
      simpa only [mul_zero] using hr.const_mul (highOrdinateWitnessConstant σ ^ 4 / Λ)
    have hlim2 : Tendsto (fun t : ℝ =>
        highOrdinateWitnessConstant σ ^ (2 / σ) * t ^ (-2 / (1 + σ))) atTop (𝓝 0) := by
      have hr : Tendsto (fun t : ℝ => t ^ (-2 / (1 + σ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop h2_neg).congr fun t => by congr 1; ring
      simpa only [mul_zero] using hr.const_mul (highOrdinateWitnessConstant σ ^ (2 / σ))
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hlim1.eventually (gt_mem_nhds hL_pos),
      hlim2.eventually (gt_mem_nhds hL_pos)] with t ht1 hub1 hub2
    set sPos : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    set sNeg : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I
    have hsPos_re : sPos.re = σ := by simp [sPos]
    have hsNeg_re : sNeg.re = σ := by simp [sNeg]
    have hsPos_im : |sPos.im| = t := by simp [sPos, abs_of_pos (zero_lt_one.trans_le ht1)]
    have hsNeg_im : |sNeg.im| = t := by simp [sNeg, abs_of_pos (zero_lt_one.trans_le ht1)]
    refine ⟨le_of_not_gt fun hgt => ?_, le_of_not_gt fun hgt => ?_,
      le_of_not_gt fun hgt => ?_, le_of_not_gt fun hgt => ?_⟩
    · have h := capped_witness_lineLoss_lt_rpow_neg (by rw [hsPos_re]; exact hσ0)
        (by rw [hsPos_re]; exact hσ1) (by rw [hsPos_im]; exact ht1) hΛ v hgt
      rw [hsPos_re, hsPos_im] at h; linarith
    · have h := capped_witness_lineLoss_lt_rpow_neg (by rw [hsNeg_re]; exact hσ0)
        (by rw [hsNeg_re]; exact hσ1) (by rw [hsNeg_im]; exact ht1) hΛ v hgt
      rw [hsNeg_re, hsNeg_im] at h; linarith
    · rw [← hsPos_re] at hgt
      have h := uncapped_witness_lineLoss_lt_rpow_neg (by rw [hsPos_re]; exact hσ0)
        (by rw [hsPos_re]; exact hσ1) (by rw [hsPos_im]; exact ht1) v hgt
      rw [hsPos_re, hsPos_im] at h; linarith
    · rw [← hsNeg_re] at hgt
      have h := uncapped_witness_lineLoss_lt_rpow_neg (by rw [hsNeg_re]; exact hσ0)
        (by rw [hsNeg_re]; exact hσ1) (by rw [hsNeg_im]; exact ht1) v hgt
      rw [hsNeg_re, hsNeg_im] at h; linarith
  induction F using Finset.induction_on with
  | empty => exact Eventually.of_forall fun _ _ hv => (Finset.notMem_empty _ hv).elim
  | @insert a S _ ih =>
    filter_upwards [hsingle a, ih] with t ha hS v hv
    rcases Finset.mem_insert.mp hv with rfl | hvS
    · exact ha
    · exact hS v hvS

/-! ### Part 3: Clean-height zero-exception horizontal lines in every `T^{24 / 25}` window above `84.5` -/

/-- **Zero-exception horizontal lines and uniform subsegment attenuation at Speiser-clean heights:**
at every height `γ ≥ 101` satisfying `RHTower.SpeiserUnshadowed γ`, both horizontal left-strip lines
`σ ± i γ` (`0 < σ < 1 / 2`, automatically satisfying `169 / 2 < |±γ|`) have **zero exceptions** for
both the UV-capped fourth-power finite-eigenvalue test and the uncapped `(2 / σ)`-power
finite-eigenvalue test, and every compact subsegment `[a, b] ⊂ (0, 1 / 2)` satisfies the uniform
horizontal lower bound `‖ζ(b + i γ)‖ ≤ ‖ζ(σ ± i γ)‖` (`0 < ‖ζ(b + i γ)‖`). -/
theorem speiserClean_full_left_strip_witnesses
    {γ : ℝ} (hγ : 101 ≤ γ) (hu : _root_.RHTower.SpeiserUnshadowed γ) :
    (∀ σ : ℝ, 0 < σ → σ < 1 / 2 →
      let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
      let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
      169 / 2 < |sPos.im| ∧ 169 / 2 < |sNeg.im| ∧
      (∀ {Λ : ℝ}, 0 < Λ →
        (∃ (hsPos : 0 < sPos.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne sPos hsPos Λ v ∧
            (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sPos <
              ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖) ∧
        (∃ (hsNeg : 0 < sNeg.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne sNeg hsNeg Λ v ∧
            (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sNeg <
              ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖)) ∧
      (∃ (v : MissingWave) (K : ℕ),
        (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) + triadTailBound K sPos <
          ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖) ∧
      (∃ (v : MissingWave) (K : ℕ),
        (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) + triadTailBound K sNeg <
          ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖)) ∧
    (∀ {a b : ℝ}, 0 < a → a ≤ b → b < 1 / 2 →
      0 < ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ ∧
      ∀ σ ∈ Icc a b,
        ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
          ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ∧
        ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
          ‖riemannZeta ((σ : ℂ) - (γ : ℂ) * Complex.I)‖) := by
  obtain ⟨hclean, hanti, _⟩ := _root_.RHTower.cleanLine_of_speiserUnshadowed hγ hu
  let tc₀ : ExceptionalTime := halfTurnClock
  refine ⟨fun σ hσ0 hσ_half => ?_, fun {a b} ha hab hb => ?_⟩
  · set sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
    set sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
    have hsPos_re : sPos.re = σ := by simp [sPos]
    have hsNeg_re : sNeg.re = σ := by simp [sNeg]
    have hsPos0 : 0 < sPos.re := by rw [hsPos_re]; exact hσ0
    have hsPos1 : sPos.re < 1 := by rw [hsPos_re]; linarith
    have hsNeg0 : 0 < sNeg.re := by rw [hsNeg_re]; exact hσ0
    have hsNeg1 : sNeg.re < 1 := by rw [hsNeg_re]; linarith
    have hζ_pos : riemannZeta sPos ≠ 0 := (hclean σ hσ0 hσ_half).1
    have hconj : conj sPos = sNeg := by apply Complex.ext <;> simp [sPos, sNeg]
    have hζ_neg : riemannZeta sNeg ≠ 0 := by
      intro hz
      apply hζ_pos
      have hc := congrArg (starRingEnd ℂ) hz
      rw [← hconj, riemannZeta_conj, RingHomCompTriple.comp_apply, RingHom.id_apply, map_zero] at hc
      exact hc
    have hne_pos : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast tc₀ 0 sPos u / (u : ℂ)) ≠ 0 :=
      fun hint0 => hζ_pos ((positive_zero_iff ⟨sPos, hsPos0⟩).mp
        ((continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero tc₀ 0 hsPos0 hsPos1.ne).mp hint0))
    have hne_neg : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast tc₀ 0 sNeg u / (u : ℂ)) ≠ 0 :=
      fun hint0 => hζ_neg ((positive_zero_iff ⟨sNeg, hsNeg0⟩).mp
        ((continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero tc₀ 0 hsNeg0 hsNeg1.ne).mp hint0))
    refine ⟨?_, ?_, fun {Λ} hΛ => ⟨?_, ?_⟩,
      (exists_finite_uncapped_witness_iff_integral_ne_zero tc₀ 0 hsPos0 hsPos1).mpr hne_pos,
      (exists_finite_uncapped_witness_iff_integral_ne_zero tc₀ 0 hsNeg0 hsNeg1).mpr hne_neg⟩
    · simp [sPos, abs_of_pos (by linarith : 0 < γ)]; linarith
    · simp [sNeg, abs_of_pos (by linarith : 0 < γ)]; linarith
    · obtain ⟨v, K, hv⟩ :=
        (exists_finite_capped_witness_iff_integral_ne_zero tc₀ 0 hsPos0 hsPos1 hΛ).mpr hne_pos
      exact ⟨hsPos0, v, K, hv⟩
    · obtain ⟨v, K, hv⟩ :=
        (exists_finite_capped_witness_iff_integral_ne_zero tc₀ 0 hsNeg0 hsNeg1 hΛ).mpr hne_neg
      exact ⟨hsNeg0, v, K, hv⟩
  · have hb0 : 0 < b := ha.trans_le hab
    have hpos_b : 0 < ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ :=
      norm_pos_iff.mpr (hclean b hb0 hb).1
    have hstrict := hanti a b ha hb
    refine ⟨hpos_b, fun σ hσ => ?_⟩
    have hsq_le : ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ ^ 2 ≤
        ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ ^ 2 := by
      rcases eq_or_lt_of_le hσ.2 with rfl | hlt
      · exact le_rfl
      · exact (hstrict hσ ⟨hab, le_rfl⟩ hlt).le
    have hle_pos : ‖riemannZeta ((b : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
        ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq_le
    have hconj_norm : ‖riemannZeta ((σ : ℂ) - (γ : ℂ) * Complex.I)‖ =
        ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := by
      have hc : conj ((σ : ℂ) + (γ : ℂ) * Complex.I) = (σ : ℂ) - (γ : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [← hc, riemannZeta_conj, Complex.norm_conj]
    exact ⟨hle_pos, hconj_norm ▸ hle_pos⟩

/-- **Positive-proportion zero-exception horizontal lines in every `T^{24 / 25}` window above `84.5`:**
for all sufficiently large `T` and every `T^{24 / 25} ≤ H ≤ T`, the set of heights
`γ ∈ [T + 3 / 2, T + H - 3 / 2]` on which **every** `σ ∈ [3001 / 24000, 1 / 2)` at `±γ` (`|±γ| > 84.5`)
simultaneously admits both capped (`∀ Λ > 0`) and uncapped finite-eigenvalue witnesses has Lebesgue
measure at least `(14 / 25) H - 3`. -/
theorem eventually_volume_clean_zero_exception_heights_window_ge :
    ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (14 / 25 * H - 3) ≤
        volume {γ ∈ Icc (T + 3 / 2) (T + H - 3 / 2) |
          169 / 2 < γ ∧
          ∀ σ : ℝ, 3001 / 24000 ≤ σ → σ < 1 / 2 →
            let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
            let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
            (∀ {Λ : ℝ}, 0 < Λ →
              (∃ (hsPos : 0 < sPos.re) (v : MissingWave) (K : ℕ),
                uvRegularRankOne sPos hsPos Λ v ∧
                  (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) +
                    triadTailBound K sPos <
                    ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖) ∧
              (∃ (hsNeg : 0 < sNeg.re) (v : MissingWave) (K : ℕ),
                uvRegularRankOne sNeg hsNeg Λ v ∧
                  (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) +
                    triadTailBound K sNeg <
                    ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖)) ∧
            (∃ (v : MissingWave) (K : ℕ),
              (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) +
                triadTailBound K sPos <
                ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖) ∧
            (∃ (v : MissingWave) (K : ℕ),
              (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) +
                triadTailBound K sNeg <
                ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖)} := by
  filter_upwards [_root_.RHTower.eventually_volume_speiserUnshadowed_window_ge,
    eventually_ge_atTop (101 : ℝ)] with T hvol hT101 H hH1 hH2
  refine (hvol H hH1 hH2).trans (measure_mono ?_)
  rintro γ ⟨hγ_mem, hu⟩
  have hγ101 : 101 ≤ γ := by linarith [hT101, hγ_mem.1]
  obtain ⟨hfull, _⟩ := speiserClean_full_left_strip_witnesses hγ101 hu
  refine ⟨hγ_mem, by linarith, fun σ hlo hhi => ?_⟩
  obtain ⟨_, _, hcap, hunc1, hunc2⟩ := hfull σ (by linarith) hhi
  exact ⟨hcap, hunc1, hunc2⟩

/-! ### Part 4: Sublinear power-saving exception bounds on dyadic left-strip boxes -/

/-- Dyadic left-strip exception box `{3001 / 24000 ≤ Re s ≤ σ₀ ∧ T ≤ |Im s| ≤ 2 T}` lacking a
finite-eigenvalue UV-capped rank-one witness at cap `Λ`. -/
def missingLeftWitnessBox (Λ σ₀ T : ℝ) : Set ℂ :=
  {s : ℂ | 3001 / 24000 ≤ s.re ∧ s.re ≤ σ₀ ∧ T ≤ |s.im| ∧ |s.im| ≤ 2 * T ∧
    ¬∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
      uvRegularRankOne s hs0 Λ v ∧
        (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
          ‖finiteTriadReading (missingWaveSpectrum v) K s‖}

private def mkXiZeroCopyLeft {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) (hz : riemannZeta z = 0) :
    _root_.RHTower.XiZeroCopy := by
  have hz_ne1 : z ≠ 1 := fun he => h1.ne (by rw [he, Complex.one_re])
  have hxi : _root_.RHTower.xi z = 0 := (_root_.RHTower.xi_eq_zero_iff h0 hz_ne1).mpr hz
  let s : _root_.RHTower.XiDivisorSupport :=
    ⟨z, _root_.RHTower.mem_xi_divisor_support_of_eq_zero hxi⟩
  have hpos := _root_.RHTower.xi_divisor_pos_on_support s
  exact ⟨s, ⟨0, by omega⟩⟩

/-- **Reflected zero-copy injection bound for dyadic left-strip exception boxes:**
for every `Λ > 0`, `σ₀ < 1 / 2`, and `T : ℝ`, `missingLeftWitnessBox Λ σ₀ T` is finite and has
cardinality at most `2 * (RHTower.zeroHeightBox (1 - σ₀) T).ncard`. -/
theorem ncard_missingLeftWitnessBox_le_two_mul_zeroHeightBox
    {Λ σ₀ : ℝ} (hΛ : 0 < Λ) (hσ₀ : σ₀ < 1 / 2) (T : ℝ) :
    (missingLeftWitnessBox Λ σ₀ T).Finite ∧
      (missingLeftWitnessBox Λ σ₀ T).ncard ≤
        2 * (_root_.RHTower.zeroHeightBox (1 - σ₀) T).ncard := by
  classical
  let tc₀ : ExceptionalTime := halfTurnClock
  set M := missingLeftWitnessBox Λ σ₀ T
  set B := _root_.RHTower.zeroHeightBox (1 - σ₀) T
  have hB_fin : B.Finite := _root_.RHTower.zeroHeightBox_finite (1 - σ₀) T
  have hz_of_mem : ∀ s ∈ M, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
    rintro s ⟨hlo, hhi, _, _, hno⟩
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast tc₀ 0 s u / (u : ℂ)) = 0 := by
      by_contra hne
      obtain ⟨v, K, hv⟩ :=
        (exists_finite_capped_witness_iff_integral_ne_zero tc₀ 0 hs0 hs1 hΛ).mpr hne
      exact hno ⟨hs0, v, K, hv⟩
    have hcs := (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero tc₀ 0 hs0 hs1.ne).mp hint0
    exact ⟨hs0, hs1, (positive_zero_iff ⟨s, hs0⟩).mp hcs⟩
  set Mpos := {s ∈ M | 0 ≤ s.im}
  set Mneg := {s ∈ M | s.im < 0}
  have hM_union : M = Mpos ∪ Mneg := by
    ext s
    simp only [Mpos, Mneg, mem_union, mem_setOf_eq]
    exact ⟨fun hs => (le_or_gt 0 s.im).imp (fun h => ⟨hs, h⟩) (fun h => ⟨hs, h⟩),
      fun h => h.elim And.left And.left⟩
  -- Positive-ordinate branch via `s ↦ conj (1 - s)`.
  have hrefl_pos : ∀ x : Mpos, 0 < (conj (1 - x.1)).re ∧ (conj (1 - x.1)).re < 1 ∧
      riemannZeta (conj (1 - x.1)) = 0 := by
    intro x
    obtain ⟨hs0, hs1, hzs⟩ := hz_of_mem x.1 x.2.1
    have hz1 := _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hzs hs0 hs1
    exact ⟨by simp; linarith, by simp; linarith, by rw [riemannZeta_conj, hz1, map_zero]⟩
  let ιPos : Mpos → _root_.RHTower.XiZeroCopy := fun x =>
    mkXiZeroCopyLeft (hrefl_pos x).1 (hrefl_pos x).2.1 (hrefl_pos x).2.2
  have hιPos_val : ∀ x : Mpos, ((ιPos x).1 : ℂ) = conj (1 - x.1) := fun _ => rfl
  have hιPos_inj : Function.Injective ιPos := by
    intro x y hxy
    have hc : conj (1 - x.1) = conj (1 - y.1) := by
      simpa only [hιPos_val] using congrArg (fun q : _root_.RHTower.XiZeroCopy => (q.1 : ℂ)) hxy
    have h1 : 1 - x.1 = 1 - y.1 := by simpa using congrArg (starRingEnd ℂ) hc
    exact Subtype.ext (by linear_combination -h1)
  have hιPos_mem : ∀ x : Mpos, ιPos x ∈ B := by
    intro x
    obtain ⟨⟨_, hre_hi, him_lo, him_hi, _⟩, him_nn⟩ := x.2
    rw [abs_of_nonneg him_nn] at him_lo him_hi
    dsimp only [B, _root_.RHTower.zeroHeightBox]
    rw [mem_setOf_eq, hιPos_val]
    exact ⟨by simp; linarith, by simpa using him_lo, by simpa using him_hi⟩
  -- Negative-ordinate branch via `s ↦ 1 - s`.
  have hrefl_neg : ∀ x : Mneg, 0 < (1 - x.1).re ∧ (1 - x.1).re < 1 ∧
      riemannZeta (1 - x.1) = 0 := by
    intro x
    obtain ⟨hs0, hs1, hzs⟩ := hz_of_mem x.1 x.2.1
    exact ⟨by simp; linarith, by simp; linarith,
      _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hzs hs0 hs1⟩
  let ιNeg : Mneg → _root_.RHTower.XiZeroCopy := fun x =>
    mkXiZeroCopyLeft (hrefl_neg x).1 (hrefl_neg x).2.1 (hrefl_neg x).2.2
  have hιNeg_val : ∀ x : Mneg, ((ιNeg x).1 : ℂ) = 1 - x.1 := fun _ => rfl
  have hιNeg_inj : Function.Injective ιNeg := by
    intro x y hxy
    have h1 : 1 - x.1 = 1 - y.1 := by
      simpa only [hιNeg_val] using congrArg (fun q : _root_.RHTower.XiZeroCopy => (q.1 : ℂ)) hxy
    exact Subtype.ext (by linear_combination -h1)
  have hιNeg_mem : ∀ x : Mneg, ιNeg x ∈ B := by
    intro x
    obtain ⟨⟨_, hre_hi, him_lo, him_hi, _⟩, him_neg⟩ := x.2
    rw [abs_of_neg him_neg] at him_lo him_hi
    dsimp only [B, _root_.RHTower.zeroHeightBox]
    rw [mem_setOf_eq, hιNeg_val]
    exact ⟨by simp; linarith, by simpa using him_lo, by simpa using him_hi⟩
  haveI : Finite B := hB_fin.to_subtype
  have hMpos_fin : Mpos.Finite :=
    Finite.of_injective (fun x : Mpos => (⟨ιPos x, hιPos_mem x⟩ : B)) fun x y h =>
      hιPos_inj (congrArg Subtype.val h)
  have hMneg_fin : Mneg.Finite :=
    Finite.of_injective (fun x : Mneg => (⟨ιNeg x, hιNeg_mem x⟩ : B)) fun x y h =>
      hιNeg_inj (congrArg Subtype.val h)
  have hM_fin : M.Finite := hM_union ▸ hMpos_fin.union hMneg_fin
  have hpos_le : Mpos.ncard ≤ B.ncard := by
    let Fpos : Finset Mpos := hMpos_fin.toFinset.attach.map
      ⟨fun x => ⟨x.1, hMpos_fin.mem_toFinset.mp x.2⟩,
        fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩
    have hsub : Fpos.image ιPos ⊆ hB_fin.toFinset := by
      intro q hq
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
      exact hB_fin.mem_toFinset.mpr (hιPos_mem x)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hιPos_inj, Finset.card_map, Finset.card_attach,
      ← Set.ncard_eq_toFinset_card Mpos hMpos_fin, ← Set.ncard_eq_toFinset_card B hB_fin] at hcard
    exact hcard
  have hneg_le : Mneg.ncard ≤ B.ncard := by
    let Fneg : Finset Mneg := hMneg_fin.toFinset.attach.map
      ⟨fun x => ⟨x.1, hMneg_fin.mem_toFinset.mp x.2⟩,
        fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)⟩
    have hsub : Fneg.image ιNeg ⊆ hB_fin.toFinset := by
      intro q hq
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
      exact hB_fin.mem_toFinset.mpr (hιNeg_mem x)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hιNeg_inj, Finset.card_map, Finset.card_attach,
      ← Set.ncard_eq_toFinset_card Mneg hMneg_fin, ← Set.ncard_eq_toFinset_card B hB_fin] at hcard
    exact hcard
  have hunion_le : M.ncard ≤ Mpos.ncard + Mneg.ncard := by
    rw [hM_union]
    exact Set.ncard_union_le Mpos Mneg
  exact ⟨hM_fin, by omega⟩

/-- **Global `4 / 3` linear-deficit sublinear exception bound (`o(T)`) across the left strip:**
for every critical-line margin `0 < θ ≤ 1 / 2` and slope slack `0 < δ < 4 / 3`, there exist
`D ≥ 0`, `B : ℕ`, and `T₀ ≥ 1` such that for all `T ≥ T₀`, all `Λ > 0`, and **all**
`σ₀ ≤ 1 / 2 - θ`, the total number of exceptions in `missingLeftWitnessBox Λ σ₀ T` is at most
`D * (1 + log T)^B * T^{1 - (4/3 - δ)(1/2 - σ₀)}` (`= o(T)`). -/
theorem exists_ncard_missingLeftWitnessBox_le_one_sub_four_thirds_uniform
    {θ δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hδ0 : 0 < δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ {Λ σ₀ : ℝ}, 0 < Λ → 0 ≤ σ₀ → σ₀ ≤ 1 / 2 - θ →
        ((missingLeftWitnessBox Λ σ₀ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ B * T ^ (1 - (4 / 3 - δ) * (1 / 2 - σ₀)) := by
  obtain ⟨D₀, hD₀, B, T₀, hT₀, hbox⟩ :=
    BiScaleUncertainty.ChebyshevGauge.exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
      hθ0 hθ1 hδ0
  refine ⟨2 * D₀, by positivity, B, T₀, hT₀, fun T hT {Λ σ₀} hΛ hσ₀_nn hσ₀_hi => ?_⟩
  have hσ₀_lt : σ₀ < 1 / 2 := by linarith
  obtain ⟨_, hcard2⟩ := ncard_missingLeftWitnessBox_le_two_mul_zeroHeightBox hΛ hσ₀_lt T
  have hcast : ((missingLeftWitnessBox Λ σ₀ T).ncard : ℝ) ≤
      2 * ((_root_.RHTower.zeroHeightBox (1 - σ₀) T).ncard : ℝ) := by exact_mod_cast hcard2
  have hb := hbox T hT (1 - σ₀) (by linarith) (by linarith)
  have hexp_eq : 1 - σ₀ - 1 / 2 = 1 / 2 - σ₀ := by ring
  rw [hexp_eq] at hb
  linarith

/-- **Density-Hypothesis `2 σ₀` power-saving exception bound on the outer left strip `σ₀ ≤ 1 / 6`:**
for every `0 < ε ≤ 1`, there exist `D ≥ 0` and `T₀ ≥ 1` such that for all `T ≥ T₀`, all `Λ > 0`,
and all `0 ≤ σ₀ ≤ 1 / 6` (covering `[3001 / 24000, 1 / 6]`), the total number of exceptions in
`missingLeftWitnessBox Λ σ₀ T` is at most
`D * (1 + log T)^{dhLogExponent ε + 4} * T^{(2 + ε) σ₀}` (`≤ O_ε(T^{1/3 + ε})`). -/
theorem exists_ncard_missingLeftWitnessBox_le_density_hypothesis
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ {Λ σ₀ : ℝ}, 0 < Λ → 0 ≤ σ₀ → σ₀ ≤ 1 / 6 →
        ((missingLeftWitnessBox Λ σ₀ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ (_root_.RHTower.dhLogExponent ε + 4) *
            T ^ ((2 + ε) * σ₀) := by
  obtain ⟨D₀, hD₀, T₀, hT₀, hdh⟩ :=
    _root_.RHTower.exists_zeroHeightBox_ncard_le_density_hypothesis hε0 hε1
  refine ⟨2 * D₀, by positivity, T₀, hT₀, fun T hT {Λ σ₀} hΛ hσ₀_nn hσ₀_hi => ?_⟩
  have hσ₀_lt : σ₀ < 1 / 2 := by linarith
  obtain ⟨_, hcard2⟩ := ncard_missingLeftWitnessBox_le_two_mul_zeroHeightBox hΛ hσ₀_lt T
  have hcast : ((missingLeftWitnessBox Λ σ₀ T).ncard : ℝ) ≤
      2 * ((_root_.RHTower.zeroHeightBox (1 - σ₀) T).ncard : ℝ) := by exact_mod_cast hcard2
  have hb := hdh T hT (1 - σ₀) (by linarith) (by linarith)
  have hexp_eq : 1 - (1 - σ₀) = σ₀ := by ring
  rw [hexp_eq] at hb
  linarith

#print axioms norm_dyadicSpectralTriad_le
#print axioms norm_jointSurviving_sub_finiteTriadReading_le
#print axioms tendsto_triadTailBound_zero
#print axioms exists_finite_capped_witness_iff_integral_ne_zero
#print axioms exists_finite_uncapped_witness_iff_integral_ne_zero
#print axioms rh_iff_exists_finite_eigenvalue_witness_above_eightyFour_and_half
#print axioms norm_jointSurvivingPartition_le_rpow_im_uniform
#print axioms capped_witness_lineLoss_lt_rpow_neg
#print axioms uncapped_witness_lineLoss_lt_rpow_neg
#print axioms uncapped_witness_operator_sq_dist_le_rpow_neg
#print axioms eventually_no_finset_witness_at_high_ordinates
#print axioms speiserClean_full_left_strip_witnesses
#print axioms eventually_volume_clean_zero_exception_heights_window_ge
#print axioms ncard_missingLeftWitnessBox_le_two_mul_zeroHeightBox
#print axioms exists_ncard_missingLeftWitnessBox_le_one_sub_four_thirds_uniform
#print axioms exists_ncard_missingLeftWitnessBox_le_density_hypothesis

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
