import GaloisForLFunctions.RHTower.CCMGammaAutocorrelationModulus
import GaloisForLFunctions.RHTower.CCMPrimeQuantileHeightLimit
import GaloisForLFunctions.RHTower.CCMActualPrimeBandMassLimit

/-!
# Uniform cancellation of the complete prime--continuum current

The signed current is little-o of the exponential aperture scale, uniformly
on the unit ball of physical mass plus higher Gamma energy. Neither degree
nor coefficients are restricted. The terminal interval keeps its original
orientation. This removes the leading exponential bound, but gives neither
an aperture-independent bound nor positivity of the complete Weil source.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem cell_bound (n : ℕ) (f : SoninL2) (B : ℝ)
    (hB : ∀ h ∈ Icc (ccmOutgoingPrimeQuantileBoundary n)
      (ccmOutgoingPrimeQuantileBoundary (n + 1)),
      |ccmActualHeadSymmetricAutocorrelation h f -
        ccmActualHeadSymmetricAutocorrelation (Real.log n) f| ≤ B) :
    |∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) * (ccmActualHeadSymmetricAutocorrelation h f -
        ccmActualHeadSymmetricAutocorrelation (Real.log n) f)| ≤
      criticalMellinAtomWeight n * B := by
  have hab := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hi : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2) * B) volume
      (ccmOutgoingPrimeQuantileBoundary n) (ccmOutgoingPrimeQuantileBoundary (n + 1)) :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2) * B).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun h => Real.exp (h / 2) * (ccmActualHeadSymmetricAutocorrelation h f -
      ccmActualHeadSymmetricAutocorrelation (Real.log n) f)) hab
    (Filter.Eventually.of_forall fun h hh => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hB h (Ioc_subset_Icc_self hh)) (Real.exp_pos _).le) hi
  rw [Real.norm_eq_abs, intervalIntegral.integral_mul_const,
    integral_exp_half_quantileCell_eq_atomWeight] at hh
  exact hh

/-- The finite old cells cost a fixed constant; every later cell has an
arbitrarily small coefficient, simultaneously for all complete Gamma heads. -/
theorem exists_ccmQuantileCurrent_uniform_small_mass_coefficient (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : SuzukiPositiveAperture)
      (u : CCMArchimedeanFormDomain a) (N : ℕ),
      |ccmOutgoingQuantileCellAutocorrelationCurrent N (ccmArchimedeanFormToAperture a u).1| ≤
        (B + ε * ccmOutgoingPrimeCumulative N) *
          (‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
            ccmActualHeadGammaHigherBinetModeEnergy (ccmArchimedeanFormToAperture a u).1) := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := exists_ccmGammaAutocorrelation_uniform_modulus ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_ccmOutgoingPrimeQuantileCell_near_log δ hδ)
  refine ⟨2 * ccmOutgoingPrimeCumulative M,
    mul_nonneg (by norm_num) (ccmOutgoingPrimeCumulative_nonneg M), ?_⟩
  intro a u N
  let f := ccmArchimedeanFormToAperture a u
  let E := ‖f‖ ^ 2 + ccmActualHeadGammaHigherBinetModeEnergy f.1
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (ccmActualHeadGammaHigherBinetModeEnergy_nonneg _)
  have hmass : ‖f‖ ^ 2 ≤ E := le_add_of_nonneg_right
    (ccmActualHeadGammaHigherBinetModeEnergy_nonneg _)
  let w := criticalMellinAtomWeight
  have hw (n : ℕ) : 0 ≤ w n := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hcell (n : ℕ) :
      |∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) * (ccmActualHeadSymmetricAutocorrelation h f.1 -
          ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1)| ≤
        ((if n < M then 2 * w n else 0) + ε * w n) * E := by
    by_cases hn : n < M
    · have hb := cell_bound n f.1 (2 * E) (fun h _ => by
        have h := (abs_sub (ccmActualHeadSymmetricAutocorrelation h f.1)
          (ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1)).trans
          (add_le_add (abs_ccmActualHeadSymmetricAutocorrelation_le_norm_sq h f.1)
            (abs_ccmActualHeadSymmetricAutocorrelation_le_norm_sq (Real.log n) f.1))
        change _ ≤ ‖f‖ ^ 2 + ‖f‖ ^ 2 at h
        linarith)
      simp only [if_pos hn]
      exact hb.trans (by dsimp only [w]; nlinarith [mul_nonneg (mul_nonneg hε.le (hw n)) hE])
    · have hb := cell_bound n f.1 (ε * E) (fun h hh =>
        hmod a u h (Real.log n) (hM n (by omega) h hh))
      simp only [if_neg hn, zero_add]
      calc
        _ ≤ w n * (ε * E) := hb
        _ = ε * w n * E := by ring
  have hprefix : (∑ n ∈ Finset.range N, if n < M then 2 * w n else 0) ≤
      2 * ccmOutgoingPrimeCumulative M := by
    calc
      _ = ∑ n ∈ (Finset.range N).filter (fun n => n < M), 2 * w n :=
        (Finset.sum_filter _ _).symm
      _ ≤ ∑ n ∈ Finset.range M, 2 * w n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
          (fun n _ _ => mul_nonneg (by norm_num) (hw n))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hs := (Finset.abs_sum_le_sum_abs
    (fun n : ℕ => ∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) * (ccmActualHeadSymmetricAutocorrelation h f.1 -
        ccmActualHeadSymmetricAutocorrelation (Real.log n) f.1)) (Finset.range N)).trans
    (Finset.sum_le_sum (fun n _ => hcell n))
  rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (add_le_add hprefix le_rfl) hE)

private theorem terminal_scaled_zero :
    Tendsto (fun a : ℝ => Real.exp (-a) *
      |criticalMellinCompletedError (2 * a) - 2 * (1 - Real.exp (-a))|) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => 2 * a) atTop atTop :=
    tendsto_id.const_mul_atTop two_pos
  have he : Tendsto (fun a : ℝ => Real.exp (-a) * criticalMellinCompletedError (2 * a))
      atTop (𝓝 0) := by
    convert tendsto_exp_neg_half_mul_criticalMellinCompletedError_atTop_zero.comp ht using 1
    ext a
    congr 2
    ring
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero
  have hl := he.sub ((hh.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hh)).const_mul 2)
  norm_num only [zero_mul, mul_zero, sub_zero] at hl
  have habs := hl.abs
  norm_num only [abs_zero] at habs
  apply habs.congr
  intro a
  rw [show Real.exp (-a) * criticalMellinCompletedError (2 * a) -
      2 * (Real.exp (-a) * (1 - Real.exp (-a))) =
      Real.exp (-a) * (criticalMellinCompletedError (2 * a) - 2 * (1 - Real.exp (-a))) by ring,
    abs_mul, abs_of_pos (Real.exp_pos _)]

/-- Complete signed prime--continuum cancellation, uniform on all orders and
all coefficients in the actual Gamma form domain. The exponential scale is
strictly improved, but the surviving bound is not aperture-independent. -/
theorem exists_ccmOutgoingCurrent_uniform_littleO_exp_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ (a : SuzukiPositiveAperture), A ≤ a.1 →
      ∀ u : CCMArchimedeanFormDomain a,
      |ccmActualHeadOutgoingQuantileAutocorrelationCurrent a (ccmArchimedeanFormToAperture a u)| ≤
        ε * Real.exp a.1 * (‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
          ccmActualHeadGammaHigherBinetModeEnergy (ccmArchimedeanFormToAperture a u).1) := by
  obtain ⟨B, hB, hcell⟩ := exists_ccmQuantileCurrent_uniform_small_mass_coefficient
    (ε / 24) (by positivity)
  have hheadlim : Tendsto (fun a : ℝ => Real.exp (-a) * (4 + 2 * B)) atTop (𝓝 0) :=
    by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (4 + 2 * B)
  have hhead : ∀ᶠ a : ℝ in atTop, Real.exp (-a) * (4 + 2 * B) < ε / 4 :=
    hheadlim (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  have hprime : ∀ᶠ a : ℝ in atTop, Real.exp (-a) * criticalMellinPrimeMass (2 * a) < 3 := by
    have hh := tendsto_exp_neg_mul_shifted_criticalMellinPrimeMass 0
    simp only [sub_zero, neg_zero, zero_div, Real.exp_zero, mul_one] at hh
    exact hh (Iio_mem_nhds (by norm_num))
  have hterminal : ∀ᶠ a : ℝ in atTop, Real.exp (-a) *
      |criticalMellinCompletedError (2 * a) - 2 * (1 - Real.exp (-a))| < ε / 8 :=
    terminal_scaled_zero (Iio_mem_nhds (by positivity))
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hhead.and (hprime.and hterminal))
  refine ⟨A, fun a ha u => ?_⟩
  obtain ⟨hh, hp, ht⟩ := hA a.1 ha
  let f := ccmArchimedeanFormToAperture a u
  let E := ‖f‖ ^ 2 + ccmActualHeadGammaHigherBinetModeEnergy f.1
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let M := criticalMellinPrimeMass (2 * a.1)
  let D := |criticalMellinCompletedError (2 * a.1) - 2 * (1 - Real.exp (-a.1))|
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (ccmActualHeadGammaHigherBinetModeEnergy_nonneg _)
  have hmass : ‖f‖ ^ 2 ≤ E := le_add_of_nonneg_right
    (ccmActualHeadGammaHigherBinetModeEnergy_nonneg _)
  have hs := hcell a u N
  rw [ccmOutgoingPrimeCumulative_floor_exp_succ_eq_primeMass] at hs
  have hr := abs_quantileTerminalAutocorrelation_le_completedErrorMismatch a f
  have harg : -((2 * a.1) / 2) = -a.1 := by ring
  rw [harg] at hr
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hmass (abs_nonneg _))
  have hbound : |ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f| ≤
      (4 + 2 * B + 2 * (ε / 24) * M + 2 * D) * E := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
    dsimp only
    have h₁ := abs_add_le (4 * ‖f‖ ^ 2)
      (2 * ccmOutgoingQuantileCellAutocorrelationCurrent N f.1)
    have h₂ := abs_add_le (4 * ‖f‖ ^ 2 +
      2 * ccmOutgoingQuantileCellAutocorrelationCurrent N f.1)
      (2 * ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1)
    rw [abs_of_nonneg (by positivity : 0 ≤ 4 * ‖f‖ ^ 2), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h₁
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h₂
    change _ ≤ (B + ε / 24 * M) * E at hs
    change _ ≤ D * E at hr'
    change _ ≤ _ at h₂
    dsimp only [ccmOutgoingQuantileCellAutocorrelationCurrent, N] at h₁ h₂ hs
    nlinarith only [h₁, h₂, hs, hr', hmass]
  have hcoef : (4 + 2 * B + 2 * (ε / 24) * M + 2 * D) ≤ ε * Real.exp a.1 := by
    have hh' := mul_lt_mul_of_pos_left hh (Real.exp_pos a.1)
    have hp' := mul_lt_mul_of_pos_left hp (Real.exp_pos a.1)
    have ht' := mul_lt_mul_of_pos_left ht (Real.exp_pos a.1)
    have hc : Real.exp a.1 * Real.exp (-a.1) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [← mul_assoc, hc, one_mul] at hh' hp' ht'
    change M < _ at hp'
    change D < _ at ht'
    nlinarith [mul_pos hε (Real.exp_pos a.1)]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef hE)

/-- Source-side lower bound obtained from the independently proved signed
cancellation estimate. The right side is the complete actual Weil quadratic. -/
theorem exists_ccmRestrictedWeilSource_ge_gamma_sub_littleO_exp (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ (a : SuzukiPositiveAperture), A ≤ a.1 →
      ∀ u : CCMArchimedeanFormDomain a,
      let f := ccmArchimedeanFormToAperture a u
      ccmActualHeadGammaHigherBinetModeEnergy f.1 + 2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 -
        ε * Real.exp a.1 * (‖f‖ ^ 2 + ccmActualHeadGammaHigherBinetModeEnergy f.1) ≤
          ccmRestrictedWeilSourceQuadratic a u := by
  obtain ⟨A, hA⟩ := exists_ccmOutgoingCurrent_uniform_littleO_exp_bound ε hε
  refine ⟨A, fun a ha u => ?_⟩
  have h := (abs_le.mp (hA a ha u)).1
  rw [ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation]
  dsimp only
  linarith only [h]

end RHTower
