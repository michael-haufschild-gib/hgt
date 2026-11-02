import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor
import GaloisForLFunctions.HTGeometry.CompactFourierIntegrableEntire

/-!
# Every nonzero compact profile has a positive conductor floor

Fourier uniqueness prevents the spectrum of a nonzero compact profile from vanishing on any
half-line. Its integrated tail is therefore strictly positive, even when the Fourier transform
has real zeros. The first coprime repayment term gives a common positive conductor-energy floor
throughout every bounded positive-overlap interval.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

private theorem compactFourier_unit_eq_paperFT {φ : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) (z : ℂ) :
    HTGeometry.compactFourier (fun x : ℝ => (φ x : ℂ)) 0 1 z =
      paperFT (fun x : ℝ => (φ x : ℂ)) z := by
  unfold HTGeometry.compactFourier paperFT
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (0 : ℝ) 1)
    (fun x hx => by simp only [hsupp x hx, Complex.ofReal_zero, zero_mul])]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by dsimp only; rw [mul_assoc]

/-- Every real spectral half-line contains a positive point for a nonzero compact profile. -/
theorem exists_shellSpectrum_pos_gt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) (c : ℝ) :
    ∃ t : ℝ, c < t ∧ 0 < shellSpectrum φ t := by
  by_contra hnone
  push Not at hnone
  have hzero (t : ℝ) (ht : c < t) :
      paperFT (fun x : ℝ => (φ x : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ) = 0 := by
    apply norm_eq_zero.mp
    have hs := hnone t ht
    change ‖paperFT (fun x : ℝ => (φ x : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ)‖ ^ 2 ≤ 0 at hs
    nlinarith only [hs, norm_nonneg
      (paperFT (fun x : ℝ => (φ x : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ))]
  have hfsupp : ∀ x : ℝ, x ∉ Icc 0 1 → (φ x : ℂ) = 0 := by
    intro x hx
    simp only [hsupp x hx, Complex.ofReal_zero]
  have hfc : HasCompactSupport (fun x : ℝ => (φ x : ℂ)) :=
    HasCompactSupport.intro isCompact_Icc hfsupp
  have hfi : Integrable (fun x : ℝ => (φ x : ℂ)) :=
    (Complex.continuous_ofReal.comp hφ.continuous).integrable_of_hasCompactSupport hfc
  let a : ℝ := 2 * Real.pi * (c + 1) + 1
  have hvanish : ∀ᵐ (ξ : ℝ) ∂volume.restrict (Ioo (a - 1) (a + 1)),
      HTGeometry.compactFourier (fun x : ℝ => (φ x : ℂ)) 0 1 (ξ : ℂ) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ξ hξ
    rw [compactFourier_unit_eq_paperFT hsupp]
    have hpi : 0 < 2 * Real.pi := by positivity
    have ht : c < ξ / (2 * Real.pi) := by
      rw [lt_div_iff₀ hpi]
      have hlo := hξ.1
      dsimp only [a] at hlo
      nlinarith only [hlo, Real.pi_pos]
    have hscale : 2 * Real.pi * (ξ / (2 * Real.pi)) = ξ := by
      field_simp
    simpa only [hscale] using hzero (ξ / (2 * Real.pi)) ht
  have hae := HTGeometry.ae_eq_zero_of_compactFourier_vanishing
    (by norm_num : (0 : ℝ) ≤ 1) hfi hfsupp (by norm_num : (0 : ℝ) < 1) hvanish
  have hsq : (fun x : ℝ => φ x ^ 2) =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have hz : φ x = 0 := Complex.ofReal_eq_zero.mp hx
    simp only [hz, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]
  have hmass : (∫ x, φ x ^ 2) = 0 := by
    rw [integral_congr_ae hsq]
    simp only [Pi.zero_apply, integral_zero]
  exact hM.ne' hmass

/-- A nonzero compact `C²` profile has strictly positive integrated spectrum on every half-line. -/
theorem integral_shellSpectrum_pos {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) (c : ℝ) :
    0 < ∫ t in Ioi c, shellSpectrum φ t := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨t, ht, hpos⟩ := exists_shellSpectrum_pos_gt hφ hsupp hM c
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => shellSpectrum_nonneg t)
    (integrableOn_shellSpectrum_Ioi hφ hφc c)]
  exact ((continuous_shellSpectrum hφ.continuous hφc).isOpen_support.inter isOpen_Ioi).measure_pos
    volume ⟨t, hpos.ne', ht⟩

/-- Every nonzero compact `C²` profile has a common positive conductor floor on bounded overlap. -/
theorem exists_uniform_completedConductor_floor {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) (hM : 0 < ∫ x, φ x ^ 2) (K : ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ c : ℝ, 0 < c → c ≤ K →
      ∀ m : ℕ, 0 < m → e ≤ completedConductorEnergy φ c m := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  refine ⟨2 / (∫ x, φ x ^ 2) * ∫ t in Ioi K, shellSpectrum φ t,
    mul_pos (div_pos zero_lt_two hM) (integral_shellSpectrum_pos hφ hsupp hM K), ?_⟩
  intro c hc hcK m hm
  have htail : (∫ t in Ioi K, shellSpectrum φ t) ≤ ∫ t in Ioi c, shellSpectrum φ t :=
    setIntegral_mono_set (integrableOn_shellSpectrum_Ioi hφ hφc c)
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Ioi_subset_Ioi hcK))
  exact (mul_le_mul_of_nonneg_left htail (div_nonneg zero_le_two hM.le)).trans
    (completedConductorEnergy_ge_shellTail hφ hsupp hM hc hm)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
