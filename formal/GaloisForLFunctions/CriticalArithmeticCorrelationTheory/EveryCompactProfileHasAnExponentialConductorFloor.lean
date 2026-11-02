import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompactEntireDensityRetainsExponentialTails
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryNonzeroProfileHasAPositiveConductorFloor

/-!
# Exponential conductor floors for arbitrary compact profiles

The entire extension of the spectral density has a universal exponential type. Its positive
mass on a distant interval gives a quantitative uncertainty bound, including profiles with
real Fourier zeros. The first coprime repayment term transfers this to conductor energy.
-/

noncomputable section

open MeasureTheory Set Filter Zeta23
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

set_option autoImplicit false

private theorem compact_profile_fourier_eq {φ : ℝ → ℝ}
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

private theorem compact_profile_fourier_neg {φ : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) (t : ℝ) :
    HTGeometry.compactFourier (fun x : ℝ => (φ x : ℂ)) 0 1 (-(t : ℂ)) =
      conj (HTGeometry.compactFourier (fun x : ℝ => (φ x : ℂ)) 0 1 (t : ℂ)) := by
  rw [compact_profile_fourier_eq hsupp, compact_profile_fourier_eq hsupp]
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

private theorem exists_entire_shell_density {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ t : ℝ, H (t : ℂ) = (shellSpectrum φ t : ℂ)) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, ‖H z‖ ≤ M * Real.exp (4 * Real.pi * ‖z‖) := by
  let F := HTGeometry.compactFourier (fun x : ℝ => (φ x : ℂ)) 0 1
  have hcx : Continuous (fun x : ℝ => (φ x : ℂ)) := Complex.continuous_ofReal.comp hφ
  have hF : Differentiable ℂ F := HTGeometry.differentiable_compactFourier hcx 0 1
  obtain ⟨L, hL⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcx.continuousOn
  let M := max L 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFM (z : ℂ) : ‖F z‖ ≤ M * Real.exp ‖z‖ := by
    have hs := HTGeometry.norm_compactFourier_le (f := fun x : ℝ => (φ x : ℂ))
      (M := M) (by norm_num : (0 : ℝ) ≤ 1)
      (fun x hx => (hL x (uIoc_subset_uIcc hx)).trans (le_max_left _ _)) z
    simp only [abs_zero, abs_one, max_eq_right zero_le_one, one_mul, sub_zero, mul_one] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (Complex.abs_im_le_norm z)) hM.le)
  let H := fun z : ℂ => F ((2 * Real.pi : ℂ) * z) * F (-((2 * Real.pi : ℂ) * z))
  have hlin : Differentiable ℂ (fun z : ℂ => (2 * Real.pi : ℂ) * z) := by fun_prop
  have hH : Differentiable ℂ H := (hF.comp hlin).mul (hF.comp hlin.neg)
  refine ⟨H, hH, ?_, M ^ 2, sq_pos_of_pos hM, ?_⟩
  · intro t
    have hcast : (2 * Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) := by
      push_cast
      rfl
    dsimp only [H]
    rw [hcast]
    change F ((2 * Real.pi * t : ℝ) : ℂ) * F (-((2 * Real.pi * t : ℝ) : ℂ)) = _
    dsimp only [F]
    rw [compact_profile_fourier_neg hsupp, Complex.mul_conj']
    rw [compact_profile_fourier_eq hsupp]
    rw [← Complex.ofReal_pow]
    rfl
  · intro z
    have hn : ‖(2 * Real.pi : ℂ) * z‖ = 2 * Real.pi * ‖z‖ := by
      rw [norm_mul]
      have heq : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      ‖H z‖ = ‖F ((2 * Real.pi : ℂ) * z)‖ * ‖F (-((2 * Real.pi : ℂ) * z))‖ := norm_mul _ _
      _ ≤ (M * Real.exp ‖(2 * Real.pi : ℂ) * z‖) *
          (M * Real.exp ‖-((2 * Real.pi : ℂ) * z)‖) :=
        mul_le_mul (hFM _) (hFM _) (norm_nonneg _) (by positivity)
      _ = M ^ 2 * Real.exp (4 * Real.pi * ‖z‖) := by
        rw [norm_neg, hn]
        rw [show (M * Real.exp (2 * Real.pi * ‖z‖)) *
            (M * Real.exp (2 * Real.pi * ‖z‖)) =
            M ^ 2 * (Real.exp (2 * Real.pi * ‖z‖) * Real.exp (2 * Real.pi * ‖z‖)) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-- The spectral tail of every nonzero compact `C²` profile has an exponential lower bound
with a rate independent of the profile. Real Fourier zeros are allowed. -/
theorem exists_universal_exponential_shell_tail :
    ∃ b : ℝ, 0 < b ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 ≤ c →
        a * Real.exp (-b * c) ≤ ∫ t in Ioi c, shellSpectrum φ t := by
  obtain ⟨b, hb, hbound⟩ := exists_exponential_lower_tail_of_entire_nonnegative
    (show 0 ≤ 4 * Real.pi by positivity)
  refine ⟨b, hb, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨H, hH, hshell, M, hMpos, hgrowth⟩ := exists_entire_shell_density hφ.continuous hsupp
  have hre (t : ℝ) : (H (t : ℂ)).re = shellSpectrum φ t := by
    rw [hshell, Complex.ofReal_re]
  have him (t : ℝ) : (H (t : ℂ)).im = 0 := by rw [hshell, Complex.ofReal_im]
  have hpos (t : ℝ) : 0 ≤ (H (t : ℂ)).re := by rw [hre]; exact shellSpectrum_nonneg t
  obtain ⟨z, -, hz⟩ := exists_shellSpectrum_pos_gt hφ hsupp hM 0
  have hHz : 0 < (H (z : ℂ)).re := by rwa [hre]
  have hcompact : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  have hint (c : ℝ) : IntegrableOn (fun t : ℝ => (H (t : ℂ)).re) (Ioi c) := by
    simpa only [hre] using integrableOn_shellSpectrum_Ioi hφ hcompact c
  obtain ⟨a, ha, htail⟩ := hbound H hH him hpos ⟨M, hMpos, hgrowth⟩ ⟨z, hHz⟩ hint
  exact ⟨a, ha, by simpa only [hre] using htail⟩

private theorem completedConductorEnergy_ge_rescaled_tail {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    2 / (∫ x, φ x ^ 2) * ∫ t in Ioi (c / m), shellSpectrum φ t ≤
      completedConductorEnergy φ c m := by
  let M := ∫ x, φ x ^ 2
  have hsum := hasSum_completedConductorEnergy hφ hsupp hM hc hm
  have hterm (n : ℕ) : 0 ≤ (if Nat.Coprime m (n + 1) then
      2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0) := by
    split_ifs
    · refine mul_nonneg (mul_nonneg (div_nonneg zero_le_two
        (mul_nonneg hM.le (Nat.cast_nonneg _))) (div_nonneg (Nat.cast_nonneg _) (by positivity))) ?_
      exact setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
    · exact le_rfl
  have hfirst := le_hasSum hsum 0 fun n _ => hterm n
  simp only [Nat.coprime_one_right_eq_true, if_true, Nat.cast_zero, zero_add, one_mul,
    div_one] at hfirst
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr htot_le
  have htail : 0 ≤ ∫ t in Ioi (c / m), shellSpectrum φ t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  calc
    2 / M * ∫ t in Ioi (c / m), shellSpectrum φ t ≤
        2 / M * (((m : ℝ) / m.totient) * ∫ t in Ioi (c / m), shellSpectrum φ t) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left htail hratio) (div_nonneg zero_le_two hM.le)
    _ = 2 / (M * m.totient) * m * ∫ t in Ioi (c / m), shellSpectrum φ t := by field_simp
    _ ≤ _ := hfirst

/-- The exponential floor improves with conductor: its decay variable is `c/m`, the lower
endpoint of the first coprime spectral repayment. The rate is universal across profiles. -/
theorem exists_universal_exponential_completedConductor_floor :
    ∃ b : ℝ, 0 < b ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 < c → ∀ m : ℕ, 0 < m →
        a * Real.exp (-b * (c / m)) ≤ completedConductorEnergy φ c m := by
  obtain ⟨b, hb, htail⟩ := exists_universal_exponential_shell_tail
  refine ⟨b, hb, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a, ha, hbound⟩ := htail φ hφ hsupp hM
  refine ⟨2 / (∫ x, φ x ^ 2) * a, mul_pos (div_pos zero_lt_two hM) ha, ?_⟩
  intro c hc m hm
  calc
    (2 / (∫ x, φ x ^ 2) * a) * Real.exp (-b * (c / m)) =
        2 / (∫ x, φ x ^ 2) * (a * Real.exp (-b * (c / m))) := mul_assoc _ _ _
    _ ≤ 2 / (∫ x, φ x ^ 2) * ∫ t in Ioi (c / m), shellSpectrum φ t :=
      mul_le_mul_of_nonneg_left (hbound _ (div_nonneg hc.le (Nat.cast_nonneg _)))
        (div_nonneg zero_le_two hM.le)
    _ ≤ _ := completedConductorEnergy_ge_rescaled_tail hφ hsupp hM hc hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
