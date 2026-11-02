import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.IntegrableLogarithmsForceSubexponentialTails
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasAnExponentialConductorFloor
import GaloisForLFunctions.RHTower.PaleyWienerPoissonMajorant

/-!
# Every compact profile has subexponential conductor floors

The compact Fourier transform has an integrable weighted logarithm and only a null set of
real zeros. Its spectral tail therefore dominates every exponential. The first coprime
repayment term transfers this lower bound to each completed conductor energy.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

private theorem suzukiFourier_eq_paperFT (f : ℝ → ℂ) (z : ℂ) :
    _root_.RHTower.suzukiEntireFourier f z = paperFT f z := rfl

private theorem shellSpectrum_eq_suzukiFourier (φ : ℝ → ℝ) (t : ℝ) :
    shellSpectrum φ t =
      ‖_root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ))
        ((2 * Real.pi * t : ℝ) : ℂ)‖ ^ 2 := by
  rw [suzukiFourier_eq_paperFT]
  rfl

private theorem compact_profile_suzuki_facts {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    Integrable (fun u : ℝ => (φ u : ℂ)) ∧
      (∀ u : ℝ, (φ u : ℂ) ≠ 0 → |u| ≤ 1) ∧
      Differentiable ℂ (_root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ))) ∧
      ∃ t : ℝ, _root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ)) (t : ℂ) ≠ 0 := by
  have hfsupp : ∀ u : ℝ, u ∉ Icc 0 1 → (φ u : ℂ) = 0 := by
    intro u hu
    simp only [hsupp u hu, Complex.ofReal_zero]
  have hfc : HasCompactSupport (fun u : ℝ => (φ u : ℂ)) :=
    HasCompactSupport.intro isCompact_Icc hfsupp
  have hfi : Integrable (fun u : ℝ => (φ u : ℂ)) :=
    (Complex.continuous_ofReal.comp hφ.continuous).integrable_of_hasCompactSupport hfc
  have hbound (u : ℝ) (hu : (φ u : ℂ) ≠ 0) : |u| ≤ 1 := by
    have huI : u ∈ Icc (0 : ℝ) 1 := by
      by_contra hnot
      exact hu (hfsupp u hnot)
    rw [abs_of_nonneg huI.1]
    exact huI.2
  have hcenter : GaloisForLFunctions.HTGeometry.FourierZeroFlip.SupportedIn 1
      (fun u : ℝ => (φ u : ℂ)) := by
    intro u hu
    by_contra hne
    exact hu (abs_le.mp (hbound u hne))
  have hF := _root_.RHTower.differentiable_suzukiEntireFourier zero_le_one hfi hcenter
  refine ⟨hfi, hbound, hF, ?_⟩
  obtain ⟨t, -, ht⟩ := exists_shellSpectrum_pos_gt hφ hsupp hM 0
  rw [shellSpectrum_eq_suzukiFourier] at ht
  refine ⟨2 * Real.pi * t, ?_⟩
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at ht
  exact lt_irrefl _ ht

private theorem shellSpectrum_pos_ae {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∀ᵐ t : ℝ, 0 < shellSpectrum φ t := by
  obtain ⟨-, -, hF, t₀, ht₀⟩ := compact_profile_suzuki_facts hφ hsupp hM
  have hzeros := _root_.RHTower.countable_setOf_eq_zero_of_differentiable hF ht₀
  have hinj : Function.Injective (fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ)) := by
    intro u v huv
    exact (mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0))
      (Complex.ofReal_injective huv)
  have hnull : volume {t : ℝ |
      _root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ))
        ((2 * Real.pi * t : ℝ) : ℂ) = 0} = 0 :=
    (hzeros.preimage hinj).measure_zero volume
  have hne : ∀ᵐ t : ℝ, _root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ))
      ((2 * Real.pi * t : ℝ) : ℂ) ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  filter_upwards [hne] with t ht
  rw [shellSpectrum_eq_suzukiFourier]
  exact sq_pos_of_pos (norm_pos_iff.mpr ht)

private theorem exists_integrable_shellSpectrum_log_weight {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ x y : ℝ, 0 < y ∧ Integrable
      (fun t : ℝ => Real.log (shellSpectrum φ t) / ((2 * Real.pi * t - x) ^ 2 + y ^ 2)) := by
  obtain ⟨hfi, hbound, hF, x, hx⟩ := compact_profile_suzuki_facts hφ hsupp hM
  let F := _root_.RHTower.suzukiEntireFourier (fun u : ℝ => (φ u : ℂ))
  have hcont : Continuous (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    hF.continuous.comp (by fun_prop)
  have hx0 : F ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hcont.continuousAt.eventually_ne hx0)
  let y := r / 2
  have hy : 0 < y := div_pos hr zero_lt_two
  have hyball : y ∈ Metric.ball (0 : ℝ) r := by
    change dist y 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_pos hy]
    dsimp only [y]
    linarith only [hr]
  have hlog := (_root_.RHTower.log_norm_le_poissonMajorant zero_le_one hfi hbound x hy
    (hball hyball)).1
  have hscaled : Integrable (fun t : ℝ =>
      Real.log ‖F ((2 * Real.pi * t : ℝ) : ℂ)‖ / ((2 * Real.pi * t - x) ^ 2 + y ^ 2)) :=
    (integrable_comp_mul_left_iff _ (by positivity : 2 * Real.pi ≠ 0)).mpr hlog
  refine ⟨x, y, hy, ?_⟩
  apply (hscaled.const_mul 2).congr
  exact ae_of_all _ fun t => by
    dsimp only
    rw [shellSpectrum_eq_suzukiFourier, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp only [F]
    ring

/-- Every exponential is eventually a lower bound for the positive spectral tail of a
nonzero compact profile, even when its Fourier transform has real zeros. -/
theorem eventually_exp_le_shell_tail {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in atTop, Real.exp (-ε * c) ≤ ∫ t in Ioi c, shellSpectrum φ t := by
  obtain ⟨x, y, hy, hlog⟩ := exists_integrable_shellSpectrum_log_weight hφ hsupp hM
  have hcompact : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  exact eventually_exp_le_tail_of_integrable_log_weight (fun t => shellSpectrum_nonneg t)
    (shellSpectrum_pos_ae hφ hsupp hM) (integrableOn_shellSpectrum_Ioi hφ hcompact 0) hy hlog hε

private theorem exists_subexponential_shell_tail_of_eventually {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε)
    (hevent : ∀ᶠ c : ℝ in atTop,
      Real.exp (-ε * c) ≤ ∫ t in Ioi c, shellSpectrum φ t) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 ≤ c →
      a * Real.exp (-ε * c) ≤ ∫ t in Ioi c, shellSpectrum φ t := by
  obtain ⟨C, hC⟩ := eventually_atTop.mp hevent
  obtain ⟨b, hb, hbound⟩ := exists_universal_exponential_shell_tail
  obtain ⟨a₀, ha₀, htail⟩ := hbound φ hφ hsupp hM
  let a := min 1 (a₀ * Real.exp (-b * max C 0))
  have ha : 0 < a := lt_min zero_lt_one (mul_pos ha₀ (Real.exp_pos _))
  refine ⟨a, ha, ?_⟩
  intro c hc
  by_cases hlarge : C ≤ c
  · exact (mul_le_of_le_one_left (Real.exp_pos _).le (min_le_left _ _)).trans (hC c hlarge)
  · have hcC : c ≤ max C 0 := (lt_of_not_ge hlarge).le.trans (le_max_left _ _)
    calc
      a * Real.exp (-ε * c) ≤ a := mul_le_of_le_one_right ha.le
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hc))
      _ ≤ a₀ * Real.exp (-b * max C 0) := min_le_right _ _
      _ ≤ a₀ * Real.exp (-b * c) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcC (neg_nonpos.mpr hb.le))) ha₀.le
      _ ≤ _ := htail c hc

/-- A profile-dependent prefactor makes each exponential tail floor valid at every
nonnegative overlap. The decay rate can be chosen arbitrarily small. -/
theorem exists_subexponential_shell_tail {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 ≤ c →
      a * Real.exp (-ε * c) ≤ ∫ t in Ioi c, shellSpectrum φ t :=
  exists_subexponential_shell_tail_of_eventually hφ hsupp hM hε
    (eventually_exp_le_shell_tail hφ hsupp hM hε)

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

/-- Every prescribed exponential rate gives a conductor-uniform floor, with decay
variable `c/m` supplied by the first coprime spectral repayment. -/
theorem exists_subexponential_completedConductor_floor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 < c → ∀ m : ℕ, 0 < m →
      a * Real.exp (-ε * (c / m)) ≤ completedConductorEnergy φ c m := by
  obtain ⟨a, ha, htail⟩ := exists_subexponential_shell_tail hφ hsupp hM hε
  refine ⟨2 / (∫ u, φ u ^ 2) * a, mul_pos (div_pos zero_lt_two hM) ha, ?_⟩
  intro c hc m hm
  calc
    (2 / (∫ u, φ u ^ 2) * a) * Real.exp (-ε * (c / m)) =
        2 / (∫ u, φ u ^ 2) * (a * Real.exp (-ε * (c / m))) := mul_assoc _ _ _
    _ ≤ 2 / (∫ u, φ u ^ 2) * ∫ t in Ioi (c / m), shellSpectrum φ t :=
      mul_le_mul_of_nonneg_left (htail _ (div_nonneg hc.le (Nat.cast_nonneg _)))
        (div_nonneg zero_le_two hM.le)
    _ ≤ _ := completedConductorEnergy_ge_rescaled_tail hφ hsupp hM hc hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
