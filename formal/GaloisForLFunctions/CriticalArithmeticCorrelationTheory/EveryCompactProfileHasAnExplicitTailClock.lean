import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmicTailMassGivesAnExplicitSpectralFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasSubexponentialConductorFloors
import GaloisForLFunctions.RHTower.PaleyWienerPoissonMajorant

/-!
# An explicit spectral clock for every compact profile

The compact Fourier transform has an integrable standard Cauchy-weighted logarithm.
Its remaining logarithmic mass sets a radius growing faster than every linear scale,
while the spectral tail throughout that radius dominates each exponential in the scale.
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

/-- The logarithm of the actual spectral density is integrable against the standard
Cauchy weight, including profiles whose Fourier transform has real zeros. -/
theorem integrable_shellSpectrum_standard_log_weight {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    Integrable (fun u : ℝ => Real.log (shellSpectrum φ u) / (1 + u ^ 2)) := by
  obtain ⟨x, y, hy, hlog⟩ := exists_integrable_shellSpectrum_log_weight hφ hsupp hM
  let s : ℝ := 2 * Real.pi
  let D : ℝ := 2 * s ^ 2 + 2 * x ^ 2 + y ^ 2 + 1
  let w := fun u : ℝ => ((s * u - x) ^ 2 + y ^ 2) / (1 + u ^ 2)
  have hwcont : Continuous w := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro u
    positivity
  have hwbound : ∀ᵐ u : ℝ, ‖w u‖ ≤ D := by
    filter_upwards [] with u
    have hw : 0 < 1 + u ^ 2 := by positivity
    have hv : 0 < (s * u - x) ^ 2 + y ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)
    have hden : (s * u - x) ^ 2 + y ^ 2 ≤ D * (1 + u ^ 2) := by
      have hp : 0 ≤ (2 * x ^ 2 + y ^ 2 + 1) * u ^ 2 := by positivity
      dsimp only [D]
      nlinarith only [sq_nonneg (s * u + x), hp, sq_nonneg s]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hv hw)]
    exact (div_le_iff₀ hw).mpr hden
  apply (hlog.mul_bdd hwcont.aestronglyMeasurable hwbound).congr
  exact ae_of_all _ fun u => by
    have hv : (s * u - x) ^ 2 + y ^ 2 ≠ 0 :=
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)).ne'
    change Real.log (shellSpectrum φ u) / ((s * u - x) ^ 2 + y ^ 2) *
      (((s * u - x) ^ 2 + y ^ 2) / (1 + u ^ 2)) = _
    field_simp

/-- The logarithmic tail of the actual compact profile gives an explicit radius
whose ratio to the input scale tends to infinity. -/
def compactProfileTailClock (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  min (t * Real.log t) (logarithmicTailClock (shellSpectrum φ) t)

theorem compactProfileTailClock_le_mul_log (φ : ℝ → ℝ) (t : ℝ) :
    compactProfileTailClock φ t ≤ t * Real.log t := min_le_left _ _

theorem compactProfileTailClock_le_sq (φ : ℝ → ℝ) (t : ℝ) :
    compactProfileTailClock φ t ≤ t ^ 2 := (min_le_right _ _).trans (min_le_left _ _)

theorem tendsto_compactProfileTailClock_div_atTop (φ : ℝ → ℝ) :
    Tendsto (fun t : ℝ => compactProfileTailClock φ t / t) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_mul_le_logarithmicTailClock (shellSpectrum φ)
    (show 0 < max K 1 from zero_lt_one.trans_le (le_max_right _ _)),
    Real.tendsto_log_atTop.eventually_ge_atTop K, eventually_gt_atTop (0 : ℝ)]
    with t hclock hlog ht
  apply (le_div_iff₀ ht).mpr
  refine le_min ?_ ?_
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlog ht.le
  · exact (mul_le_mul_of_nonneg_right (le_max_left K 1) ht.le).trans hclock

/-- Every nonzero compact `C²` profile retains each exponential floor on its explicit
superlinear radius. The clock itself is independent of the chosen decay exponent. -/
theorem eventually_exp_le_shell_tail_up_to_explicit_clock {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ c : ℝ, 0 ≤ c → c ≤ compactProfileTailClock φ t →
      Real.exp (-ε * t) ≤ ∫ u in Ioi c, shellSpectrum φ u := by
  have hh := eventually_exp_le_tail_up_to_logarithmicTailClock
    (fun u => shellSpectrum_nonneg u) (shellSpectrum_pos_ae hφ hsupp hM)
    (integrableOn_shellSpectrum_Ioi hφ (HasCompactSupport.intro isCompact_Icc hsupp) 0)
    (integrable_shellSpectrum_standard_log_weight hφ hsupp hM) hε
  filter_upwards [hh] with t ht
  intro c hc hclock
  exact ht c hc (hclock.trans (min_le_right _ _))

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

/-- The same explicit clock retains any exponential floor uniformly in the conductor.
Its scale depends on the profile, while its choice is independent of the exponent. -/
theorem eventually_exp_le_completedConductorEnergy_up_to_explicit_clock {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ c : ℝ, 0 < c → c ≤ compactProfileTailClock φ t →
      ∀ m : ℕ, 0 < m → Real.exp (-ε * t) ≤ completedConductorEnergy φ c m := by
  let a := 2 / (∫ u, φ u ^ 2)
  have ha : 0 < a := div_pos zero_lt_two hM
  filter_upwards [eventually_exp_le_shell_tail_up_to_explicit_clock hφ hsupp hM
    (div_pos hε zero_lt_two), eventually_ge_atTop (-2 * Real.log a / ε)]
    with t htail ht
  intro c hc hclock m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcm : c / m ≤ compactProfileTailClock φ t := (div_le_self hc.le hm1).trans hclock
  have hcm0 : 0 ≤ c / m := div_nonneg hc.le (Nat.cast_nonneg _)
  have hsmall : Real.exp (-(ε / 2) * t) ≤ a := by
    have hh := (div_le_iff₀ hε).mp ht
    apply (Real.exp_le_exp.mpr (show -(ε / 2) * t ≤ Real.log a by nlinarith only [hh])).trans_eq
    exact Real.exp_log ha
  calc
    Real.exp (-ε * t) = Real.exp (-(ε / 2) * t) * Real.exp (-(ε / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ a * Real.exp (-(ε / 2) * t) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ ≤ a * ∫ u in Ioi (c / m), shellSpectrum φ u :=
      mul_le_mul_of_nonneg_left (htail _ hcm0 hcm) ha.le
    _ ≤ _ := completedConductorEnergy_ge_rescaled_tail hφ hsupp hM hc hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
