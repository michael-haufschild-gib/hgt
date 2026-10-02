import GaloisForLFunctions.RHTower.LogPhaseFullPhysicalStationary
import GaloisForLFunctions.RHTower.ZetaChiModelOscillatoryError

/-!
# Complete physical stationary kernels of actual chi grades

Exact affine rescaling transports the full fixed-window logarithmic formula
to the literal conductor phase. The actual height cutoff supplies its derivative
and total variation, so the source oscillatory chi/model transfer retains every
physical term. The positive-grade capstone includes the exact conductor phase
and both complete remainders; no supplied asymptotic equality is used.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private theorem conductorPhase_scaled {a : ℝ} (ha : 0 < a) (k v : ℝ) :
    k * (a * (1 + v) - a * (1 + v) * Real.log (a * (1 + v) / (2 * Real.pi))) +
        (k * Real.log (a / (2 * Real.pi))) * (a * (1 + v)) =
      k * a + (k * a) * logPhaseProfile v := by
  by_cases hv : 1 + v = 0
  · have hv' : v = -1 := by linarith
    subst v
    simp [logPhaseProfile]
  · have hp : a / (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
    have hfactor : a * (1 + v) / (2 * Real.pi) = (a / (2 * Real.pi)) * (1 + v) := by ring
    rw [hfactor, Real.log_mul hp hv]
    unfold logPhaseProfile
    ring

private theorem full_integral_affine (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, f t) = (a : ℂ) * ∫ v : ℝ, f (a * (1 + v)) := by
  have hshift := integral_add_left_eq_self (μ := volume) (fun x : ℝ => f (a * x)) (1 : ℝ)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left f a
  rw [hscale] at hshift
  rw [abs_of_pos (inv_pos.mpr ha), Complex.real_smul] at hshift
  rw [hshift, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']

/-- Exact physical rescaling of the complete conductor-model kernel. -/
theorem integral_physical_conductorModel_eq {T a : ℝ} (ha : 0 < a) (k : ℝ) :
    (∫ t : ℝ, (bagPhysicalHeightWindow (t / T) : ℂ) *
      Complex.exp (I * ((k * (t - t * Real.log (t / (2 * Real.pi))) +
        (k * Real.log (a / (2 * Real.pi))) * t : ℝ) : ℂ))) =
      (a : ℂ) * Complex.exp (I * ((k * a : ℝ) : ℂ)) *
        ∫ v : ℝ, (bagPhysicalHeightWindow ((a / T) * (1 + v)) : ℂ) *
          Complex.exp (I * (((k * a) * logPhaseProfile v : ℝ) : ℂ)) := by
  rw [full_integral_affine _ ha]
  have hpoint (v : ℝ) : (bagPhysicalHeightWindow (a * (1 + v) / T) : ℂ) *
      Complex.exp (I * ((k * (a * (1 + v) - a * (1 + v) *
        Real.log (a * (1 + v) / (2 * Real.pi))) +
        (k * Real.log (a / (2 * Real.pi))) * (a * (1 + v)) : ℝ) : ℂ)) =
      Complex.exp (I * ((k * a : ℝ) : ℂ)) *
        ((bagPhysicalHeightWindow ((a / T) * (1 + v)) : ℂ) *
          Complex.exp (I * (((k * a) * logPhaseProfile v : ℝ) : ℂ))) := by
    rw [conductorPhase_scaled ha]
    have harg : a * (1 + v) / T = (a / T) * (1 + v) := by ring
    rw [harg, Complex.ofReal_add, mul_add I, Complex.exp_add]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  ring

/-- One source constant controls the literal complete conductor kernel for every positive grade
and physical saddle with the stated geometric scale. -/
theorem exists_physical_conductorModel_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ (T a k : ℝ), 0 < a →
      a / T ∈ Icc (1 / 2 : ℝ) 4 → 1 ≤ k * a →
      ‖(∫ t : ℝ, (bagPhysicalHeightWindow (t / T) : ℂ) *
          Complex.exp (I * ((k * (t - t * Real.log (t / (2 * Real.pi))) +
            (k * Real.log (a / (2 * Real.pi))) * t : ℝ) : ℂ))) -
        (a : ℂ) * (bagPhysicalHeightWindow (a / T) : ℂ) *
          (Real.sqrt (2 * Real.pi / (k * a)) : ℂ) *
          Complex.exp (I * ((k * a - Real.pi / 4 : ℝ) : ℂ))‖ ≤
        a * C / ((k * a) * Real.sqrt (k * a)) := by
  obtain ⟨C, hC, hbound⟩ := exists_full_physical_logPhase_stationary
  refine ⟨C, hC, ?_⟩
  intro T a k ha hp hka
  rw [integral_physical_conductorModel_eq ha]
  have hphase : Complex.exp (I * ((k * a - Real.pi / 4 : ℝ) : ℂ)) =
      Complex.exp (I * ((k * a : ℝ) : ℂ)) *
        Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I) := by
    have he : I * ((k * a - Real.pi / 4 : ℝ) : ℂ) =
        I * ((k * a : ℝ) : ℂ) + (((-(Real.pi / 4) : ℝ) : ℂ) * I) := by push_cast; ring
    rw [he, Complex.exp_add]
  rw [hphase]
  have hfactor : (a : ℂ) * Complex.exp (I * ((k * a : ℝ) : ℂ)) *
      (∫ v : ℝ, (bagPhysicalHeightWindow ((a / T) * (1 + v)) : ℂ) *
        Complex.exp (I * (((k * a) * logPhaseProfile v : ℝ) : ℂ))) -
      (a : ℂ) * (bagPhysicalHeightWindow (a / T) : ℂ) *
        (Real.sqrt (2 * Real.pi / (k * a)) : ℂ) *
        (Complex.exp (I * ((k * a : ℝ) : ℂ)) *
          Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)) =
      (a : ℂ) * Complex.exp (I * ((k * a : ℝ) : ℂ)) *
        ((∫ v : ℝ, (bagPhysicalHeightWindow ((a / T) * (1 + v)) : ℂ) *
          Complex.exp (I * (((k * a) * logPhaseProfile v : ℝ) : ℂ))) -
          (bagPhysicalHeightWindow (a / T) : ℂ) *
            (Real.sqrt (2 * Real.pi / (k * a)) : ℂ) *
            Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)) := by ring
  rw [hfactor, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have heNorm : ‖Complex.exp (I * ((k * a : ℝ) : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]
  rw [heNorm, mul_one]
  have hb := mul_le_mul_of_nonneg_left (hbound (a / T) hp (k * a) hka) ha.le
  simpa only [mul_div_assoc] using hb

/-- One source constant controls the variation of every rescaled physical height window. -/
theorem exists_physicalWindow_variation :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      (∀ t : ℝ, HasDerivAt (fun x : ℝ => (bagPhysicalHeightWindow (x / T) : ℂ))
        (((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)) t) ∧
      IntervalIntegrable (fun t : ℝ =>
        ((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)) volume T (2 * T) ∧
      ‖(bagPhysicalHeightWindow ((2 * T) / T) : ℂ)‖ +
        (∫ t in T..2 * T, ‖((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)‖) ≤ C := by
  have hW : ContDiff ℝ ∞ (fun x : ℝ => bagPhysicalHeightWindow x) := bagPhysicalHeightWindow.contDiff
  have hW' : ContDiff ℝ ∞ (deriv bagPhysicalHeightWindow) := (contDiff_infty_iff_deriv.mp hW).2
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hW'.continuous.continuousOn
  let M₁ := |M| + 1
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨1 + M₁, by positivity, ?_⟩
  intro T hT
  have hder (t : ℝ) : HasDerivAt (fun x : ℝ => (bagPhysicalHeightWindow (x / T) : ℂ))
      (((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)) t := by
    have hh := ((hW.differentiable (by simp) (t / T)).hasDerivAt).comp t
      ((hasDerivAt_id' t).div_const T)
    simpa only [Function.comp_apply, one_div, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_one, one_mul, div_eq_mul_inv] using! hh.ofReal_comp
  have hcont : Continuous (fun t : ℝ =>
      ((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)) :=
    (Complex.continuous_ofReal.comp (hW'.continuous.comp (continuous_id.div_const T))).div_const _
  refine ⟨hder, hcont.intervalIntegrable T (2 * T), ?_⟩
  have hpoint (t : ℝ) (ht : t ∈ Icc T (2 * T)) :
      ‖((deriv bagPhysicalHeightWindow (t / T) : ℝ) : ℂ) / (T : ℂ)‖ ≤ M₁ / T := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hT]
    apply div_le_div_of_nonneg_right _ hT.le
    have hm : t / T ∈ Icc (1 : ℝ) 2 := by
      constructor
      · exact (le_div_iff₀ hT).mpr (by simpa using ht.1)
      · exact (div_le_iff₀ hT).mpr ht.2
    have hb := hM (t / T) hm
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by dsimp [M₁]; linarith [le_abs_self M])
  have hint := intervalIntegral.integral_mono_on (show T ≤ 2 * T by linarith)
    (hcont.norm.intervalIntegrable T (2 * T))
    (intervalIntegrable_const (c := M₁ / T) (μ := volume)) hpoint
  have heval : (∫ t in T..2 * T, M₁ / T) = M₁ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [heval] at hint
  have hend : ‖(bagPhysicalHeightWindow ((2 * T) / T) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact bagPhysicalHeightWindow.le_one
  exact add_le_add hend hint

/-- The actual source physical window preserves the vanishing oscillatory chi/model error.
All amplitude and derivative inputs are supplied here, for every signed integer grade. -/
theorem exists_physicalWindow_chi_model_error :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T → ∀ k : ℤ, k ≠ 0 → ∀ freq : ℝ,
      ‖∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
        ((_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ k -
          _root_.RHTower.bourgainOscillation (Real.pi / 4) ^ k *
            Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
          Complex.exp (((freq * t : ℝ) : ℂ) * I))‖ ≤
        ((6 / Real.sqrt (|(k : ℝ)| / (100 * T))) * (52 * |(k : ℝ)| / T)) * C := by
  obtain ⟨C, hC, hvar⟩ := exists_physicalWindow_variation
  refine ⟨C, hC, ?_⟩
  intro T hT k hk freq
  obtain ⟨hder, hint, hb⟩ := hvar T (by linarith)
  have he := _root_.RHTower.norm_integral_complexAmplitude_mul_zetaChi_integerGrade_sub_model_le
    hT le_rfl (show T ≤ 2 * T by linarith) le_rfl hk freq (fun t _ => hder t) hint
  exact he.trans (mul_le_mul_of_nonneg_left hb (by positivity))

private theorem physicalWindow_interval_eq (f : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) * f t) =
      ∫ t : ℝ, (bagPhysicalHeightWindow (t / T) : ℂ) * f t := by
  rw [intervalIntegral.integral_of_le (by linarith : T ≤ 2 * T)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hw : bagPhysicalHeightWindow (t / T) = 0 := by
    apply bagPhysicalHeightWindow.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist (t / T) (3 / 2 : ℝ)
    rw [Real.dist_eq]
    by_cases htl : t ≤ T
    · have hratio : t / T ≤ 1 := (div_le_iff₀ hT).mpr (by simpa using htl)
      linarith [neg_le_abs (t / T - 3 / 2)]
    · have htr : 2 * T < t := by
        by_contra hh
        exact ht ⟨lt_of_not_ge htl, le_of_not_gt hh⟩
      have hratio : 2 ≤ t / T := (le_div_iff₀ hT).mpr htr.le
      linarith [le_abs_self (t / T - 3 / 2)]
  simp only [hw, Complex.ofReal_zero, zero_mul]

private theorem continuous_conductorProfile :
    Continuous (fun t : ℝ => t - t * Real.log (t / (2 * Real.pi))) := by
  have hc := continuous_id.sub
    ((Real.continuous_mul_log.comp (continuous_id.div_const (2 * Real.pi))).const_mul (2 * Real.pi))
  apply hc.congr
  intro t
  dsimp only [Function.comp_apply, id_eq, Pi.sub_apply]
  field_simp [Real.pi_ne_zero]

/-- The literal oriented stationary main, including the exact integer-grade conductor phase. -/
def physicalChiStationaryMain (T a : ℝ) (k : ℤ) : ℂ :=
  _root_.RHTower.bourgainOscillation (Real.pi / 4) ^ k * (a : ℂ) *
    (bagPhysicalHeightWindow (a / T) : ℂ) *
    (Real.sqrt (2 * Real.pi / ((k : ℝ) * a)) : ℂ) *
    Complex.exp (I * (((k : ℝ) * a - Real.pi / 4 : ℝ) : ℂ))

/-- The complete actual chi kernel has a uniform source-derived stationary formula.
Both physical cutoff transitions, the full nonstationary complement, and the oscillatory
actual/model error are retained. No analytic model equality or amplitude bound is a premise. -/
theorem exists_complete_physical_chi_positiveGrade_kernel :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ T a : ℝ, 4 ≤ T → 0 < a →
      a / T ∈ Icc (1 / 2 : ℝ) 4 → ∀ k : ℤ, 0 < k →
      ‖(∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
          (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ k *
            Complex.exp (((((k : ℝ) * Real.log (a / (2 * Real.pi))) * t : ℝ) : ℂ) * I))) -
        physicalChiStationaryMain T a k‖ ≤
          a * Cm / (((k : ℝ) * a) * Real.sqrt ((k : ℝ) * a)) +
            ((6 / Real.sqrt (|(k : ℝ)| / (100 * T))) * (52 * |(k : ℝ)| / T)) * Ce := by
  obtain ⟨Cm, hCm, hmodel⟩ := exists_physical_conductorModel_stationary
  obtain ⟨Ce, hCe, herror⟩ := exists_physicalWindow_chi_model_error
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro T a hT ha hp k hk
  have hT0 : 0 < T := by linarith
  have hk1 : (1 : ℤ) ≤ k := by omega
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hka : 1 ≤ (k : ℝ) * a := by
    have har := (le_div_iff₀ hT0).mp hp.1
    nlinarith [mul_nonneg (sub_nonneg.mpr hkr) ha.le]
  let freq : ℝ := (k : ℝ) * Real.log (a / (2 * Real.pi))
  let u : ℂ := _root_.RHTower.bourgainOscillation (Real.pi / 4) ^ k
  let f : ℝ → ℂ := fun t => (bagPhysicalHeightWindow (t / T) : ℂ) *
    (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ k *
      Complex.exp (((freq * t : ℝ) : ℂ) * I))
  let g : ℝ → ℂ := fun t => u * ((bagPhysicalHeightWindow (t / T) : ℂ) *
    Complex.exp (I * (((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) + freq * t : ℝ) : ℂ)))
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_zpow, _root_.RHTower.norm_bourgainOscillation, one_zpow]
  have hW : Continuous (fun t : ℝ => (bagPhysicalHeightWindow (t / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const T))
  have hf : Continuous f := hW.mul (_root_.RHTower.continuous_zetaChiCriticalGradeIntegrand k freq)
  have hg : Continuous g := continuous_const.mul (hW.mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_conductorProfile.const_mul (k : ℝ)).add (continuous_id.const_mul freq))))))
  have hdiff : (∫ t in T..2 * T, f t) - (∫ t in T..2 * T, g t) =
      ∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
        ((_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ k -
          _root_.RHTower.bourgainOscillation (Real.pi / 4) ^ k *
            Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
          Complex.exp (((freq * t : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [f, g, u]
    rw [Complex.ofReal_add, mul_add I, Complex.exp_add]
    have hcomm (x : ℝ) : I * (x : ℂ) = (x : ℂ) * I := mul_comm _ _
    simp_rw [hcomm]
    ring
  have hgfull : (∫ t in T..2 * T, g t) =
      u * ∫ t : ℝ, (bagPhysicalHeightWindow (t / T) : ℂ) *
        Complex.exp (I * (((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) + freq * t : ℝ) : ℂ)) := by
    change (∫ t in T..2 * T, u * _) = _
    rw [intervalIntegral.integral_const_mul, physicalWindow_interval_eq _ hT0]
  have hmain : ‖(∫ t in T..2 * T, g t) - physicalChiStationaryMain T a k‖ ≤
      a * Cm / (((k : ℝ) * a) * Real.sqrt ((k : ℝ) * a)) := by
    rw [hgfull]
    unfold physicalChiStationaryMain
    change ‖u * _ - u * (a : ℂ) * (bagPhysicalHeightWindow (a / T) : ℂ) *
      (Real.sqrt (2 * Real.pi / ((k : ℝ) * a)) : ℂ) *
      Complex.exp (I * (((k : ℝ) * a - Real.pi / 4 : ℝ) : ℂ))‖ ≤ _
    simp only [mul_assoc]
    rw [← mul_sub, norm_mul, hu, one_mul]
    simpa only [freq, mul_assoc] using hmodel T a (k : ℝ) ha hp hka
  change ‖(∫ t in T..2 * T, f t) - physicalChiStationaryMain T a k‖ ≤ _
  calc
    _ ≤ ‖(∫ t in T..2 * T, f t) - (∫ t in T..2 * T, g t)‖ +
        ‖(∫ t in T..2 * T, g t) - physicalChiStationaryMain T a k‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((6 / Real.sqrt (|(k : ℝ)| / (100 * T))) * (52 * |(k : ℝ)| / T)) * Ce +
        a * Cm / (((k : ℝ) * a) * Real.sqrt ((k : ℝ) * a)) := by
      apply add_le_add _ hmain
      rw [hdiff]
      exact herror T hT k hk.ne' freq
    _ = _ := by ring

end GaloisForLFunctions.RHTower
