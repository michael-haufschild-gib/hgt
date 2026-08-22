import GaloisForLFunctions.HTGeometry.OscillatoryIntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The damped power amplitude against an oscillation

For `Re s > 0` and a damping `ε ≥ 0` the amplitude `t ↦ t^{-s} e^{-εt}` has, on `[a, A]` with
`0 < a ≤ A`, boundary values bounded by `a^{-Re s}` and total derivative mass bounded by
`‖s‖ a^{-Re s}/Re s + a^{-Re s}`, **uniformly in `ε`**.  One integration by parts against `e^{itL}`
therefore gives

`‖∫_a^A t^{-s} e^{-εt} e^{itL} dt‖ ≤ (3 a^{-Re s} + ‖s‖ a^{-Re s}/Re s) / L`,

uniformly in `ε ≥ 0` and in the upper limit `A`.  This is the estimate that lets the Abel
regularisation `ε ↓ 0` be interchanged with the improper limit `A → ∞` in the classical
Fourier–Mellin evaluation of a power (Burnol, arXiv:math/0203120, via his C. R. note [6]).

## Main results

* `hasDerivAt_dampedPowerAmp`
* `norm_integral_dampedPowerAmp_le`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set intervalIntegral

noncomputable section

/-- The damped power amplitude `t ↦ t^{-s} e^{-εt}`. -/
def dampedPowerAmp (s : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-s) * Complex.exp (-(ε : ℂ) * (t : ℂ))

/-- Its derivative. -/
def dampedPowerAmp' (s : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  (-s * (t : ℂ) ^ (-s - 1) - (ε : ℂ) * (t : ℂ) ^ (-s)) * Complex.exp (-(ε : ℂ) * (t : ℂ))

theorem hasDerivAt_dampedPowerAmp {t : ℝ} (ht : 0 < t) {s : ℂ} (hs0 : (-s) ≠ 0) (ε : ℝ) :
    HasDerivAt (dampedPowerAmp s ε) (dampedPowerAmp' s ε t) t := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht.ne' hs0
  have hlin : HasDerivAt (fun x : ℝ => -(ε : ℂ) * (x : ℂ)) (-(ε : ℂ)) t := by
    have hbase : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa using hbase.const_mul (-(ε : ℂ))
  have h2 : HasDerivAt (fun x : ℝ => Complex.exp (-(ε : ℂ) * (x : ℂ)))
      (Complex.exp (-(ε : ℂ) * (t : ℂ)) * (-(ε : ℂ))) t := hlin.cexp
  have := h1.mul h2
  refine this.congr_deriv ?_
  rw [dampedPowerAmp']
  ring

theorem norm_dampedPowerAmp {t : ℝ} (ht : 0 < t) (s : ℂ) (ε : ℝ) :
    ‖dampedPowerAmp s ε t‖ = t ^ (-s.re) * Real.exp (-(ε * t)) := by
  rw [dampedPowerAmp, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re,
    Complex.norm_exp]
  congr 1
  simp

theorem norm_dampedPowerAmp_le {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 < a) (hat : a ≤ t)
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖dampedPowerAmp s ε t‖ ≤ a ^ (-s.re) := by
  rw [norm_dampedPowerAmp ht s ε]
  have hexp : Real.exp (-(ε * t)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ ε * t := mul_nonneg hε ht.le
    linarith
  have hpow : t ^ (-s.re) ≤ a ^ (-s.re) := by
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ha]
    refine Real.exp_le_exp.2 ?_
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha hat
    nlinarith [mul_nonneg (sub_nonneg.2 hlog) hs.le]
  have hnn : (0:ℝ) ≤ t ^ (-s.re) := Real.rpow_nonneg ht.le _
  calc t ^ (-s.re) * Real.exp (-(ε * t)) ≤ t ^ (-s.re) * 1 := by
        exact mul_le_mul_of_nonneg_left hexp hnn
    _ = t ^ (-s.re) := mul_one _
    _ ≤ a ^ (-s.re) := hpow

theorem norm_dampedPowerAmp'_le {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 < a) (hat : a ≤ t)
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖dampedPowerAmp' s ε t‖
      ≤ ‖s‖ * t ^ (-s.re - 1) + a ^ (-s.re) * (ε * Real.exp (-(ε * t))) := by
  have hexpnorm : ‖Complex.exp (-(ε : ℂ) * (t : ℂ))‖ = Real.exp (-(ε * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hexp1 : Real.exp (-(ε * t)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ ε * t := mul_nonneg hε ht.le
    linarith
  have hexp0 : (0:ℝ) ≤ Real.exp (-(ε * t)) := (Real.exp_pos _).le
  have hre : (-s - 1).re = -s.re - 1 := by simp
  have hc1 : ‖(-s : ℂ) * (t : ℂ) ^ (-s - 1)‖ = ‖s‖ * t ^ (-s.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht, hre]
  have hc2 : ‖((ε : ℂ)) * (t : ℂ) ^ (-s)‖ = ε * t ^ (-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hε, Complex.neg_re]
  have hpow : t ^ (-s.re) ≤ a ^ (-s.re) := by
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ha]
    refine Real.exp_le_exp.2 ?_
    have hlog : Real.log a ≤ Real.log t := Real.log_le_log ha hat
    nlinarith [mul_nonneg (sub_nonneg.2 hlog) hs.le]
  rw [dampedPowerAmp', norm_mul, hexpnorm]
  have hsplit : ‖(-s : ℂ) * (t : ℂ) ^ (-s - 1) - (ε : ℂ) * (t : ℂ) ^ (-s)‖
      ≤ ‖s‖ * t ^ (-s.re - 1) + ε * t ^ (-s.re) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hc1, hc2]
  have hnn1 : (0:ℝ) ≤ ‖s‖ * t ^ (-s.re - 1) := by positivity
  have hnn2 : (0:ℝ) ≤ ε * t ^ (-s.re) := by positivity
  calc ‖(-s : ℂ) * (t : ℂ) ^ (-s - 1) - (ε : ℂ) * (t : ℂ) ^ (-s)‖ * Real.exp (-(ε * t))
      ≤ (‖s‖ * t ^ (-s.re - 1) + ε * t ^ (-s.re)) * Real.exp (-(ε * t)) := by
        exact mul_le_mul_of_nonneg_right hsplit hexp0
    _ = ‖s‖ * t ^ (-s.re - 1) * Real.exp (-(ε * t))
          + (ε * Real.exp (-(ε * t))) * t ^ (-s.re) := by ring
    _ ≤ ‖s‖ * t ^ (-s.re - 1) * 1 + (ε * Real.exp (-(ε * t))) * a ^ (-s.re) := by
        gcongr
    _ = ‖s‖ * t ^ (-s.re - 1) + a ^ (-s.re) * (ε * Real.exp (-(ε * t))) := by ring

theorem continuousOn_dampedPowerAmp' {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) {s : ℂ} (ε : ℝ) :
    ContinuousOn (dampedPowerAmp' s ε) (Set.uIcc a A) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have htpos : 0 < t := by
    rw [Set.uIcc_of_le haA] at ht
    exact lt_of_lt_of_le ha ht.1
  have h1 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s - 1)) t :=
    Complex.continuousAt_ofReal_cpow_const t (-s - 1) (Or.inr htpos.ne')
  have h2 : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
    Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr htpos.ne')
  have h3 : ContinuousAt (fun x : ℝ => Complex.exp (-(ε : ℂ) * (x : ℂ))) t := by
    fun_prop
  exact (((h1.const_mul (-s)).sub (h2.const_mul (ε : ℂ))).mul h3)

theorem integral_norm_dampedPowerAmp'_le {a A : ℝ} (ha : 0 < a) (haA : a ≤ A)
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ t in a..A, ‖dampedPowerAmp' s ε t‖)
      ≤ ‖s‖ * a ^ (-s.re) / s.re + a ^ (-s.re) := by
  have hs0 : (-s) ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h] at hs
    simp at hs
  set g : ℝ → ℝ := fun t => ‖s‖ * t ^ (-s.re - 1) + a ^ (-s.re) * (ε * Real.exp (-(ε * t)))
    with hg
  have hcontF : ContinuousOn (fun t : ℝ => ‖dampedPowerAmp' s ε t‖) (Set.uIcc a A) :=
    (continuousOn_dampedPowerAmp' ha haA (s := s) ε).norm
  have hcontpow : ContinuousOn (fun t : ℝ => t ^ (-s.re - 1)) (Set.uIcc a A) := by
    refine ContinuousOn.rpow_const continuousOn_id ?_
    intro t ht
    left
    rw [Set.uIcc_of_le haA] at ht
    exact (lt_of_lt_of_le ha ht.1).ne'
  have hcontg : ContinuousOn g (Set.uIcc a A) := by
    refine ContinuousOn.add (continuousOn_const.mul hcontpow) ?_
    fun_prop
  have hmono : (∫ t in a..A, ‖dampedPowerAmp' s ε t‖) ≤ ∫ t in a..A, g t := by
    refine intervalIntegral.integral_mono_on haA hcontF.intervalIntegrable
      hcontg.intervalIntegrable ?_
    intro t ht
    exact norm_dampedPowerAmp'_le (lt_of_lt_of_le ha ht.1) ha ht.1 hs hε
  refine hmono.trans ?_
  have hsplit : (∫ t in a..A, g t)
      = ‖s‖ * (∫ t in a..A, t ^ (-s.re - 1))
        + a ^ (-s.re) * (∫ t in a..A, ε * Real.exp (-(ε * t))) := by
    rw [hg]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (continuousOn_const.mul hcontpow).intervalIntegrable
    · exact ContinuousOn.intervalIntegrable (by fun_prop)
  rw [hsplit]
  have hzero : (0 : ℝ) ∉ Set.uIcc a A := by
    rw [Set.uIcc_of_le haA]
    intro hmem
    exact absurd hmem.1 (not_le.2 ha)
  have hrne : (-s.re - 1) ≠ -1 := by
    intro h
    have : s.re = 0 := by linarith
    linarith
  have hexpshift : -s.re - 1 + 1 = -s.re := by ring
  have hpow : (∫ t in a..A, t ^ (-s.re - 1)) = (A ^ (-s.re) - a ^ (-s.re)) / (-s.re) := by
    rw [integral_rpow (Or.inr ⟨hrne, hzero⟩), hexpshift]
  have hAnn : (0:ℝ) ≤ A ^ (-s.re) := Real.rpow_nonneg (lt_of_lt_of_le ha haA).le _
  have hpowle : (∫ t in a..A, t ^ (-s.re - 1)) ≤ a ^ (-s.re) / s.re := by
    rw [hpow]
    have hflip : (A ^ (-s.re) - a ^ (-s.re)) / (-s.re)
        = (a ^ (-s.re) - A ^ (-s.re)) / s.re := by
      field_simp
      ring
    rw [hflip, div_le_div_iff_of_pos_right hs]
    linarith
  have hexpint : (∫ t in a..A, ε * Real.exp (-(ε * t)))
      = -Real.exp (-(ε * A)) - -Real.exp (-(ε * a)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.exp (-(ε * t))) ?_ ?_
    · intro t _
      have hbase : HasDerivAt (fun x : ℝ => -(ε * x)) (-ε) t := by
        simpa [neg_mul] using (hasDerivAt_id t).const_mul (-ε)
      have hexp := hbase.exp
      refine hexp.neg.congr_deriv ?_
      ring
    · exact ContinuousOn.intervalIntegrable (by fun_prop)
  have hexple : (∫ t in a..A, ε * Real.exp (-(ε * t))) ≤ 1 := by
    rw [hexpint]
    have h1 : Real.exp (-(ε * a)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ ε * a := mul_nonneg hε ha.le
      linarith
    have h2 : (0:ℝ) < Real.exp (-(ε * A)) := Real.exp_pos _
    linarith
  have hann : (0:ℝ) ≤ a ^ (-s.re) := Real.rpow_nonneg ha.le _
  have hsn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
  calc ‖s‖ * (∫ t in a..A, t ^ (-s.re - 1))
        + a ^ (-s.re) * (∫ t in a..A, ε * Real.exp (-(ε * t)))
      ≤ ‖s‖ * (a ^ (-s.re) / s.re) + a ^ (-s.re) * 1 := by
        gcongr
    _ = ‖s‖ * a ^ (-s.re) / s.re + a ^ (-s.re) := by ring

/-- **The uniform damped oscillatory bound.**  The estimate does not see the damping `ε` nor the
upper limit `A`. -/
theorem norm_integral_dampedPowerAmp_le {a A : ℝ} (ha : 0 < a) (haA : a ≤ A)
    {s : ℂ} (hs : 0 < s.re) {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 < L) :
    ‖∫ t in a..A, dampedPowerAmp s ε t * Complex.exp ((t * L : ℝ) * Complex.I)‖
      ≤ (3 * a ^ (-s.re) + ‖s‖ * a ^ (-s.re) / s.re) / L := by
  have hs0 : (-s) ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h] at hs
    simp at hs
  have hderiv : ∀ x ∈ Set.uIcc a A, HasDerivAt (dampedPowerAmp s ε) (dampedPowerAmp' s ε x) x := by
    intro x hx
    rw [Set.uIcc_of_le haA] at hx
    exact hasDerivAt_dampedPowerAmp (lt_of_lt_of_le ha hx.1) hs0 ε
  have hg'int : IntervalIntegrable (dampedPowerAmp' s ε) MeasureTheory.volume a A :=
    (continuousOn_dampedPowerAmp' ha haA (s := s) ε).intervalIntegrable
  refine (norm_integral_oscillatory_le hL haA hderiv hg'int).trans ?_
  rw [div_le_div_iff_of_pos_right hL]
  have hA : ‖dampedPowerAmp s ε A‖ ≤ a ^ (-s.re) :=
    norm_dampedPowerAmp_le (lt_of_lt_of_le ha haA) ha haA hs hε
  have ha' : ‖dampedPowerAmp s ε a‖ ≤ a ^ (-s.re) :=
    norm_dampedPowerAmp_le ha ha le_rfl hs hε
  have hint := integral_norm_dampedPowerAmp'_le ha haA hs hε
  linarith

end

end GaloisForLFunctions.HTGeometry
