import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# The Mellin multiplier of the first cyclotomic mode

Integration by parts bounds a power-weighted exponential moment by the
variation of its amplitude divided by its phase derivative. The moment
cannot vanish above its oscillation frequency.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Power moment of a finite exponential arc. -/
def cyclotomicMellinMoment (a : ℝ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) ^ s * Complex.exp (Complex.I * a * t)

private theorem continuousOn_power {s : ℂ} (hs : 0 < s.re) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ s) (uIcc 0 1) :=
  (Complex.continuous_ofReal_cpow_const hs).continuousOn

private theorem continuousOn_momentIntegrand (a : ℝ) {s : ℂ} (hs : 0 < s.re) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ s * Complex.exp (Complex.I * a * t))
      (uIcc 0 1) :=
  (continuousOn_power hs).mul (by fun_prop)

private theorem deriv_momentPrimitive (a : ℝ) {s : ℂ} (hs : 0 < s.re)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (u : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * u))
      ((s + 1) * ((t : ℂ) ^ s * Complex.exp (Complex.I * a * t)) +
        (Complex.I * a) * ((t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t))) t := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  have hp := hasDerivAt_ofReal_cpow_const ht.ne' hs1
  rw [add_sub_cancel_right] at hp
  have he : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * a * u))
      (Complex.exp (Complex.I * a * t) * (Complex.I * a)) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * a)).cexp
  convert! hp.mul he using 1
  ring

/-- Integration by parts relates successive power moments. -/
theorem cyclotomicMellinMoment_recurrence (a : ℝ) {s : ℂ} (hs : 0 < s.re) :
    (s + 1) * cyclotomicMellinMoment a s +
      (Complex.I * a) * cyclotomicMellinMoment a (s + 1) = Complex.exp (Complex.I * a) := by
  have hs1 : 0 < (s + 1).re := by simpa only [add_re, one_re] using (by linarith : 0 < s.re + 1)
  have h0 : s + 1 ≠ 0 := ne_zero_of_re_pos hs1
  have hc := continuousOn_momentIntegrand a hs
  have hc1 := continuousOn_momentIntegrand a hs1
  have hi : ContinuousOn (fun t : ℝ =>
      (s + 1) * ((t : ℂ) ^ s * Complex.exp (Complex.I * a * t)) +
        (Complex.I * a) * ((t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t)))
      (uIcc 0 1) := (continuousOn_const.mul hc).add (continuousOn_const.mul hc1)
  have h := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc1)
    (fun t ht => deriv_momentPrimitive a hs ht.1) hi.intervalIntegrable
  rw [intervalIntegral.integral_add] at h
  · simp only [intervalIntegral.integral_const_mul, cyclotomicMellinMoment, ofReal_one, one_cpow,
      mul_one, one_mul, ofReal_zero, zero_cpow h0, zero_mul, sub_zero] at h ⊢
    exact h
  · exact (hc.intervalIntegrable).const_mul _
  · exact (hc1.intervalIntegrable).const_mul _


private def phaseCoefficient (a : ℝ) (s : ℂ) (t : ℝ) : ℝ :=
  ((s.re + 2) * s.im + (s.re + 1) * a * t) / (s.im + a * t) ^ 2

private def phasePrimitive (a : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s + 2) * Complex.exp (Complex.I * a * t) /
    (Complex.I * ((s.im + a * t : ℝ) : ℂ))

private def phaseAmplitude (a : ℝ) (s : ℂ) (t : ℝ) : ℝ :=
  t ^ (s.re + 2) / (s.im + a * t)

private theorem phase_den_pos {a : ℝ} (ha : 0 < a) {s : ℂ} (hτ : 0 < s.im)
    {t : ℝ} (ht : 0 ≤ t) : 0 < s.im + a * t :=
  add_pos_of_pos_of_nonneg hτ (mul_nonneg ha.le ht)

private theorem phaseCoefficient_nonneg {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ phaseCoefficient a s t := by
  unfold phaseCoefficient
  exact div_nonneg (add_nonneg (mul_nonneg (by linarith) hτ.le)
    (mul_nonneg (mul_nonneg (by linarith) ha.le) ht)) (sq_nonneg _)

private theorem continuousOn_phaseCoefficient {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hτ : 0 < s.im) : ContinuousOn (phaseCoefficient a s) (uIcc 0 1) := by
  unfold phaseCoefficient
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact pow_ne_zero _ (phase_den_pos ha hτ ht.1).ne'

private theorem hasDerivAt_phaseAmplitude {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hτ : 0 < s.im) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (phaseAmplitude a s)
      (t ^ (s.re + 1) * phaseCoefficient a s t) t := by
  have hp := Real.hasDerivAt_rpow_const (p := s.re + 2) (Or.inl ht.ne')
  rw [show s.re + 2 - 1 = s.re + 1 by ring] at hp
  have hd : HasDerivAt (fun u : ℝ => s.im + a * u) a t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using ((hasDerivAt_id t).const_mul a).const_add s.im
  have hpow : t ^ (s.re + 2) = t ^ (s.re + 1) * t := by
    rw [show s.re + 2 = (s.re + 1) + 1 by ring, Real.rpow_add_one ht.ne']
  convert! hp.div hd (phase_den_pos ha hτ ht.le).ne' using 1
  rw [hpow]
  unfold phaseCoefficient
  ring

private theorem integral_phase_variation {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) :
    (∫ t in (0 : ℝ)..1, t ^ (s.re + 1) * phaseCoefficient a s t) =
      1 / (s.im + a) := by
  have hc : ContinuousOn (phaseAmplitude a s) (Icc 0 1) := by
    unfold phaseAmplitude
    refine ContinuousOn.div (Real.continuous_rpow_const (by linarith)).continuousOn
      (by fun_prop) fun t ht => (phase_den_pos ha hτ ht.1).ne'
  have hv : ContinuousOn (fun t : ℝ => t ^ (s.re + 1) * phaseCoefficient a s t)
      (uIcc 0 1) :=
    (Real.continuous_rpow_const (by linarith)).continuousOn.mul
      (continuousOn_phaseCoefficient ha hτ)
  have h := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1) hc
    (fun t ht => hasDerivAt_phaseAmplitude ha hτ ht.1) hv.intervalIntegrable
  simpa only [phaseAmplitude, Real.one_rpow, mul_one,
    Real.zero_rpow (show s.re + 2 ≠ 0 by linarith), zero_div, sub_zero] using h

private theorem hasDerivAt_phasePrimitive {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (phasePrimitive a s)
      ((t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t) -
        Complex.I * ((t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t) *
          (phaseCoefficient a s t : ℂ))) t := by
  have hs2 : s + 2 ≠ 0 := ne_zero_of_re_pos (by simpa using
    (show 0 < s.re + 2 by linarith))
  have hp := hasDerivAt_ofReal_cpow_const ht.ne' hs2
  rw [show s + 2 - 1 = s + 1 by ring] at hp
  have he : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * a * u))
      (Complex.exp (Complex.I * a * t) * (Complex.I * a)) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * a)).cexp
  have hd : HasDerivAt (fun u : ℝ => Complex.I * ((s.im + a * u : ℝ) : ℂ))
      (Complex.I * a) t := by
    have h := (((hasDerivAt_id t).const_mul a).const_add s.im).ofReal_comp
    simpa only [id_eq, Complex.ofReal_one, mul_one] using h.const_mul Complex.I
  have hden : ((s.im + a * t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (phase_den_pos ha hτ ht.le).ne'
  have hpow : (t : ℂ) ^ (s + 2) = (t : ℂ) ^ (s + 1) * t := by
    rw [show s + 2 = (s + 1) + 1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
  convert! (hp.mul he).div hd (mul_ne_zero Complex.I_ne_zero hden) using 1
  simp only [Pi.mul_apply]
  rw [hpow]
  unfold phaseCoefficient
  push_cast at hden ⊢
  have hsrepr : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
  rw [hsrepr]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, add_zero, zero_add, mul_one, sub_zero]
  field_simp [hden]
  ring_nf
  simp only [Complex.I_sq]
  ring


private def phaseRemainder (a : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t) * (phaseCoefficient a s t : ℂ)

private theorem continuousOn_phaseRemainder {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) :
    ContinuousOn (phaseRemainder a s) (uIcc 0 1) := by
  exact (continuousOn_momentIntegrand a (by simpa using (show 0 < s.re + 1 by linarith))).mul
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_phaseCoefficient ha hτ))

private theorem norm_phaseRemainder {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) {t : ℝ} (ht : 0 ≤ t) :
    ‖phaseRemainder a s t‖ = t ^ (s.re + 1) * phaseCoefficient a s t := by
  have hs1 : (s + 1).re ≠ 0 := by simp only [add_re, one_re]; linarith
  have he : ‖Complex.exp (Complex.I * a * t)‖ = 1 := by simp [Complex.norm_exp]
  rw [phaseRemainder, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_nonneg ht hs1, he, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (phaseCoefficient_nonneg ha hs hτ ht)]
  simp only [add_re, one_re]

private theorem continuousOn_phasePrimitive {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) :
    ContinuousOn (phasePrimitive a s) (Icc 0 1) := by
  unfold phasePrimitive
  refine ContinuousOn.div ?_ (by fun_prop) ?_
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_momentIntegrand a (show 0 < (s + 2).re by simpa using
        (show 0 < s.re + 2 by linarith))
  · intro t ht
    exact mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (phase_den_pos ha hτ ht.1).ne')

/-- The phase quotient has monotone amplitude, so its total variation pays
the oscillatory integral with exactly two endpoint contributions. -/
theorem norm_cyclotomicMellinMoment_succ_le {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : 0 < s.im) :
    ‖cyclotomicMellinMoment a (s + 1)‖ ≤ 2 / (s.im + a) := by
  have hs1 : 0 < (s + 1).re := by simpa using (show 0 < s.re + 1 by linarith)
  have hs2 : s + 2 ≠ 0 := ne_zero_of_re_pos (by simpa using
    (show 0 < s.re + 2 by linarith))
  have hd : 0 < s.im + a := add_pos hτ ha
  have hi : IntervalIntegrable
      (fun t : ℝ => (t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t)) volume 0 1 :=
    (continuousOn_momentIntegrand a hs1).intervalIntegrable
  have hR : IntervalIntegrable (phaseRemainder a s) volume 0 1 :=
    (continuousOn_phaseRemainder ha hs hτ).intervalIntegrable
  have hftc : cyclotomicMellinMoment a (s + 1) -
      Complex.I * (∫ t in (0 : ℝ)..1, phaseRemainder a s t) = phasePrimitive a s 1 := by
    have h := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
      (continuousOn_phasePrimitive ha hs hτ)
      (fun t ht => hasDerivAt_phasePrimitive ha hs hτ ht.1)
      (hi.sub (hR.const_mul Complex.I))
    change (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s + 1) * Complex.exp (Complex.I * a * t) -
      Complex.I * phaseRemainder a s t) = phasePrimitive a s 1 - phasePrimitive a s 0 at h
    rw [intervalIntegral.integral_sub hi (hR.const_mul Complex.I),
      intervalIntegral.integral_const_mul] at h
    have hzero : phasePrimitive a s 0 = 0 := by
      simp only [phasePrimitive, ofReal_zero, zero_cpow hs2, zero_mul, zero_div]
    simpa only [cyclotomicMellinMoment, phaseRemainder, hzero, sub_zero] using h
  have hnorm : ‖phasePrimitive a s 1‖ = 1 / (s.im + a) := by
    simp [phasePrimitive, Complex.norm_exp]
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hvar : (∫ t in (0 : ℝ)..1, ‖phaseRemainder a s t‖) = 1 / (s.im + a) := by
    rw [show (∫ t in (0 : ℝ)..1, ‖phaseRemainder a s t‖) =
        ∫ t in (0 : ℝ)..1, t ^ (s.re + 1) * phaseCoefficient a s t from
      intervalIntegral.integral_congr fun t ht => norm_phaseRemainder ha hs hτ
        (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht; exact ht.1)]
    exact integral_phase_variation ha hs hτ
  have hsplit : cyclotomicMellinMoment a (s + 1) = phasePrimitive a s 1 +
      Complex.I * (∫ t in (0 : ℝ)..1, phaseRemainder a s t) := by
    linear_combination hftc
  calc
    ‖cyclotomicMellinMoment a (s + 1)‖ ≤ ‖phasePrimitive a s 1‖ +
        ‖Complex.I * (∫ t in (0 : ℝ)..1, phaseRemainder a s t)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ ‖phasePrimitive a s 1‖ + ∫ t in (0 : ℝ)..1, ‖phaseRemainder a s t‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm
        (by norm_num : (0 : ℝ) ≤ 1))
    _ = 2 / (s.im + a) := by rw [hnorm, hvar]; ring

/-- Above the oscillation frequency, a power moment cannot vanish. -/
theorem cyclotomicMellinMoment_ne_zero {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hτ : a < s.im) : cyclotomicMellinMoment a s ≠ 0 := by
  intro hzero
  have h := cyclotomicMellinMoment_recurrence a hs
  rw [hzero, mul_zero, zero_add] at h
  have hn : a * ‖cyclotomicMellinMoment a (s + 1)‖ = 1 := by
    simpa [norm_mul, Complex.norm_exp, abs_of_pos ha] using congrArg norm h
  have hpos : 0 < ‖cyclotomicMellinMoment a (s + 1)‖ := by
    by_contra hnot
    have hnormzero := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    rw [hnormzero, mul_zero] at hn
    norm_num at hn
  have hτ0 : 0 < s.im := ha.trans hτ
  have hb := norm_cyclotomicMellinMoment_succ_le ha hs hτ0
  rw [le_div_iff₀ (add_pos hτ0 ha)] at hb
  have hgap := mul_pos (sub_pos.mpr hτ) hpos
  nlinarith only [hn, hb, hgap]

#print axioms cyclotomicMellinMoment_recurrence
#print axioms norm_cyclotomicMellinMoment_succ_le
#print axioms cyclotomicMellinMoment_ne_zero


/-- Mellin multiplier of the first cyclotomic difference. -/
def firstCyclotomicMellin (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) *
    (1 - Complex.exp (Complex.I * (2 * Real.pi) * t))

private theorem mellinDifference_eq_moment (a : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s * (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) *
      (1 - Complex.exp (Complex.I * a * t))) =
      1 - Complex.exp (Complex.I * a) + (Complex.I * a) * cyclotomicMellinMoment a s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have hkernel : ContinuousOn
      (fun t : ℝ => (1 : ℂ) - Complex.exp (Complex.I * a * t)) (uIcc 0 1) := by
    fun_prop
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (1 - Complex.exp (Complex.I * a * t))) volume 0 1 :=
    (intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 1)
      (by simp only [sub_re, one_re]; linarith)).mul_continuousOn hkernel
  have him : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ s *
      Complex.exp (Complex.I * a * t)) volume 0 1 :=
    (continuousOn_momentIntegrand a hs).intervalIntegrable
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ s *
      (1 - Complex.exp (Complex.I * a * t))) (Icc 0 1) := by
    simpa only [Pi.mul_apply, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using!
      (continuousOn_power hs).mul hkernel
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => (u : ℂ) ^ s * (1 - Complex.exp (Complex.I * a * u)))
      (s * ((t : ℂ) ^ (s - 1) * (1 - Complex.exp (Complex.I * a * t))) -
        (Complex.I * a) *
          ((t : ℂ) ^ s * Complex.exp (Complex.I * a * t))) t := by
    intro t ht
    have hp := hasDerivAt_ofReal_cpow_const ht.1.ne' hs0
    have he : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * a * u))
        (Complex.exp (Complex.I * a * t) * (Complex.I * a)) t := by
      simpa only [id_eq, Complex.ofReal_one, mul_one] using
        (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I * a)).cexp
    convert! hp.mul ((hasDerivAt_const t (1 : ℂ)).sub he) using 1
    simp only [Pi.sub_apply]
    ring
  have h := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1) hc hd
    ((hi.const_mul s).sub (him.const_mul (Complex.I * a)))
  rw [intervalIntegral.integral_sub (hi.const_mul s)
    (him.const_mul (Complex.I * a)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simp only [ofReal_one, ofReal_zero, one_cpow, zero_cpow hs0, mul_one,
    one_mul, zero_mul, sub_zero] at h
  change s * (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) *
      (1 - Complex.exp (Complex.I * a * t))) -
    (Complex.I * a) * cyclotomicMellinMoment a s = 1 - Complex.exp (Complex.I * a) at h
  linear_combination h

/-- The endpoint phase is one, leaving a single exponential moment. -/
theorem firstCyclotomicMellin_eq_moment {s : ℂ} (hs : 0 < s.re) :
    s * firstCyclotomicMellin s =
      (Complex.I * (2 * Real.pi)) * cyclotomicMellinMoment (2 * Real.pi) s := by
  have hphase : Complex.exp (Complex.I * (2 * Real.pi)) = 1 := by
    rw [show Complex.I * (2 * Real.pi) = 2 * (Real.pi : ℂ) * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  simpa only [firstCyclotomicMellin, Complex.ofReal_mul, Complex.ofReal_ofNat,
    hphase, sub_self, zero_add] using
    mellinDifference_eq_moment (2 * Real.pi) hs

/-- The first mode retains every Mellin pole above height `2π` in the right half-plane. -/
theorem firstCyclotomicMellin_ne_zero {s : ℂ} (hs : 0 < s.re)
    (hτ : 2 * Real.pi < s.im) : firstCyclotomicMellin s ≠ 0 := by
  intro hz
  have h := firstCyclotomicMellin_eq_moment hs
  rw [hz, mul_zero] at h
  have ha : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hcoeff : Complex.I * (2 * Real.pi) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ha.ne')
  exact (mul_ne_zero hcoeff (cyclotomicMellinMoment_ne_zero ha hs hτ)) h.symm

#print axioms firstCyclotomicMellin_eq_moment
#print axioms firstCyclotomicMellin_ne_zero

end GaloisForLFunctions.CompletedArithmeticForms
