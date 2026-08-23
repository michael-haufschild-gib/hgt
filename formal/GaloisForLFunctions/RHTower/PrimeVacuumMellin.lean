import GaloisForLFunctions.RHTower.PrimeVacuumExponentialIntegral

/-!
# The Mellin identity of the continuous prime vacuum

The interval suspension of the continuous logarithmic density has the same divided-difference
Mellin transform as the arithmetic co-Poisson current:
`∫_0^1 V_z(x) x^{w-1} dx = (V(z) - V(w)) / (w - z)`.

As with the Abel transform, the identity is proved by differentiating in the lower cut rather than
by Fubini: an explicit antiderivative in the cut is available because the `z`- and `w`-tails of the
logarithmic density differentiate to the same kernel up to the two powers.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## The vacuum current above the kink -/

theorem primeVacuumCurrent_eq_const {z : ℂ} {x : ℝ} (hx : (Real.exp 1)⁻¹ < x) (_hx1 : x ≤ 1) :
    primeVacuumCurrent z x = (x : ℂ) ^ (-z) * primeVacuumValue z := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hx0 : (0 : ℝ) < x := lt_trans (by positivity) hx
  have hinvle : x⁻¹ ≤ Real.exp 1 := by
    rw [inv_le_comm₀ hx0 he]
    exact hx.le
  rw [primeVacuumCurrent, max_eq_left hinvle, primeVacuumValue]

theorem primeVacuumCurrent_eq_tail {z : ℂ} {x : ℝ} (hx : 0 < x) (hxe : x ≤ (Real.exp 1)⁻¹) :
    primeVacuumCurrent z x = (x : ℂ) ^ (-z) * primeVacuumTail z x⁻¹ := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hle : Real.exp 1 ≤ x⁻¹ := by
    rw [le_inv_comm₀ he hx]
    exact hxe
  rw [primeVacuumCurrent, max_eq_right hle]

/-! ## The antiderivative in the cut -/

theorem ofReal_inv_cpow {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ((a⁻¹ : ℝ) : ℂ) ^ w = ((a : ℂ) ^ w)⁻¹ := by
  rw [Complex.ofReal_inv]
  refine Complex.inv_cpow (a : ℂ) w ?_
  rw [Complex.arg_ofReal_of_nonneg ha.le]
  exact ne_of_lt Real.pi_pos

theorem hasDerivAt_primeVacuumTail_inv {z : ℂ} (hz : 1 < z.re) {a : ℝ}
    (ha : 0 < a) (hae : a < 1) :
    HasDerivAt (fun t : ℝ => primeVacuumTail z t⁻¹)
      ((((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a : ℂ) ^ z / (Real.log a⁻¹ : ℂ))) a := by
  have hinv1 : (1 : ℝ) < a⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) ha]
    simpa using hae
  have hFd : HasDerivAt (primeVacuumTail z) (-logPowerTail z 1 a⁻¹) a⁻¹ := by
    have hbase : (1 : ℝ) < (1 + a⁻¹) / 2 := by linarith
    refine hasDerivAt_integral_Ioi (c := (1 + a⁻¹) / 2) (by linarith)
      (integrableOn_logPowerTail hbase hz) ?_ (continuousAt_logPowerTail hinv1)
    refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ a⁻¹ hinv1
    intro r hr
    exact (continuousAt_logPowerTail hr).continuousWithinAt
  have hginv : HasDerivAt (fun t : ℝ => t⁻¹) (-(a ^ (2 : ℕ))⁻¹) a :=
    hasDerivAt_inv (ne_of_gt ha)
  have hcomp := hFd.scomp a hginv
  refine hcomp.congr_deriv ?_
  rw [Complex.real_smul, logPowerTail, pow_one, ofReal_inv_cpow ha,
    Complex.cpow_neg, inv_inv]
  push_cast
  ring

/-- The explicit antiderivative of the vacuum Mellin integrand in the lower cut. -/
def vacuumMellinPrimitive (z w : ℂ) (a : ℝ) : ℂ :=
  ((a : ℂ) ^ (w - z) * primeVacuumTail z a⁻¹
      - (Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z
      + primeVacuumValue w - primeVacuumTail w a⁻¹) / (z - w)

theorem hasDerivAt_vacuumMellinPrimitive {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re)
    (hzw : z ≠ w) {a : ℝ} (ha : 0 < a) (hae : a < 1) :
    HasDerivAt (vacuumMellinPrimitive z w)
      (-((a : ℂ) ^ (w - z - 1) * primeVacuumTail z a⁻¹)) a := by
  have hzwne : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hane : (a : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hinv1 : (1 : ℝ) < a⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) ha]
    simpa using hae
  have hlogne : ((Real.log a⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.log_pos hinv1)
  have hd1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (w - z))
      ((w - z) * (a : ℂ) ^ (w - z - 1)) a := hasDerivAt_ofReal_cpow (w - z) ha
  have hd2 := hasDerivAt_primeVacuumTail_inv hz ha hae
  have hd3 := hasDerivAt_primeVacuumTail_inv hw ha hae
  have hprod := hd1.mul hd2
  have hnum := (hprod.sub_const ((Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z)).add_const
    (primeVacuumValue w)
  have hfull := hnum.sub hd3
  have hdiv := hfull.div_const (z - w)
  refine hdiv.congr_deriv ?_
  have hcancel : (a : ℂ) ^ (w - z) * ((((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a : ℂ) ^ z / (Real.log a⁻¹ : ℂ)))
      = (((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a : ℂ) ^ w / (Real.log a⁻¹ : ℂ)) := by
    have hsum : (a : ℂ) ^ (w - z) * (a : ℂ) ^ z = (a : ℂ) ^ w := by
      rw [← Complex.cpow_add _ _ hane]
      congr 1
      ring
    rw [show (a : ℂ) ^ (w - z) * ((((a ^ 2)⁻¹ : ℝ) : ℂ) * ((a : ℂ) ^ z / (Real.log a⁻¹ : ℂ)))
        = (((a ^ 2)⁻¹ : ℝ) : ℂ) * (((a : ℂ) ^ (w - z) * (a : ℂ) ^ z) / (Real.log a⁻¹ : ℂ)) from
      by ring, hsum]
  rw [hcancel, add_sub_cancel_right]
  rw [div_eq_iff hzwne]
  ring

/-! ## The lower piece -/

theorem vacuumMellinPrimitive_at_kink {z w : ℂ} :
    vacuumMellinPrimitive z w (Real.exp 1)⁻¹ = 0 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvinv : ((Real.exp 1)⁻¹)⁻¹ = Real.exp 1 := inv_inv _
  rw [vacuumMellinPrimitive, hinvinv, ofReal_inv_cpow he,
    ← primeVacuumValue, ← primeVacuumValue]
  have hpow : ((Real.exp 1 : ℝ) : ℂ) ^ (z - w) = (((Real.exp 1 : ℝ) : ℂ) ^ (w - z))⁻¹ := by
    rw [show z - w = -(w - z) by ring, Complex.cpow_neg]
  rw [hpow]
  simp

theorem continuousOn_vacuumIntegrand {z w : ℂ} (hz : 1 < z.re) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹) (uIcc a b) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact (hasDerivAt_ofReal_cpow (w - z - 1) ht0).continuousAt
  · exact (hasDerivAt_primeVacuumTail_inv hz ht0 ht1).continuousAt

theorem integral_vacuumMellin_lower {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re) (hzw : z ≠ w)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ (Real.exp 1)⁻¹) :
    (∫ x in Ioc a (Real.exp 1)⁻¹, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      = vacuumMellinPrimitive z w a := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvlt : (Real.exp 1)⁻¹ < 1 := by
    rw [inv_lt_one₀ he]
    exact one_lt_exp_one
  have hderiv : ∀ x ∈ uIcc a (Real.exp 1)⁻¹,
      HasDerivAt (vacuumMellinPrimitive z w)
        (-((x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹)) x := by
    intro x hx
    rw [Set.uIcc_of_le hae] at hx
    exact hasDerivAt_vacuumMellinPrimitive hz hw hzw (lt_of_lt_of_le ha hx.1)
      (lt_of_le_of_lt hx.2 hinvlt)
  have hcont : ContinuousOn (fun x : ℝ => -((x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹))
      (uIcc a (Real.exp 1)⁻¹) :=
    (continuousOn_vacuumIntegrand hz ha hinvlt hae).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  rw [vacuumMellinPrimitive_at_kink] at hFTC
  have hcongr : (∫ x in Ioc a (Real.exp 1)⁻¹, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      = ∫ x in Ioc a (Real.exp 1)⁻¹, (x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1.le
    rw [primeVacuumCurrent_eq_tail hx0 hx.2]
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx0
    have hsum : (x : ℂ) ^ (-z) * (x : ℂ) ^ (w - 1) = (x : ℂ) ^ (w - z - 1) := by
      rw [← Complex.cpow_add _ _ hxne]
      congr 1
      ring
    calc (x : ℂ) ^ (-z) * primeVacuumTail z x⁻¹ * (x : ℂ) ^ (w - 1)
        = ((x : ℂ) ^ (-z) * (x : ℂ) ^ (w - 1)) * primeVacuumTail z x⁻¹ := by ring
      _ = (x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹ := by rw [hsum]
  rw [hcongr, ← intervalIntegral.integral_of_le hae]
  have hneg : (∫ x in a..(Real.exp 1)⁻¹,
      -((x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹))
      = -∫ x in a..(Real.exp 1)⁻¹, (x : ℂ) ^ (w - z - 1) * primeVacuumTail z x⁻¹ :=
    intervalIntegral.integral_neg
  rw [hneg] at hFTC
  linear_combination -hFTC

end

end RHTower
