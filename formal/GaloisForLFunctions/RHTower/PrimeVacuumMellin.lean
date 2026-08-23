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

theorem primeVacuumCurrent_eq_const {z : ℂ} {x : ℝ} (hx : (Real.exp 1)⁻¹ ≤ x) :
    primeVacuumCurrent z x = (x : ℂ) ^ (-z) * primeVacuumValue z := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx
  have hinvle : x⁻¹ ≤ Real.exp 1 := by
    rw [inv_le_comm₀ hx0 he]
    exact hx
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

/-! ## The upper piece and the limit -/

theorem integral_vacuumMellin_upper {z w : ℂ} (hzw : z ≠ w) :
    (∫ x in Ioc (Real.exp 1)⁻¹ 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      = primeVacuumValue z * ((1 : ℂ) - (Real.exp 1 : ℂ) ^ (z - w)) / (w - z) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvlt : (Real.exp 1)⁻¹ < 1 := by
    rw [inv_lt_one₀ he]
    exact one_lt_exp_one
  have hinvpos : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
  have hcongr : (∫ x in Ioc (Real.exp 1)⁻¹ 1, primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      = ∫ x in Ioc (Real.exp 1)⁻¹ 1, primeVacuumValue z * (x : ℂ) ^ (w - z - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans hinvpos hx.1
    rw [primeVacuumCurrent_eq_const hx.1.le]
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx0
    have hsum : (x : ℂ) ^ (-z) * (x : ℂ) ^ (w - 1) = (x : ℂ) ^ (w - z - 1) := by
      rw [← Complex.cpow_add _ _ hxne]
      congr 1
      ring
    calc (x : ℂ) ^ (-z) * primeVacuumValue z * (x : ℂ) ^ (w - 1)
        = primeVacuumValue z * ((x : ℂ) ^ (-z) * (x : ℂ) ^ (w - 1)) := by ring
      _ = primeVacuumValue z * (x : ℂ) ^ (w - z - 1) := by rw [hsum]
  rw [hcongr, ← intervalIntegral.integral_of_le hinvlt.le,
    intervalIntegral.integral_const_mul, integral_cpow ?_]
  · have hrw : w - z - 1 + 1 = w - z := by ring
    rw [hrw, Complex.ofReal_one, Complex.one_cpow, ofReal_inv_cpow he,
      show ((Real.exp 1 : ℝ) : ℂ) ^ (z - w) = (((Real.exp 1 : ℝ) : ℂ) ^ (w - z))⁻¹ by
        rw [show z - w = -(w - z) by ring, Complex.cpow_neg]]
    ring
  · refine Or.inr ⟨?_, ?_⟩
    · intro hcon
      exact hzw (by
        have : w - z = 0 := by linear_combination hcon
        linear_combination -this)
    · rw [Set.uIcc_of_le hinvlt.le]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hinvpos)

theorem tendsto_vacuumMellinPrimitive {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re) :
    Tendsto (vacuumMellinPrimitive z w) (𝓝[>] 0)
      (𝓝 ((-((Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z) + primeVacuumValue w)
        / (z - w))) := by
  have hfirst : Tendsto (fun a : ℝ => (a : ℂ) ^ (w - z) * primeVacuumTail z a⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
    have hmaj : Tendsto (fun a : ℝ => a ^ (w.re - 1) / (z.re - 1)) (𝓝[>] 0) (𝓝 0) := by
      have hbase : Tendsto (fun a : ℝ => a ^ (w.re - 1)) (𝓝[>] 0) (𝓝 0) := by
        have h := (Real.continuousAt_rpow_const (0 : ℝ) (w.re - 1) (Or.inr (by linarith))).tendsto
        rw [Real.zero_rpow (by intro hc; linarith [hc])] at h
        exact h.mono_left nhdsWithin_le_nhds
      simpa using hbase.div_const (z.re - 1)
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < (Real.exp 1)⁻¹ by positivity)] with a ha
    have ha0 : (0 : ℝ) < a := ha.1
    have hainv : Real.exp 1 ≤ a⁻¹ := by
      rw [le_inv_comm₀ (Real.exp_pos 1) ha0]
      exact ha.2.le
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
    have hb := norm_primeVacuumTail_le hz hainv
    have hpow : (a⁻¹ : ℝ) ^ (1 - z.re) = a ^ (z.re - 1) := by
      rw [← Real.rpow_neg_one a, ← Real.rpow_mul ha0.le]
      congr 1
      ring
    rw [hpow] at hb
    have hre : a ^ (w - z).re = a ^ (w.re - z.re) := by
      congr 1
    rw [hre]
    have hstep : a ^ (w.re - z.re) * ‖primeVacuumTail z a⁻¹‖
        ≤ a ^ (w.re - z.re) * (a ^ (z.re - 1) / (z.re - 1)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos ha0 _).le
    refine hstep.trans ?_
    refine le_of_eq ?_
    rw [mul_div_assoc', ← Real.rpow_add ha0,
      show w.re - z.re + (z.re - 1) = w.re - 1 by ring]
  have hsecond : Tendsto (fun a : ℝ => primeVacuumTail w a⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hmaj : Tendsto (fun a : ℝ => a ^ (w.re - 1) / (w.re - 1)) (𝓝[>] 0) (𝓝 0) := by
      have hbase : Tendsto (fun a : ℝ => a ^ (w.re - 1)) (𝓝[>] 0) (𝓝 0) := by
        have h := (Real.continuousAt_rpow_const (0 : ℝ) (w.re - 1) (Or.inr (by linarith))).tendsto
        rw [Real.zero_rpow (by intro hc; linarith [hc])] at h
        exact h.mono_left nhdsWithin_le_nhds
      simpa using hbase.div_const (w.re - 1)
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < (Real.exp 1)⁻¹ by positivity)] with a ha
    have ha0 : (0 : ℝ) < a := ha.1
    have hainv : Real.exp 1 ≤ a⁻¹ := by
      rw [le_inv_comm₀ (Real.exp_pos 1) ha0]
      exact ha.2.le
    have hb := norm_primeVacuumTail_le hw hainv
    have hpow : (a⁻¹ : ℝ) ^ (1 - w.re) = a ^ (w.re - 1) := by
      rw [← Real.rpow_neg_one a, ← Real.rpow_mul ha0.le]
      congr 1
      ring
    rwa [hpow] at hb
  have hcomb := ((hfirst.sub_const ((Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z)).add_const
    (primeVacuumValue w)).sub hsecond
  have hlim := hcomb.div_const (z - w)
  have hval : (0 - (Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z + primeVacuumValue w - 0)
      = -((Real.exp 1 : ℂ) ^ (z - w) * primeVacuumValue z) + primeVacuumValue w := by ring
  rw [hval] at hlim
  refine Tendsto.congr ?_ hlim
  intro a
  rw [vacuumMellinPrimitive]

/-! ## Integrability and the Mellin identity -/

theorem integrableOn_vacuumMellin_lower {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      (Ioc 0 (Real.exp 1)⁻¹) volume := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvpos : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
  have hinvlt : (Real.exp 1)⁻¹ < 1 := by
    rw [inv_lt_one₀ he]
    exact one_lt_exp_one
  have heq : ∀ x ∈ Ioc (0 : ℝ) (Real.exp 1)⁻¹,
      primeVacuumCurrent z x * (x : ℂ) ^ (w - 1)
        = (x : ℂ) ^ (-z) * primeVacuumTail z x⁻¹ * (x : ℂ) ^ (w - 1) :=
    fun x hx => by rw [primeVacuumCurrent_eq_tail hx.1 hx.2]
  have hmajor : IntegrableOn (fun x : ℝ => (z.re - 1)⁻¹ * x ^ (w.re - 2))
      (Ioc 0 (Real.exp 1)⁻¹) volume := by
    have hb : IntegrableOn (fun x : ℝ => x ^ (w.re - 2)) (Ioo 0 (Real.exp 1)⁻¹) volume := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hinvpos]
      linarith
    exact ((integrableOn_Ioc_iff_integrableOn_Ioo).mpr hb).const_mul _
  refine Integrable.mono' hmajor ?_ ?_
  · refine (ContinuousOn.congr ?_ heq).aestronglyMeasurable measurableSet_Ioc
    intro t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hinvlt
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_)
    · exact (hasDerivAt_ofReal_cpow (-z) ht0).continuousAt
    · exact (hasDerivAt_primeVacuumTail_inv hz ht0 ht1).continuousAt
    · exact (hasDerivAt_ofReal_cpow (w - 1) ht0).continuousAt
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxinv : Real.exp 1 ≤ x⁻¹ := by
      rw [le_inv_comm₀ he hx0]
      exact hx.2
    rw [heq x hx, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hb := norm_primeVacuumTail_le hz hxinv
    have hpow : (x⁻¹ : ℝ) ^ (1 - z.re) = x ^ (z.re - 1) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    rw [hpow] at hb
    have hre1 : x ^ (-z).re = x ^ (-z.re) := by congr 1
    have hre2 : x ^ (w - 1).re = x ^ (w.re - 1) := by congr 1
    rw [hre1, hre2]
    have hstep : x ^ (-z.re) * ‖primeVacuumTail z x⁻¹‖ * x ^ (w.re - 1)
        ≤ x ^ (-z.re) * (x ^ (z.re - 1) / (z.re - 1)) * x ^ (w.re - 1) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hx0 _).le
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hx0 _).le
    refine hstep.trans ?_
    refine le_of_eq ?_
    rw [mul_div_assoc', ← Real.rpow_add hx0, div_mul_eq_mul_div, ← Real.rpow_add hx0,
      show -z.re + (z.re - 1) + (w.re - 1) = w.re - 2 by ring]
    ring

theorem integrableOn_vacuumMellin_upper {z w : ℂ} :
    IntegrableOn (fun x : ℝ => primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      (Ioc (Real.exp 1)⁻¹ 1) volume := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinvpos : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
  have hinvlt : (Real.exp 1)⁻¹ < 1 := by
    rw [inv_lt_one₀ he]
    exact one_lt_exp_one
  have hcont : ContinuousOn (fun x : ℝ => primeVacuumCurrent z x * (x : ℂ) ^ (w - 1))
      (Icc (Real.exp 1)⁻¹ 1) := by
    refine ContinuousOn.congr
      (f := fun x : ℝ => (x : ℂ) ^ (-z) * primeVacuumValue z * (x : ℂ) ^ (w - 1)) ?_
      (fun x hx => ?_)
    · exact fun t ht => ContinuousAt.continuousWithinAt
        (((hasDerivAt_ofReal_cpow (-z) (lt_of_lt_of_le hinvpos ht.1)).continuousAt.mul
          continuousAt_const).mul
          (hasDerivAt_ofReal_cpow (w - 1) (lt_of_lt_of_le hinvpos ht.1)).continuousAt)
    · rw [primeVacuumCurrent_eq_const hx.1]
  exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self

end

end RHTower
