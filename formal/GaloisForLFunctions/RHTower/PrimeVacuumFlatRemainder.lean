import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer

/-!
# The vacuum-normalized arithmetic remainder is all-orders flat

Subtracting the two Abel transforms — the arithmetic one for the prime tail and the continuous one
for the logarithmic vacuum — expresses their difference as a single Mellin-type integral of the
window increment of `J - J₀`.  The quantitative prime number theorem bounds that increment by
`u e^{-c √log u}`, and the monotonicity of `√log` turns the bound into a factor
`e^{-c √log y}` outside the elementary power integral.

The resulting remainder is smaller than the vacuum by a factor beating every power of the
logarithmic boundary coordinate.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## Integrability of the Abel integrands -/

theorem integrableOn_cpow_mul_linear {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 0 < y)
    {g : ℝ → ℝ} {C : ℝ}
    (hg : AEStronglyMeasurable (fun u : ℝ => ((g u : ℝ) : ℂ)) (volume.restrict (Ioi y)))
    (_hC : 0 ≤ C)
    (hbd : ∀ u : ℝ, y ≤ u → |g u| ≤ C * u) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1) * (g u : ℂ)) (Ioi y) volume := by
  have hmajor : IntegrableOn (fun u : ℝ => C * u ^ (-z.re)) (Ioi y) volume :=
    (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy).const_mul C
  refine Integrable.mono' hmajor ?_ ?_
  · exact (measurable_ofReal_cpow (-z - 1)).aestronglyMeasurable.restrict.mul hg
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans hy hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real, Real.norm_eq_abs]
    have hpow : u ^ (-z - 1).re = u ^ (-z.re) * u⁻¹ := by
      rw [← Real.rpow_neg_one u, ← Real.rpow_add hu0]
      congr 1
    rw [hpow, mul_assoc]
    have hsmall : u⁻¹ * |g u| ≤ C := by
      rw [inv_mul_eq_div, div_le_iff₀ hu0]
      have := hbd u hu.le
      linarith
    calc u ^ (-z.re) * (u⁻¹ * |g u|)
        ≤ u ^ (-z.re) * C := mul_le_mul_of_nonneg_left hsmall (Real.rpow_pos_of_pos hu0 _).le
      _ = C * u ^ (-z.re) := by ring

theorem aestronglyMeasurable_ofReal_logIntegralCount {y : ℝ} (hy : 1 ≤ y) :
    AEStronglyMeasurable (fun u : ℝ => ((logIntegralCount u : ℝ) : ℂ))
      (volume.restrict (Ioi y)) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_logIntegralCount.mono (fun _ ht => lt_of_le_of_lt hy ht))).aestronglyMeasurable
    measurableSet_Ioi

/-! ## The arithmetic remainder relative to the vacuum -/

/-- The difference of the arithmetic tail and the continuous vacuum tail. -/
def primeRemainderTail (z : ℂ) (y : ℝ) : ℂ := primeTailSum z y - primeVacuumTail z y

theorem integrableOn_abel_primeTailCount {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : 1 < y) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1)
      * (((primeTailCount u : ℝ) : ℂ) - ((primeTailCount y : ℝ) : ℂ))) (Ioi y) volume := by
  obtain ⟨C, hC0, hC⟩ := exists_primeTailCount_le_linear
  have hy0 : (0 : ℝ) < y := by linarith
  have hcongr : (fun u : ℝ => (u : ℂ) ^ (-z - 1)
      * (((primeTailCount u : ℝ) : ℂ) - ((primeTailCount y : ℝ) : ℂ)))
      = fun u : ℝ => (u : ℂ) ^ (-z - 1)
        * (((primeTailCount u - primeTailCount y : ℝ)) : ℂ) := by
    funext u
    rw [Complex.ofReal_sub]
  rw [hcongr]
  refine integrableOn_cpow_mul_linear hz hy0
    (((Complex.measurable_ofReal.comp
      (measurable_primeTailCount.sub measurable_const))).aestronglyMeasurable.restrict)
    (le_of_lt (add_pos_of_pos_of_nonneg hC0
      (div_nonneg (primeTailCount_nonneg y) hy0.le))) (fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu
  have h1 : primeTailCount u ≤ C * u := hC u (by linarith)
  have h2 : (0 : ℝ) ≤ primeTailCount y := primeTailCount_nonneg y
  have h3 : (0 : ℝ) ≤ primeTailCount u := primeTailCount_nonneg u
  have h4 : primeTailCount y / y * u ≥ primeTailCount y := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hy0]
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem integrableOn_abel_logIntegralCount {z : ℂ} (hz : 1 < z.re) {y : ℝ}
    (hy : Real.exp 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-z - 1)
      * (((logIntegralCount u : ℝ) : ℂ) - ((logIntegralCount y : ℝ) : ℂ))) (Ioi y) volume := by
  have hy1 : (1 : ℝ) < y := lt_of_lt_of_le one_lt_exp_one hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hcongr : (fun u : ℝ => (u : ℂ) ^ (-z - 1)
      * (((logIntegralCount u : ℝ) : ℂ) - ((logIntegralCount y : ℝ) : ℂ)))
      = fun u : ℝ => (u : ℂ) ^ (-z - 1)
        * (((logIntegralCount u - logIntegralCount y : ℝ)) : ℂ) := by
    funext u
    rw [Complex.ofReal_sub]
  rw [hcongr]
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((logIntegralCount u - logIntegralCount y : ℝ) : ℂ))
      (volume.restrict (Ioi y)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_logIntegralCount.mono
        (fun _ ht => lt_of_le_of_lt hy1.le ht)).sub continuousOn_const)).aestronglyMeasurable
      measurableSet_Ioi
  refine integrableOn_cpow_mul_linear hz hy0 hmeas (by norm_num : (0:ℝ) ≤ 1) (fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hy0 hu
  have hue : Real.exp 1 ≤ u := le_trans hy hu
  have h1 : logIntegralCount u ≤ u := logIntegralCount_le hue
  have h2 : (0 : ℝ) ≤ logIntegralCount y := logIntegralCount_nonneg hy
  have h3 : (0 : ℝ) ≤ logIntegralCount u := logIntegralCount_nonneg hue
  have h4 : logIntegralCount y ≤ y := logIntegralCount_le hy
  rw [abs_le]
  constructor <;> nlinarith

theorem primeRemainderTail_eq {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : Real.exp 1 < y) :
    primeRemainderTail z y
      = z * ∫ u in Ioi y, (u : ℂ) ^ (-z - 1)
          * ((((primeTailCount u - logIntegralCount u : ℝ)) : ℂ)
            - (((primeTailCount y - logIntegralCount y : ℝ)) : ℂ)) := by
  have hy1 : (1 : ℝ) < y := lt_trans one_lt_exp_one hy
  rw [primeRemainderTail, primeTailSum_eq_integral hz hy1.le, primeVacuumTail_eq_window hz hy,
    ← mul_sub, ← MeasureTheory.integral_sub (integrableOn_abel_primeTailCount hz hy1)
      (integrableOn_abel_logIntegralCount hz hy.le)]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  push_cast
  ring

theorem norm_primeRemainderTail_le {z : ℂ} (hz : 1 < z.re) {C c y : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hy : Real.exp 1 < y)
    (hE : ∀ u : ℝ, y ≤ u → |primeTailCount u - logIntegralCount u|
        ≤ C * (u * Real.exp (-c * Real.sqrt (Real.log u)))) :
    ‖primeRemainderTail z y‖
      ≤ ‖z‖ * (C * (1 / (z.re - 1) + 1 / z.re))
        * (y ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log y))) := by
  have hy1 : (1 : ℝ) < y := lt_trans one_lt_exp_one hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hz0 : (0 : ℝ) < z.re := by linarith
  set E : ℝ := Real.exp (-c * Real.sqrt (Real.log y)) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hmaj : IntegrableOn
      (fun u : ℝ => C * E * (u ^ (-z.re) + y * u ^ (-z.re - 1))) (Ioi y) volume := by
    refine Integrable.const_mul ?_ _
    exact (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0).add
      ((integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) hy0).const_mul y)
  have hptw : ∀ u ∈ Ioi y,
      ‖(u : ℂ) ^ (-z - 1) * ((((primeTailCount u - logIntegralCount u : ℝ)) : ℂ)
        - (((primeTailCount y - logIntegralCount y : ℝ)) : ℂ))‖
        ≤ C * E * (u ^ (-z.re) + y * u ^ (-z.re - 1)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hy0 hu
    have huy : y ≤ u := hu.le
    have hlogle : Real.exp (-c * Real.sqrt (Real.log u)) ≤ E := by
      rw [hEdef]
      refine Real.exp_le_exp.mpr ?_
      have hsq : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log u) :=
        Real.sqrt_le_sqrt (Real.log_le_log hy0 huy)
      nlinarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hbd : |primeTailCount u - logIntegralCount u
        - (primeTailCount y - logIntegralCount y)| ≤ C * (u * E) + C * (y * E) := by
      refine le_trans (abs_sub _ _) ?_
      have h1 := hE u huy
      have h2 := hE y le_rfl
      have h1' : C * (u * Real.exp (-c * Real.sqrt (Real.log u))) ≤ C * (u * E) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact mul_le_mul_of_nonneg_left hlogle hu0.le
      linarith
    have hpowrw : u ^ (-z - 1).re = u ^ (-z.re - 1) := by
      congr 1
    have hstep : u ^ (-z.re - 1) * |primeTailCount u - logIntegralCount u
        - (primeTailCount y - logIntegralCount y)|
        ≤ u ^ (-z.re - 1) * (C * (u * E) + C * (y * E)) :=
      mul_le_mul_of_nonneg_left hbd (Real.rpow_pos_of_pos hu0 _).le
    rw [hpowrw]
    refine hstep.trans ?_
    have hsplit : u ^ (-z.re - 1) * u = u ^ (-z.re) := by
      rw [show u ^ (-z.re - 1) * u = u ^ (-z.re - 1) * u ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hu0]
      congr 1
      ring
    refine le_of_eq ?_
    calc u ^ (-z.re - 1) * (C * (u * E) + C * (y * E))
        = C * E * ((u ^ (-z.re - 1) * u) + y * u ^ (-z.re - 1)) := by ring
      _ = C * E * (u ^ (-z.re) + y * u ^ (-z.re - 1)) := by rw [hsplit]
  have hnorm : ‖∫ u in Ioi y, (u : ℂ) ^ (-z - 1)
      * ((((primeTailCount u - logIntegralCount u : ℝ)) : ℂ)
        - (((primeTailCount y - logIntegralCount y : ℝ)) : ℂ))‖
      ≤ ∫ u in Ioi y, C * E * (u ^ (-z.re) + y * u ^ (-z.re - 1)) := by
    refine norm_integral_le_of_norm_le hmaj ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact hptw u hu
  have hval : (∫ u in Ioi y, C * E * (u ^ (-z.re) + y * u ^ (-z.re - 1)))
      = C * E * (y ^ (1 - z.re) / (z.re - 1) + y * (y ^ (-z.re) / z.re)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (integrableOn_Ioi_rpow_of_lt (a := -z.re) (by linarith) hy0)
        ((integrableOn_Ioi_rpow_of_lt (a := -z.re - 1) (by linarith) hy0).const_mul y),
      MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -z.re < -1) hy0,
      integral_Ioi_rpow_of_lt (by linarith : -z.re - 1 < -1) hy0]
    have h1 : -y ^ (-z.re + 1) / (-z.re + 1) = y ^ (1 - z.re) / (z.re - 1) := by
      rw [show -z.re + 1 = -(z.re - 1) by ring, show (1 : ℝ) - z.re = -(z.re - 1) by ring]
      exact neg_div_neg_eq _ _
    have h2 : -y ^ (-z.re - 1 + 1) / (-z.re - 1 + 1) = y ^ (-z.re) / z.re := by
      rw [show -z.re - 1 + 1 = -z.re by ring]
      exact neg_div_neg_eq _ _
    rw [h1, h2]
  have hyid : y * (y ^ (-z.re) / z.re) = y ^ (1 - z.re) / z.re := by
    rw [show (1 : ℝ) - z.re = -z.re + 1 by ring, Real.rpow_add hy0, Real.rpow_one]
    ring
  rw [primeRemainderTail_eq hz hy, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)) ?_
  rw [hval, hyid]
  refine le_of_eq ?_
  have hne1 : z.re - 1 ≠ 0 := by intro h; linarith [h]
  have hne2 : z.re ≠ 0 := ne_of_gt hz0
  field_simp

/-! ## Changing the cut -/

theorem norm_primeVacuumTail_sub {z : ℂ} (hz : 1 < z.re) {a b : ℝ}
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    ‖primeVacuumTail z a - primeVacuumTail z b‖ ≤ (b - a) * a ^ (-z.re) := by
  have ha1 : (1 : ℝ) < a := lt_of_lt_of_le one_lt_exp_one ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hloga : (1 : ℝ) ≤ Real.log a := by
    have : Real.log (Real.exp 1) ≤ Real.log a := Real.log_le_log (Real.exp_pos 1) ha
    simpa using this
  have hint : IntegrableOn (logPowerTail z 1) (Ioi a) volume := integrableOn_logPowerTail ha1 hz
  have hdiff : primeVacuumTail z a - primeVacuumTail z b
      = ∫ t in Ioc a b, logPowerTail z 1 t := by
    rw [primeVacuumTail, primeVacuumTail, integral_Ioi_eq_sub hab hint,
      intervalIntegral.integral_of_le hab]
    ring
  rw [hdiff]
  have hmaj : IntegrableOn (fun _ : ℝ => a ^ (-z.re)) (Ioc a b) volume := by
    refine integrableOn_const ?_ ?_
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self)
        (by simp [Real.volume_Icc]))
    · simp only [enorm_eq_nnnorm]
      exact ENNReal.coe_ne_top
  have hbound : ‖∫ t in Ioc a b, logPowerTail z 1 t‖ ≤ ∫ _t in Ioc a b, a ^ (-z.re) := by
    refine norm_integral_le_of_norm_le hmaj ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := lt_trans ha1 ht.1
    have hlogt : (1 : ℝ) ≤ Real.log t :=
      le_trans hloga (Real.log_le_log ha0 ht.1.le)
    rw [norm_logPowerTail ht1, pow_one]
    have h1 : t ^ (-z.re) ≤ a ^ (-z.re) :=
      Real.rpow_le_rpow_of_nonpos ha0 ht.1.le (by linarith)
    have h2 : t ^ (-z.re) / Real.log t ≤ t ^ (-z.re) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.rpow_pos_of_pos (lt_trans ha0 ht.1) (-z.re)]
    linarith
  refine hbound.trans ?_
  rw [MeasureTheory.setIntegral_const]
  have hvol : (volume.real (Ioc a b)) • (a ^ (-z.re)) = (b - a) * a ^ (-z.re) := by
    simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]
  rw [hvol]

/-! ## The remainder current -/

/-- **Card equation (20h).**  The arithmetic remainder relative to the continuous vacuum. -/
def primeRemainderCurrent (z : ℂ) (x : ℝ) : ℂ :=
  primeTailCurrent z x - primeVacuumCurrent z x

theorem primeRemainderCurrent_eq {z : ℂ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    primeRemainderCurrent z x
      = (x : ℂ) ^ (-z)
        * (primeTailSum z (ceilCut x) - primeVacuumTail z (max (Real.exp 1) x⁻¹)) := by
  rw [primeRemainderCurrent, primeTailCurrent_eq_primeTailSum hx hx1, primeVacuumCurrent,
    show ((⌈x⁻¹⌉₊ : ℕ) : ℝ) - 1 / 2 = ceilCut x from rfl]
  ring

/-! ## A lower bound for the vacuum -/

theorem norm_primeVacuumTail_ge {z : ℂ} (hz : 1 < z.re) {y : ℝ} (hy : Real.exp 1 < y)
    (hlog : 2 / (z.re - 1) ≤ Real.log y) :
    y ^ (1 - z.re) / (2 * ‖z - 1‖ * Real.log y) ≤ ‖primeVacuumTail z y‖ := by
  have hy1 : (1 : ℝ) < y := lt_trans one_lt_exp_one hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogpos : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hzne1 : z - (1 : ℂ) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; rw [h] at hz; simp at hz
  have hnz1 : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr hzne1
  have hpowpos : (0 : ℝ) < y ^ (1 - z.re) := Real.rpow_pos_of_pos hy0 _
  have hmain : ‖(y : ℂ) ^ (1 - z) / ((z - 1) * (Real.log y : ℂ))‖
      = y ^ (1 - z.re) / (‖z - 1‖ * Real.log y) := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
      Real.norm_of_nonneg hlogpos.le]
    congr 1
  have hrem : ‖(1 / (z - 1)) * ∫ u in Ioi y, logPowerTail z 2 u‖
      ≤ y ^ (1 - z.re) / (‖z - 1‖ * ((z.re - 1) * (Real.log y) ^ 2)) := by
    rw [norm_mul, norm_div, norm_one]
    have hb := norm_integral_logPowerTail_le (k := 2) hy1 hz
    calc 1 / ‖z - 1‖ * ‖∫ u in Ioi y, logPowerTail z 2 u‖
        ≤ 1 / ‖z - 1‖ * (y ^ (1 - z.re) / ((z.re - 1) * (Real.log y) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = y ^ (1 - z.re) / (‖z - 1‖ * ((z.re - 1) * (Real.log y) ^ 2)) := by
          field_simp
  have hsplit := integral_logPowerTail_one hz hy1
  have htri : ‖primeVacuumTail z y‖
      ≥ ‖(y : ℂ) ^ (1 - z) / ((z - 1) * (Real.log y : ℂ))‖
        - ‖(1 / (z - 1)) * ∫ u in Ioi y, logPowerTail z 2 u‖ := by
    rw [primeVacuumTail, hsplit]
    exact norm_sub_norm_le _ _
  have hhalf : y ^ (1 - z.re) / (‖z - 1‖ * ((z.re - 1) * (Real.log y) ^ 2))
      ≤ y ^ (1 - z.re) / (2 * ‖z - 1‖ * Real.log y) := by
    refine div_le_div_of_nonneg_left hpowpos.le (by positivity) ?_
    have h1 : 2 ≤ (z.re - 1) * Real.log y := by
      rw [div_le_iff₀ (by linarith)] at hlog
      linarith
    have hprod : (‖z - 1‖ * Real.log y) * 2
        ≤ (‖z - 1‖ * Real.log y) * ((z.re - 1) * Real.log y) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [hprod]
  rw [hmain] at htri
  have hgap : y ^ (1 - z.re) / (‖z - 1‖ * Real.log y)
      = 2 * (y ^ (1 - z.re) / (2 * ‖z - 1‖ * Real.log y)) := by
    field_simp
  rw [hgap] at htri
  linarith [htri, hrem, hhalf]

/-! ## The flat remainder -/

/-- The half-integer cut just above `y`. -/
def cutOf (y : ℝ) : ℝ := (⌈y⌉₊ : ℝ) - 1 / 2

theorem ceilCut_inv (x : ℝ) : ceilCut x = cutOf x⁻¹ := rfl

theorem cutOf_bounds {y : ℝ} (hy : 0 ≤ y) :
    y - 1 / 2 ≤ cutOf y ∧ cutOf y < y + 1 / 2 := by
  have h1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  constructor <;> · rw [cutOf]; linarith

theorem half_le_cutOf {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ cutOf y := by
  have := (cutOf_bounds (by linarith : (0:ℝ) ≤ y)).1
  linarith

theorem norm_primeVacuumTail_sub' {z : ℂ} (hz : 1 < z.re) {a b : ℝ}
    (ha : Real.exp 1 ≤ a) (hb : Real.exp 1 ≤ b) :
    ‖primeVacuumTail z a - primeVacuumTail z b‖ ≤ |b - a| * (min a b) ^ (-z.re) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonneg (by linarith)]
    exact norm_primeVacuumTail_sub hz ha h
  · rw [min_eq_right h, abs_of_nonpos (by linarith), neg_sub]
    rw [← norm_neg, neg_sub]
    exact norm_primeVacuumTail_sub hz hb h

theorem sqrt_log_div_two_ge {y : ℝ} (hy : 2 ≤ y) :
    Real.sqrt (Real.log y) - Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log (y / 2)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hsplit : Real.log (y / 2) = Real.log y - Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num)]
  rw [hsplit]
  have hA : (0 : ℝ) ≤ Real.log y - Real.log 2 := by linarith
  have h1 : Real.sqrt (Real.log y) ^ 2 = Real.log y := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt (Real.log 2) ^ 2 = Real.log 2 := Real.sq_sqrt hlog2.le
  have h3 : Real.sqrt (Real.log y - Real.log 2) ^ 2 = Real.log y - Real.log 2 :=
    Real.sq_sqrt hA
  nlinarith [Real.sqrt_nonneg (Real.log y), Real.sqrt_nonneg (Real.log 2),
    Real.sqrt_nonneg (Real.log y - Real.log 2), h1, h2, h3,
    Real.sqrt_le_sqrt (show Real.log 2 ≤ Real.log y from hlogy)]

/-- **Card equation (20j), cut form.**  The arithmetic tail differs from the continuous vacuum by
a factor beating every power of the logarithm. -/
theorem exists_norm_remainder_at_cut_bound {z : ℂ} (hz : 1 < z.re) :
    ∃ K c : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ᶠ y : ℝ in atTop,
      ‖primeTailSum z (cutOf y) - primeVacuumTail z y‖
        ≤ K * (y ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log y)) + y ^ (-z.re)) := by
  obtain ⟨C, c, hc, hC, hEev⟩ := exists_primeTailCount_sub_logIntegralCount_bound
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp hEev
  have hz0 : (0 : ℝ) < z.re := by linarith
  set K₁ : ℝ := ‖z‖ * (C * (1 / (z.re - 1) + 1 / z.re)) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    have : (0 : ℝ) ≤ 1 / (z.re - 1) + 1 / z.re := by positivity
    positivity
  set K : ℝ := K₁ * (2 ^ (z.re - 1) * Real.exp (c * Real.sqrt (Real.log 2))) + 2 ^ z.re with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (z.re - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0 : ℝ) < (2 : ℝ) ^ z.re := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨K, c, hc, hK0, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * max (Real.exp 1) (max U 2) + 2)] with y hy
  have hmaxpos : (0 : ℝ) < max (Real.exp 1) (max U 2) :=
    lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)
  have hy2 : (2 : ℝ) ≤ y := by
    have : (2 : ℝ) ≤ max (Real.exp 1) (max U 2) := le_trans (le_max_right U 2) (le_max_right _ _)
    linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hcut : y / 2 ≤ cutOf y := half_le_cutOf hy1
  have hcutU : max (Real.exp 1) (max U 2) ≤ y / 2 - 1 := by linarith
  have hcutE : Real.exp 1 < cutOf y := by
    have h1 : Real.exp 1 ≤ max (Real.exp 1) (max U 2) := le_max_left _ _
    linarith
  have hcut2 : (2 : ℝ) ≤ cutOf y := by
    have h1 : (2 : ℝ) ≤ max (Real.exp 1) (max U 2) :=
      le_trans (le_max_right U 2) (le_max_right _ _)
    linarith
  have hcutU' : U ≤ cutOf y := by
    have h1 : U ≤ max (Real.exp 1) (max U 2) :=
      le_trans (le_max_left U 2) (le_max_right _ _)
    linarith
  have hE : ∀ u : ℝ, cutOf y ≤ u → |primeTailCount u - logIntegralCount u|
      ≤ C * (u * Real.exp (-c * Real.sqrt (Real.log u))) :=
    fun u hu => hU u (le_trans hcutU' hu)
  have h1 := norm_primeRemainderTail_le hz hc hC hcutE hE
  have hy2e : Real.exp 1 ≤ y := by
    have : Real.exp 1 ≤ max (Real.exp 1) (max U 2) := le_max_left _ _
    linarith
  have h2 := norm_primeVacuumTail_sub' hz hcutE.le hy2e
  have hsplit : primeTailSum z (cutOf y) - primeVacuumTail z y
      = primeRemainderTail z (cutOf y) + (primeVacuumTail z (cutOf y) - primeVacuumTail z y) := by
    rw [primeRemainderTail]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  -- bound the first piece
  have hpow1 : (cutOf y) ^ (1 - z.re) ≤ (y / 2) ^ (1 - z.re) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hcut (by linarith)
  have hpowval : (y / 2) ^ (1 - z.re) = 2 ^ (z.re - 1) * y ^ (1 - z.re) := by
    rw [Real.div_rpow hy0.le (by norm_num), show z.re - 1 = -(1 - z.re) by ring,
      Real.rpow_neg (by norm_num)]
    field_simp
  have hexp1 : Real.exp (-c * Real.sqrt (Real.log (cutOf y)))
      ≤ Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (-c * Real.sqrt (Real.log y)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsl : Real.sqrt (Real.log (y / 2)) ≤ Real.sqrt (Real.log (cutOf y)) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hcut)
    have hkey := sqrt_log_div_two_ge hy2
    nlinarith [hc, hsl, hkey]
  have hfirst : ‖primeRemainderTail z (cutOf y)‖
      ≤ K₁ * (2 ^ (z.re - 1) * Real.exp (c * Real.sqrt (Real.log 2)))
        * (y ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log y))) := by
    refine h1.trans ?_
    have hnn1 : (0 : ℝ) ≤ (cutOf y) ^ (1 - z.re) := (Real.rpow_pos_of_pos (by linarith) _).le
    have hnn2 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log (cutOf y))) := Real.exp_pos _
    calc K₁ * ((cutOf y) ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log (cutOf y))))
        ≤ K₁ * ((y / 2) ^ (1 - z.re)
            * (Real.exp (c * Real.sqrt (Real.log 2))
              * Real.exp (-c * Real.sqrt (Real.log y)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK₁0
          exact mul_le_mul hpow1 hexp1 hnn2.le
            (Real.rpow_pos_of_pos (by linarith) _).le
      _ = K₁ * (2 ^ (z.re - 1) * Real.exp (c * Real.sqrt (Real.log 2)))
            * (y ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log y))) := by
          rw [hpowval]; ring
  -- bound the second piece
  have hsecond : ‖primeVacuumTail z (cutOf y) - primeVacuumTail z y‖ ≤ 2 ^ z.re * y ^ (-z.re) := by
    refine h2.trans ?_
    have habs : |y - cutOf y| ≤ 1 := by
      have hb := cutOf_bounds (by linarith : (0:ℝ) ≤ y)
      rw [abs_le]
      constructor <;> linarith [hb.1, hb.2]
    have hminge : y / 2 ≤ min (cutOf y) y := le_min hcut (by linarith)
    have hminpow : (min (cutOf y) y) ^ (-z.re) ≤ (y / 2) ^ (-z.re) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hminge (by linarith)
    have hminpos : (0 : ℝ) < (min (cutOf y) y) ^ (-z.re) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le (by linarith) hminge) _
    have hval : (y / 2) ^ (-z.re) = 2 ^ z.re * y ^ (-z.re) := by
      rw [Real.div_rpow hy0.le (by norm_num), show z.re = -(-z.re) by ring,
        Real.rpow_neg (by norm_num)]
      field_simp
    calc |y - cutOf y| * (min (cutOf y) y) ^ (-z.re)
        ≤ 1 * (y / 2) ^ (-z.re) := mul_le_mul habs hminpow hminpos.le (by norm_num)
      _ = 2 ^ z.re * y ^ (-z.re) := by rw [one_mul, hval]
  have hnn : (0 : ℝ) ≤ y ^ (1 - z.re) * Real.exp (-c * Real.sqrt (Real.log y)) := by
    positivity
  have hnn2 : (0 : ℝ) ≤ y ^ (-z.re) := (Real.rpow_pos_of_pos hy0 _).le
  rw [hK]
  nlinarith [hfirst, hsecond, hnn, hnn2]

end

end RHTower
