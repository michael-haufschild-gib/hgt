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
      simp
    rw [hpowrw]
    have hstep : u ^ (-z.re - 1) * |primeTailCount u - logIntegralCount u
        - (primeTailCount y - logIntegralCount y)|
        ≤ u ^ (-z.re - 1) * (C * (u * E) + C * (y * E)) :=
      mul_le_mul_of_nonneg_left hbd (Real.rpow_pos_of_pos hu0 _).le
    refine hstep.trans ?_
    have hsplit : u ^ (-z.re - 1) * u = u ^ (-z.re) := by
      rw [← Real.rpow_neg_one u, ← Real.rpow_add hu0] at *
      rw [show u ^ (-z.re - 1) * u = u ^ (-z.re - 1) * u ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hu0]
      congr 1
      ring
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
    congr 2
    · rw [show -z.re + 1 = 1 - z.re by ring, show z.re - 1 = -(1 - z.re) by ring, div_neg, neg_div]
    · congr 1
      rw [show -z.re - 1 + 1 = -z.re by ring, show z.re = -(-z.re) by ring, div_neg, neg_div]
  have hyid : y * (y ^ (-z.re) / z.re) = y ^ (1 - z.re) / z.re := by
    rw [show (1 : ℝ) - z.re = -z.re + 1 by ring, Real.rpow_add hy0, Real.rpow_one]
    ring
  rw [primeRemainderTail_eq hz hy, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)) ?_
  rw [hval, hyid]
  have hrw : C * E * (y ^ (1 - z.re) / (z.re - 1) + y ^ (1 - z.re) / z.re)
      = C * (1 / (z.re - 1) + 1 / z.re) * (y ^ (1 - z.re) * E) := by
    field_simp
    ring
  rw [hrw]

end

end RHTower
