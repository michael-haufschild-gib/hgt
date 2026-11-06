import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail

/-!
# Real exponential power tails

Gamma mass and an exact endpoint recurrence control exponential profiles
arising from positive frequency averages.
-/

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- A real-power tail with positive exponential rate. -/
def exponentialPowerTail (p c q : ℝ) : ℝ :=
  ∫ u in Ioi q, u ^ p * Real.exp (-c * u)

/-- Powers greater than minus one are integrable on every nonnegative tail. -/
theorem integrableOn_exponentialPowerIntegrand {p c q : ℝ}
    (hp : -1 < p) (hc : 0 < c) (hq : 0 ≤ q) :
    IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-c * u)) (Ioi q) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow hp
    (show (1 : ℝ) ≤ 1 from le_rfl) hc
  simp only [Real.rpow_one] at hi
  exact hi.mono_set (fun u hu => hq.trans_lt hu)

/-- The complete positive-ray mass is a scaled Gamma value. -/
theorem exponentialPowerTail_zero {p c : ℝ} (hp : -1 < p) (hc : 0 < c) :
    exponentialPowerTail p c 0 = (1 / c) ^ (p + 1) * Real.Gamma (p + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by linarith only [hp] : 0 < p + 1) hc
  simpa only [add_sub_cancel_right, neg_mul, exponentialPowerTail] using h

theorem exponentialPowerTail_nonneg (p c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ exponentialPowerTail p c q := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (Real.rpow_nonneg (hq.trans hu.le) _) (Real.exp_pos _).le

/-- Splitting the exponential retains both tail decay and the complete Gamma scale. -/
theorem exponentialPowerTail_split_upper {p c q : ℝ}
    (hp : -1 < p) (hc : 0 < c) (hq : 0 ≤ q) :
    exponentialPowerTail p (2 * c) q ≤
      Real.exp (-c * q) * ((1 / c) ^ (p + 1) * Real.Gamma (p + 1)) := by
  have hi := integrableOn_exponentialPowerIntegrand hp hc hq
  have h2 := integrableOn_exponentialPowerIntegrand hp (by positivity : 0 < 2 * c) hq
  have hbound : exponentialPowerTail p (2 * c) q ≤
      Real.exp (-c * q) * exponentialPowerTail p c q := by
    rw [exponentialPowerTail, exponentialPowerTail, ← integral_const_mul]
    apply setIntegral_mono_on h2 (hi.const_mul _) measurableSet_Ioi
    intro u hu
    have he : Real.exp (-c * u) ≤ Real.exp (-c * q) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.le (neg_nonpos.mpr hc.le))
    have hsplit : Real.exp (-(2 * c) * u) =
        Real.exp (-c * u) * Real.exp (-c * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    calc
      _ = Real.exp (-c * u) * (u ^ p * Real.exp (-c * u)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he
        (mul_nonneg (Real.rpow_nonneg (hq.trans hu.le) _) (Real.exp_pos _).le)
  have htail : exponentialPowerTail p c q ≤ exponentialPowerTail p c 0 := by
    apply setIntegral_mono_set (integrableOn_exponentialPowerIntegrand hp hc le_rfl)
      ?_ (Filter.Eventually.of_forall fun u hu => hq.trans_lt hu)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  rw [exponentialPowerTail_zero hp hc] at htail
  exact hbound.trans (mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le)

/-- Raising the radial power pays an arbitrary nonnegative cutoff power. -/
theorem exponentialPowerTail_raise_upper {p c q α : ℝ}
    (hp : -1 < p) (hc : 0 < c) (hq : 0 < q) (hα : 0 ≤ α) :
    q ^ α * exponentialPowerTail p (2 * c) q ≤
      Real.exp (-c * q) * ((1 / c) ^ (p + α + 1) * Real.Gamma (p + α + 1)) := by
  have hpa : -1 < p + α := by linarith only [hp, hα]
  have hraise : q ^ α * exponentialPowerTail p (2 * c) q ≤
      exponentialPowerTail (p + α) (2 * c) q := by
    rw [exponentialPowerTail, exponentialPowerTail, ← integral_const_mul]
    apply setIntegral_mono_on
      ((integrableOn_exponentialPowerIntegrand hp (by positivity) hq.le).const_mul _)
      (integrableOn_exponentialPowerIntegrand hpa (by positivity) hq.le) measurableSet_Ioi
    intro u hu
    have hu0 := hq.trans hu
    calc
      _ ≤ u ^ α * (u ^ p * Real.exp (-(2 * c) * u)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hq.le hu.le hα)
          (mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.exp_pos _).le)
      _ = _ := by
        rw [← mul_assoc, ← Real.rpow_add hu0, add_comm α p]
  exact hraise.trans (exponentialPowerTail_split_upper hpa hc hq.le)

/-- Integration by parts retains the complete lower endpoint. -/
theorem exponentialPowerTail_recurrence {p c q : ℝ}
    (hp : 0 < p) (hc : 0 < c) (hq : 0 < q) :
    p * exponentialPowerTail (p - 1) c q - c * exponentialPowerTail p c q =
      -(q ^ p * Real.exp (-c * q)) := by
  have hi1 := (integrableOn_exponentialPowerIntegrand
    (by linarith only [hp] : -1 < p - 1) hc hq.le).const_mul p
  have hi2 := (integrableOn_exponentialPowerIntegrand
    (by linarith only [hp] : -1 < p) hc hq.le).const_mul c
  have hd (u : ℝ) (hu : u ∈ Ici q) :
      HasDerivAt (fun v : ℝ => v ^ p * Real.exp (-c * v))
        (p * (u ^ (p - 1) * Real.exp (-c * u)) -
          c * (u ^ p * Real.exp (-c * u))) u := by
    have hu0 : 0 < u := hq.trans_le hu
    have hr : HasDerivAt (fun v : ℝ => v ^ p) (p * u ^ (p - 1)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
    have he := ((hasDerivAt_id u).const_mul (-c)).exp
    exact (hr.mul he).congr_deriv (by simp only [id_eq]; ring)
  have hl := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p c hc
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hi1.sub hi2) hl
  have hs := integral_sub hi1 hi2
  rw [hs, integral_const_mul, integral_const_mul] at ht
  simpa only [exponentialPowerTail, zero_sub] using ht

end GaloisForLFunctions.CompletedArithmeticForms

