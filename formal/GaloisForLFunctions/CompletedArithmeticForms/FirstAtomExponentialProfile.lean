import GaloisForLFunctions.CompletedArithmeticForms.BesselTailCoshMoment
import GaloisForLFunctions.CompletedArithmeticForms.ExponentialPowerTail

/-!
# Positive polynomial representation of the averaged first atom

The signed exponential profile is the tail of a square plus a positive
linear correction. The endpoint recurrence retains every subtraction.
-/

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Moving the cutoff of an exponential power tail preserves measurability. -/
theorem stronglyMeasurable_exponentialPowerTail (p c : ℝ) :
    StronglyMeasurable (exponentialPowerTail p c) := by
  have hm : StronglyMeasurable (fun z : ℝ × ℝ =>
      ({z : ℝ × ℝ | z.1 < z.2}).indicator
        (fun z => z.2 ^ p * Real.exp (-c * z.2)) z) := by
    apply Measurable.stronglyMeasurable
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ => z.2 ^ p * Real.exp (-c * z.2))).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hi := hm.integral_prod_right' (ν := volume)
  change StronglyMeasurable (fun q : ℝ =>
    ∫ u : ℝ, (Ioi q).indicator (fun u : ℝ => u ^ p * Real.exp (-c * u)) u) at hi
  change StronglyMeasurable (fun q : ℝ => ∫ u in Ioi q, u ^ p * Real.exp (-c * u))
  simpa only [integral_indicator measurableSet_Ioi] using hi

/-- Every convergent positive-ray exponential tail is strictly positive. -/
theorem exponentialPowerTail_pos {p c q : ℝ}
    (hp : -1 < p) (hc : 0 < c) (hq : 0 ≤ q) :
    0 < exponentialPowerTail p c q := by
  have hsupp : (Function.support (fun u : ℝ => u ^ p * Real.exp (-c * u))) ∩ Ioi q = Ioi q := by
    rw [inter_eq_right]
    intro u hu
    exact (mul_pos (Real.rpow_pos_of_pos (hq.trans_lt hu) _) (Real.exp_pos _)).ne'
  rw [exponentialPowerTail, setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hsupp, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (hq.trans hu.le) _) (Real.exp_pos _).le
  · exact integrableOn_exponentialPowerIntegrand hp hc hq

/-- Simultaneously rescaling the rate and cutoff retains the complete power factor. -/
theorem exponentialPowerTail_scale (p c : ℝ) {N q : ℝ}
    (hN : 0 < N) (hq : 0 ≤ q) :
    exponentialPowerTail p (c / N) (N * q) =
      N ^ (p + 1) * exponentialPowerTail p c q := by
  have h := integral_comp_mul_left_Ioi
    (fun u : ℝ => u ^ p * Real.exp (-(c / N) * u)) q hN
  simp only [smul_eq_mul] at h
  have he : (∫ u in Ioi q, (N * u) ^ p * Real.exp (-(c / N) * (N * u))) =
      N ^ p * exponentialPowerTail p c q := by
    rw [exponentialPowerTail, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [Real.mul_rpow hN.le (hq.trans hu.le)]
    have hcN : -(c / N) * (N * u) = -c * u := by field_simp [hN.ne']
    rw [hcN]
    ring
  rw [he] at h
  change N ^ p * exponentialPowerTail p c q =
    N⁻¹ * exponentialPowerTail p (c / N) (N * q) at h
  rw [Real.rpow_add hN, Real.rpow_one]
  have hm := congrArg (fun x : ℝ => N * x) h
  rw [← mul_assoc N N⁻¹, mul_inv_cancel₀ hN.ne', one_mul] at hm
  exact hm.symm.trans (by ring)

/-- The averaged profile retains its two signed tails and endpoint. -/
theorem besselFirstAtomExponentialTail_eq_signedPowerTails (c q : ℝ) :
    besselFirstAtomExponentialTail c q =
      4 * exponentialPowerTail (7 / 2) (2 * c) q -
        6 * exponentialPowerTail (3 / 2) (2 * c) q -
        6 * q ^ (5 / 2 : ℝ) * Real.exp (-2 * c * q) := by
  simp only [besselFirstAtomExponentialTail, exponentialPowerTail, neg_mul, mul_assoc]

/-- The entire averaged profile is measurable in its radial cutoff. -/
theorem stronglyMeasurable_besselFirstAtomExponentialTail (c : ℝ) :
    StronglyMeasurable (besselFirstAtomExponentialTail c) := by
  have he : StronglyMeasurable (fun q : ℝ => 6 * q ^ (5 / 2 : ℝ) * Real.exp (-2 * c * q)) :=
    (by fun_prop : Measurable (fun q : ℝ => 6 * q ^ (5 / 2 : ℝ) * Real.exp (-2 * c * q))).stronglyMeasurable
  have h := (((stronglyMeasurable_exponentialPowerTail (7 / 2) (2 * c)).const_mul (4 : ℝ)).sub
    ((stronglyMeasurable_exponentialPowerTail (3 / 2) (2 * c)).const_mul (6 : ℝ))).sub he
  convert h using 1
  funext q
  exact besselFirstAtomExponentialTail_eq_signedPowerTails c q

/-- The endpoint subtraction is exactly absorbed into three power tails. -/
theorem besselFirstAtomExponentialTail_eq_powerTails {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    besselFirstAtomExponentialTail c q =
      4 * exponentialPowerTail (7 / 2) (2 * c) q -
        12 * c * exponentialPowerTail (5 / 2) (2 * c) q +
        9 * exponentialPowerTail (3 / 2) (2 * c) q := by
  have ht := exponentialPowerTail_recurrence
    (by norm_num : (0 : ℝ) < 5 / 2) (by positivity : 0 < 2 * c) hq
  norm_num only [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at ht
  unfold besselFirstAtomExponentialTail exponentialPowerTail at *
  simp only [neg_mul, mul_assoc] at ht ⊢
  linarith only [ht]

/-- Expanding the radial square gives the three adjacent half-integer powers. -/
theorem exponentialProfile_rpow_polynomial_identity {u : ℝ} (hu : 0 < u) (c : ℝ) :
    u ^ (3 / 2 : ℝ) * ((2 * u - 3) ^ 2 + 12 * (1 - c) * u) =
      4 * u ^ (7 / 2 : ℝ) - 12 * c * u ^ (5 / 2 : ℝ) + 9 * u ^ (3 / 2 : ℝ) := by
  have h5 : u ^ (5 / 2 : ℝ) = u ^ (3 / 2 : ℝ) * u := by
    calc
      _ = u ^ ((3 / 2 : ℝ) + 1) := by norm_num
      _ = u ^ (3 / 2 : ℝ) * u ^ (1 : ℝ) := Real.rpow_add hu _ _
      _ = _ := by rw [Real.rpow_one]
  have h7 : u ^ (7 / 2 : ℝ) = u ^ (3 / 2 : ℝ) * u ^ (2 : ℕ) := by
    calc
      _ = u ^ ((3 / 2 : ℝ) + 2) := by norm_num
      _ = u ^ (3 / 2 : ℝ) * u ^ (2 : ℝ) := Real.rpow_add hu _ _
      _ = _ := by rw [Real.rpow_two]
  rw [h5, h7]
  ring

/-- A square and a linear correction give the exact averaged radial profile. -/
theorem besselFirstAtomExponentialTail_eq_polynomial {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    besselFirstAtomExponentialTail c q =
      ∫ u in Ioi q, u ^ (3 / 2 : ℝ) *
        ((2 * u - 3) ^ 2 + 12 * (1 - c) * u) * Real.exp (-2 * c * u) := by
  have h7 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 7 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (4 : ℝ)
  have h5 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 5 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (12 * c)
  have h3 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 3 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (9 : ℝ)
  have he : (∫ u in Ioi q, u ^ (3 / 2 : ℝ) *
      ((2 * u - 3) ^ 2 + 12 * (1 - c) * u) * Real.exp (-2 * c * u)) =
      ∫ u in Ioi q,
        4 * (u ^ (7 / 2 : ℝ) * Real.exp (-(2 * c) * u)) -
          (12 * c) * (u ^ (5 / 2 : ℝ) * Real.exp (-(2 * c) * u)) +
          9 * (u ^ (3 / 2 : ℝ) * Real.exp (-(2 * c) * u)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [exponentialProfile_rpow_polynomial_identity (hq.trans hu)]
    simp only [neg_mul, mul_assoc]
    ring
  rw [he]
  have hs := integral_sub h7 h5
  have ha := integral_add (h7.sub h5) h3
  simp only [Pi.sub_apply] at ha hs
  rw [ha, hs, integral_const_mul, integral_const_mul, integral_const_mul,
    besselFirstAtomExponentialTail_eq_powerTails hc hq]
  rfl

/-- Every subcritical averaged radial profile is nonnegative on the whole positive ray. -/
theorem besselFirstAtomExponentialTail_nonneg {c q : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hq : 0 < q) :
    0 ≤ besselFirstAtomExponentialTail c q := by
  rw [besselFirstAtomExponentialTail_eq_polynomial hc hq]
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hq.trans hu).le _)
    (add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hc1)) (hq.trans hu).le)))
    (Real.exp_pos _).le

/-- The signed profile is bounded above by its highest power tail. -/
theorem besselFirstAtomExponentialTail_le (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    besselFirstAtomExponentialTail c q ≤ 4 * exponentialPowerTail (7 / 2) (2 * c) q := by
  rw [besselFirstAtomExponentialTail_eq_signedPowerTails]
  have h3 := exponentialPowerTail_nonneg (3 / 2) (2 * c) hq
  have hq5 : 0 ≤ q ^ (5 / 2 : ℝ) * Real.exp (-2 * c * q) :=
    mul_nonneg (Real.rpow_nonneg hq _) (Real.exp_pos _).le
  linarith only [h3, hq5]

/-- A radial power pays the cutoff dependence while retaining exponential product decay. -/
theorem besselFirstAtomExponentialTail_raise_upper {c q α : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hα : 0 ≤ α) :
    q ^ α * besselFirstAtomExponentialTail c q ≤
      4 * (Real.exp (-c * q) *
        ((1 / c) ^ (7 / 2 + α + 1) * Real.Gamma (7 / 2 + α + 1))) := by
  calc
    _ ≤ q ^ α * (4 * exponentialPowerTail (7 / 2) (2 * c) q) :=
      mul_le_mul_of_nonneg_left (besselFirstAtomExponentialTail_le c hq.le)
        (Real.rpow_nonneg hq.le _)
    _ = 4 * (q ^ α * exponentialPowerTail (7 / 2) (2 * c) q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (exponentialPowerTail_raise_upper (by norm_num : (-1 : ℝ) < 7 / 2) hc hq hα)
      (by norm_num)

end GaloisForLFunctions.CompletedArithmeticForms

