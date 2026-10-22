import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard

/-!
# All exponential moments of the Hedenmalm theta source

The theta source is superexponentially small at both ends.  This module upgrades the coarse
unit-strip estimate to the exact statement needed by the source inverse: every real exponential
tilt is integrable.  On the positive half-line a real tilt is dominated by a larger natural tilt.
Natural tilts are absorbed exactly into the polynomial part of the first theta atom, while the
established first-atom domination controls the full source.  Reflection supplies the negative
half-line.
-/

open MeasureTheory Set Polynomial

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

open HedenmalmQuantile

set_option maxHeartbeats 4000000

/-- Multiplication of the first theta atom by a natural exponential tilt is exactly polynomial
multiplication by the corresponding monomial. -/
theorem exp_nat_mul_thetaCuspSourceTerm_one_eq_polynomialAtom
    (m : ℕ) (x : ℝ) :
    Real.exp ((m : ℝ) * x) * thetaCuspSourceTerm x 1 =
      thetaCuspPolynomialAtom (X ^ m * thetaCuspSeedPolynomial) 1 x := by
  rw [congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
  simp only [thetaCuspPolynomialAtom, eval_mul, eval_pow, eval_X, Nat.cast_one, one_mul]
  have hexp : Real.exp ((m : ℝ) * x) = Real.exp x ^ m := by
    rw [← Real.exp_nat_mul]
  rw [hexp]
  ring

/-- Every natural exponential tilt of the theta source is integrable on the positive ray. -/
theorem integrableOn_exp_nat_mul_thetaCuspFullSource (m : ℕ) :
    IntegrableOn
      (fun x : ℝ => Real.exp ((m : ℝ) * x) * thetaCuspFullSource x)
      (Ioi 0) := by
  let W : ℝ := thetaCuspHigherAtomDominationWeight
  let first : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let major : ℝ → ℝ := fun x =>
    (1 + W) * (Real.exp ((m : ℝ) * x) * first x)
  have hW : 0 ≤ W := thetaCuspHigherAtomDominationWeight_nonneg
  have hfirst : IntegrableOn
      (fun x : ℝ => Real.exp ((m : ℝ) * x) * first x) (Ioi 0) := by
    have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      0 (X ^ m * thetaCuspSeedPolynomial) (n := 1) (by norm_num)
    apply h.congr_fun _ measurableSet_Ioi
    intro x _
    dsimp only [first]
    rw [exp_nat_mul_thetaCuspSourceTerm_one_eq_polynomialAtom]
    simp
  have hmajor : IntegrableOn major (Ioi 0) := hfirst.const_mul (1 + W)
  apply Integrable.mono hmajor
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hfirst0 : 0 ≤ first x := thetaCuspSourceTerm_nonneg_of_pos hx 1
    have hsource0 : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    have hsource : thetaCuspFullSource x ≤ (1 + W) * first x := by
      have htail := thetaCuspFullSource_sub_first_le hx0
      dsimp only [W, first] at htail ⊢
      linarith
    have hcoef : 0 ≤ 1 + W := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsource0),
      abs_of_nonneg (mul_nonneg hcoef
        (mul_nonneg (Real.exp_pos _).le hfirst0))]
    calc
      Real.exp ((m : ℝ) * x) * thetaCuspFullSource x ≤
          Real.exp ((m : ℝ) * x) * ((1 + W) * first x) :=
        mul_le_mul_of_nonneg_left hsource (Real.exp_pos _).le
      _ = (1 + W) * (Real.exp ((m : ℝ) * x) * first x) := by ring

/-- Every real exponential tilt of the theta source is integrable on the positive ray. -/
theorem integrableOn_exp_mul_thetaCuspFullSource (a : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x) * thetaCuspFullSource x) (Ioi 0) := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt a
  have hmajor : IntegrableOn
      (fun x : ℝ => Real.exp ((m : ℝ) * x) * thetaCuspFullSource x) (Ioi 0) :=
    integrableOn_exp_nat_mul_thetaCuspFullSource m
  apply Integrable.mono hmajor
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hsource0 : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsource0),
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsource0)]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm.le hx.le)) hsource0

/-- **All-shift theorem.**  The Hedenmalm theta source has every real exponential moment. -/
theorem integrable_exp_mul_thetaCuspFullSource (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * x) * thetaCuspFullSource x) := by
  have hpos := integrableOn_exp_mul_thetaCuspFullSource a
  have hreflect : IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x) * thetaCuspFullSource x) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_thetaCuspFullSource (-a)
  have hreflect' : IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x) * thetaCuspFullSource x) (Ici (-(0 : ℝ))) := by
    simpa using hreflect
  have hnegRaw := hreflect'.comp_neg_Iic (c := (0 : ℝ))
  have hneg : IntegrableOn
      (fun x : ℝ => Real.exp (a * x) * thetaCuspFullSource x) (Iic 0) := by
    apply hnegRaw.congr_fun _ measurableSet_Iic
    intro x _
    simp only [thetaCuspFullSource_neg]
    congr 2
    ring
  simpa [Iic_union_Ioi] using hneg.union hpos

/-- A symmetric exponential envelope is integrable at every real rate. -/
theorem integrable_exp_abs_mul_thetaCuspFullSource (b : ℝ) :
    Integrable (fun x : ℝ =>
      Real.exp (b * |x|) * thetaCuspFullSource x) := by
  have hmajor := (integrable_exp_mul_thetaCuspFullSource b).add
    (integrable_exp_mul_thetaCuspFullSource (-b))
  apply Integrable.mono hmajor
  · exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    have hk : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have hexp : Real.exp (b * |x|) ≤
        Real.exp (b * x) + Real.exp ((-b) * x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_nonpos hx]
        have heq : b * -x = (-b) * x := by ring
        rw [heq]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hk),
      abs_of_nonneg (add_nonneg
        (mul_nonneg (Real.exp_pos _).le hk)
        (mul_nonneg (Real.exp_pos _).le hk))]
    calc
      Real.exp (b * |x|) * thetaCuspFullSource x ≤
          (Real.exp (b * x) + Real.exp ((-b) * x)) * thetaCuspFullSource x :=
        mul_le_mul_of_nonneg_right hexp hk
      _ = Real.exp (b * x) * thetaCuspFullSource x +
          Real.exp ((-b) * x) * thetaCuspFullSource x := by ring

/-- One source-coordinate factor is absorbed by one additional symmetric exponential tilt. -/
theorem integrable_abs_mul_exp_abs_mul_thetaCuspFullSource (b : ℝ) :
    Integrable (fun x : ℝ =>
      |x| * Real.exp (b * |x|) * thetaCuspFullSource x) := by
  have hmajor := integrable_exp_abs_mul_thetaCuspFullSource (b + 1)
  apply Integrable.mono hmajor
  · exact ((continuous_abs.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).mul
        contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  · filter_upwards with x
    have hk : 0 ≤ thetaCuspFullSource x := (thetaCuspFullSource_pos x).le
    have hxexp : |x| ≤ Real.exp |x| := by
      calc
        |x| ≤ |x| + 1 := by linarith
        _ ≤ Real.exp |x| := Real.add_one_le_exp |x|
    have hbound : |x| * Real.exp (b * |x|) ≤
        Real.exp ((b + 1) * |x|) := by
      calc
        |x| * Real.exp (b * |x|) ≤
            Real.exp |x| * Real.exp (b * |x|) :=
          mul_le_mul_of_nonneg_right hxexp (Real.exp_pos _).le
        _ = Real.exp ((b + 1) * |x|) := by
          rw [← Real.exp_add]
          congr 1
          ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le) hk),
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hk)]
    exact mul_le_mul_of_nonneg_right hbound hk

/-- The quantile source tail condition holds at every complex spectral parameter. -/
theorem hasShiftedTail_thetaSource_all (z : ℂ) : HasShiftedTail thetaSource z := by
  rw [HasShiftedTail]
  refine (integrable_exp_mul_thetaCuspFullSource (-z.im)).congr ?_
  filter_upwards with x
  simp only [thetaSource_k, neg_mul]
  ring

end HedenmalmThetaSource

end

end RHTower
