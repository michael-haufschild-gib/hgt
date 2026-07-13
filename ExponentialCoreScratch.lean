import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSurvivalTransform
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem test_integral_exp_neg_half_mul_complexPower (m : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      ((m.factorial * 2 ^ (m + 1) : ℕ) : ℂ) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * Real.exp (-x / 2) : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  exact integral_pow_mul_exp_neg_half_complex m

theorem test_integrable_exp_neg_half_mul_complexPower (m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) (Ioi 0) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * Real.exp (-x / 2) : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  exact (integrableOn_pow_mul_exp_neg_half m).ofReal

theorem test_integral_exp_neg_half_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      2 * (-(4 * z ^ 2)) ^ (d + 1) := by
  have hbase := test_integrable_exp_neg_half_mul_complexPower 0
  have hsum : IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondSection d z x) (Ioi 0) := by
    rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondSection d z x) =
      fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondSectionSourceCoefficient z r *
          ((Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ (2 * r + 2)) by
      funext x
      rw [thetaCuspTailSecondSection_eq_sourcePowerPacket,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
    exact MeasureTheory.integrable_finsetSum _ fun r _hr =>
      (test_integrable_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
    fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ 0 -
      (z ^ 2 + 1 / 4) *
        ((Real.exp (-x / 2) : ℂ) *
          thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    simp only [pow_zero, mul_one]
    ring]
  rw [integral_sub hbase (hsum.const_mul (z ^ 2 + 1 / 4)),
    test_integral_exp_neg_half_mul_complexPower,
    MeasureTheory.integral_const_mul]
  rw [show (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) * thetaCuspTailSecondSection d z x) =
    ∑ r ∈ Finset.range (d + 1),
      thetaCuspTailSecondSectionSourceCoefficient z r *
        ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ) by
    rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondSection d z x) =
      fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondSectionSourceCoefficient z r *
          ((Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ (2 * r + 2)) by
      funext x
      rw [thetaCuspTailSecondSection_eq_sourcePowerPacket,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _hr
      rw [MeasureTheory.integral_const_mul,
        test_integral_exp_neg_half_mul_complexPower]
    · intro r _hr
      exact (test_integrable_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _]
  rw [show (∑ r ∈ Finset.range (d + 1),
      thetaCuspTailSecondSectionSourceCoefficient z r *
        ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ)) =
    8 * ∑ r ∈ Finset.range (d + 1), (-(4 * z ^ 2)) ^ r by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    unfold thetaCuspTailSecondSectionSourceCoefficient
    push_cast
    have hfac : (((2 * r + 2).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * r + 2)
    field_simp
    rw [show (-(4 * z ^ 2)) ^ r =
        (-1 : ℂ) ^ r * z ^ (2 * r) * 2 ^ (2 * r) by
      calc
        (-(4 * z ^ 2)) ^ r = ((-1 : ℂ) * z ^ 2 * 4) ^ r := by
          congr 1
          ring
        _ = (-1 : ℂ) ^ r * (z ^ 2) ^ r * (4 : ℂ) ^ r := by
          rw [mul_pow, mul_pow]
        _ = _ := by
          rw [← pow_mul]
          rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul]
          ]
    ring]
  norm_num
  calc
    2 - (z ^ 2 + 1 / 4) *
        (8 * ∑ r ∈ Finset.range (d + 1), (-(4 * z ^ 2)) ^ r) =
      2 + 2 * ((-(4 * z ^ 2)) - 1) *
        ∑ r ∈ Finset.range (d + 1), (-(4 * z ^ 2)) ^ r := by ring
    _ = 2 * (-(4 * z ^ 2)) ^ (d + 1) := by
      rw [show 2 + 2 * ((-(4 * z ^ 2)) - 1) *
          ∑ r ∈ Finset.range (d + 1), (-(4 * z ^ 2)) ^ r =
        2 + 2 * (((-(4 * z ^ 2)) - 1) *
          ∑ r ∈ Finset.range (d + 1), (-(4 * z ^ 2)) ^ r) by ring]
      rw [mul_geom_sum]
      ring

def test_expNegHalfCoreDerivativePacket (d : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (d + 1),
    thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
      ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ)

theorem test_expNegHalfCoreDerivativePacket_eq
    (d : ℕ) (z : ℂ) :
    test_expNegHalfCoreDerivativePacket d z =
      -16 * ((d + 1 : ℕ) : ℂ) * z * (-(4 * z ^ 2)) ^ d := by
  induction d with
  | zero =>
      simp [test_expNegHalfCoreDerivativePacket,
        thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient,
        thetaCuspTailSecondSectionSourceCoefficient,
        thetaCuspTailSecondSectionDerivativeSourceCoefficient]
      ring
  | succ d ih =>
      change (∑ r ∈ Finset.range ((d + 1) + 1),
        thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
          ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ)) = _
      rw [Finset.sum_range_succ]
      change test_expNegHalfCoreDerivativePacket d z + _ = _
      rw [ih]
      unfold thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient
        thetaCuspTailSecondSectionSourceCoefficient
        thetaCuspTailSecondSectionDerivativeSourceCoefficient
      have hfac : ((((2 * (d + 1) + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * (d + 1) + 2)
      push_cast
      field_simp
      push_cast
      rw [show (-(4 * z ^ 2)) ^ (d + 1) =
          (-(4 * z ^ 2)) ^ d * (-(4 * z ^ 2)) by rw [pow_succ]]
      rw [show (-1 : ℂ) ^ (d + 1) = (-1 : ℂ) ^ d * (-1) by rw [pow_succ]]
      ring

theorem test_integral_exp_neg_half_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) =
      -16 * ((d + 1 : ℕ) : ℂ) * z * (-(4 * z ^ 2)) ^ d := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
    fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
      thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
        ((Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ (2 * r + 2)) by
    funext x
    rw [thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · rw [show (∑ i ∈ Finset.range (d + 1),
        ∫ a : ℝ in Ioi 0,
          thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z i *
            ((Real.exp (-a / 2) : ℂ) * (a : ℂ) ^ (2 * i + 2))) =
      test_expNegHalfCoreDerivativePacket d z by
        unfold test_expNegHalfCoreDerivativePacket
        apply Finset.sum_congr rfl
        intro i _hi
        rw [MeasureTheory.integral_const_mul,
          test_integral_exp_neg_half_mul_complexPower]]
    exact test_expNegHalfCoreDerivativePacket_eq d z
  · intro r _hr
    exact (test_integrable_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _

theorem test_expNegHalfCore_current
    (d : ℕ) (z : ℂ) :
    ((-16 * ((d + 1 : ℕ) : ℂ) * z * (-(4 * z ^ 2)) ^ d) *
      (starRingEnd ℂ) (2 * (-(4 * z ^ 2)) ^ (d + 1))).im =
      -128 * (d + 1 : ℕ) * z.im * Complex.normSq z *
        Complex.normSq ((-(4 * z ^ 2)) ^ d) := by
  let q : ℂ := -(4 * z ^ 2)
  let w : ℂ := q ^ d
  have hsucc : q ^ (d + 1) = w * q := by
    dsimp only [w]
    rw [pow_succ]
  have hw : w * (starRingEnd ℂ) w = (Complex.normSq w : ℂ) := by
    rw [Complex.normSq_apply]
    norm_num
  rw [show (-(4 * z ^ 2)) ^ d = w by rfl,
    show (-(4 * z ^ 2)) ^ (d + 1) = w * q by exact hsucc,
    map_mul]
  rw [show ((-16 * ((d + 1 : ℕ) : ℂ) * z * w) *
      (starRingEnd ℂ) (2 * (w * q))) =
    (-32 * ((d + 1 : ℕ) : ℂ)) *
      (w * (starRingEnd ℂ) w) *
        (z * (starRingEnd ℂ) q) by
      simp only [map_ofNat]
      ring]
  rw [hw]
  dsimp only [q, w]
  simp [Complex.normSq_apply, Complex.mul_im, Complex.mul_re]
  ring

end

end RHTower
