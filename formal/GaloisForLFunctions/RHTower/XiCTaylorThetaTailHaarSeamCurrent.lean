import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedSurvivalTransform
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Exact exponential channel in the cofinal Haar seam

The cofinal reflected Haar identity leaves an elementary `exp (-x/2)` source channel.  Its value
and spectral-derivative transforms against the finite theta-tail core are exactly the leading
monomial and its derivative.  In the upper half-plane that monomial current is strictly negative;
therefore the negative source-square coefficient contributes positive current.  The exponential
square cannot be assigned a favorable sign before it is coupled to the remote top row.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem integral_exp_neg_half_mul_complexPower (m : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      ((m.factorial * 2 ^ (m + 1) : ℕ) : ℂ) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * Real.exp (-x / 2) : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  exact integral_pow_mul_exp_neg_half_complex m

theorem integrableOn_exp_neg_half_mul_complexPower (m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) (Ioi 0) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * Real.exp (-x / 2) : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  exact (integrableOn_pow_mul_exp_neg_half m).ofReal

theorem integral_exp_neg_half_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      2 * (-(4 * z ^ 2)) ^ (d + 1) := by
  have hbase := integrableOn_exp_neg_half_mul_complexPower 0
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
      (integrableOn_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _
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
    integral_exp_neg_half_mul_complexPower,
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
        integral_exp_neg_half_mul_complexPower]
    · intro r _hr
      exact (integrableOn_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _]
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

def expNegHalfCoreDerivativePacket (d : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (d + 1),
    thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
      ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ)

theorem expNegHalfCoreDerivativePacket_eq
    (d : ℕ) (z : ℂ) :
    expNegHalfCoreDerivativePacket d z =
      -16 * ((d + 1 : ℕ) : ℂ) * z * (-(4 * z ^ 2)) ^ d := by
  induction d with
  | zero =>
      simp [expNegHalfCoreDerivativePacket,
        thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient,
        thetaCuspTailSecondSectionSourceCoefficient,
        thetaCuspTailSecondSectionDerivativeSourceCoefficient]
      ring
  | succ d ih =>
      change (∑ r ∈ Finset.range ((d + 1) + 1),
        thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
          ((2 * r + 2).factorial * 2 ^ (2 * r + 3) : ℕ)) = _
      rw [Finset.sum_range_succ]
      change expNegHalfCoreDerivativePacket d z + _ = _
      rw [ih]
      unfold thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient
        thetaCuspTailSecondSectionSourceCoefficient
        thetaCuspTailSecondSectionDerivativeSourceCoefficient
      have hfac : ((((2 * (d + 1) + 2).factorial : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * (d + 1) + 2)
      push_cast
      field_simp
      let A : ℂ := (-1 : ℂ) ^ d * (4 : ℂ) ^ d * z ^ (2 * d)
      have hqd : (-(z ^ 2 * 4)) ^ d = A := by
        dsimp only [A]
        calc
          (-(z ^ 2 * 4)) ^ d = ((-1 : ℂ) * z ^ 2 * 4) ^ d := by
            congr 1
            ring
          _ = (-1 : ℂ) ^ d * (z ^ 2) ^ d * (4 : ℂ) ^ d := by
            rw [mul_pow, mul_pow]
          _ = _ := by rw [← pow_mul]; ring
      have hqd1 : (-(z ^ 2 * 4)) ^ (d + 1) = -4 * z ^ 2 * A := by
        rw [pow_succ, hqd]
        dsimp only [A]
        ring
      have hzEven : z ^ (2 * (d + 1)) = z ^ (2 * d) * z ^ 2 := by
        rw [show 2 * (d + 1) = 2 * d + 2 by omega, pow_add]
      have hzOdd : z ^ (2 * (d + 1) - 1) = z ^ (2 * d) * z := by
        rw [show 2 * (d + 1) - 1 = 2 * d + 1 by omega, pow_add]
        ring
      have hsign : (-1 : ℂ) ^ (d + 1) = (-1 : ℂ) ^ d * (-1) := by
        rw [pow_succ]
      have htwo : (2 : ℂ) ^ (2 * (d + 1) + 3) = 32 * (4 : ℂ) ^ d := by
        rw [show 2 * (d + 1) + 3 = 2 * d + 5 by omega, pow_add]
        rw [show (2 : ℂ) ^ (2 * d) = (4 : ℂ) ^ d by
          calc
            (2 : ℂ) ^ (2 * d) = (2 ^ 2 : ℂ) ^ d := by
              rw [← pow_mul]
            _ = (4 : ℂ) ^ d := by norm_num]
        norm_num
        ring
      rw [hqd, hqd1, hzEven, hzOdd, hsign, htwo]
      dsimp only [A]
      ring

theorem integral_exp_neg_half_mul_coreAtomDerivative
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
      expNegHalfCoreDerivativePacket d z by
        unfold expNegHalfCoreDerivativePacket
        apply Finset.sum_congr rfl
        intro i _hi
        rw [MeasureTheory.integral_const_mul,
          integral_exp_neg_half_mul_complexPower]]
    exact expNegHalfCoreDerivativePacket_eq d z
  · intro r _hr
    exact (integrableOn_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _

theorem expNegHalfCore_current
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
    apply Complex.ext
    · simp [Complex.normSq_apply, Complex.mul_re]
    · simp [Complex.normSq_apply, Complex.mul_im]
      ring
  have hzq : (z * (starRingEnd ℂ) q).im =
      4 * z.im * Complex.normSq z := by
    have hconj : (starRingEnd ℂ) q =
        -(4 * ((starRingEnd ℂ) z) ^ 2) := by
      dsimp only [q]
      simp only [map_neg, map_mul, map_ofNat, map_pow]
    rw [hconj]
    simp [pow_two, Complex.normSq_apply, Complex.mul_im, Complex.mul_re]
    ring
  rw [show (-(4 * z ^ 2)) ^ d = w by rfl,
    show (-(4 * z ^ 2)) ^ (d + 1) = w * q by exact hsucc,
    map_mul]
  simp only [map_ofNat]
  rw [show ((-16 * ((d + 1 : ℕ) : ℂ) * z * w) *
      (2 * (starRingEnd ℂ) (w * q))) =
    (-32 * ((d + 1 : ℕ) : ℂ)) *
      (w * (starRingEnd ℂ) w) *
        (z * (starRingEnd ℂ) q) by
      rw [map_mul]
      ring]
  rw [hw]
  rw [show (-32 * ((d + 1 : ℕ) : ℂ)) * (Complex.normSq w : ℂ) *
      (z * (starRingEnd ℂ) q) =
    (((-32 : ℝ) * ((d + 1 : ℕ) : ℝ) * Complex.normSq w : ℝ) : ℂ) *
      (z * (starRingEnd ℂ) q) by
        push_cast
        ring]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  change (-32 : ℝ) * ((d + 1 : ℕ) : ℝ) * Complex.normSq w *
      (z * (starRingEnd ℂ) q).im = _
  rw [hzq]
  ring

end

end RHTower
