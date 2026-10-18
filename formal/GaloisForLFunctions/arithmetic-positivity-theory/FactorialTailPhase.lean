import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPrimitive
import GaloisForLFunctions.RHTower.ArithmeticClockFirstVariation

/-! Quantitative phase control for the literal factorial correction tail.
The periodic remainder is bounded and Lipschitz before composition with the
exponential arithmetic clock. Combining those bounds controls squared increments
without differentiating across integer joins. -/

open Set
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

private theorem collar_le_one (n : ℕ) : sourceFactorialCollar (n+1) ≤ 1 := by
  have h := sourceFactorialCollar_budget (N := n+1) (by omega)
  have he := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hN : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

private theorem remainder_gap {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |clampedLatticeRemainder u-clampedLatticeRemainder v| ≤ 1/8 := by
  obtain ⟨hu0,hu1⟩ := clampedLatticeRemainder_bounds hu
  obtain ⟨hv0,hv1⟩ := clampedLatticeRemainder_bounds hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem remainder_lipschitz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |clampedLatticeRemainder u-clampedLatticeRemainder v| ≤ |u-v|/2 := by
  rw [clampedLatticeRemainder_eq_neg_bernoulli hu,
    clampedLatticeRemainder_eq_neg_bernoulli hv, neg_sub_neg, abs_sub_comm]
  exact RHTower.DeletionMixedRefinement.bernoulliPeriodic_lipschitz_bound u v

private theorem tail_remainder_abs_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |factorialMuntzTailRemainder n u| ≤ 25/32 := by
  have he := sourceFactorialCollar_pos (N := n+1) (by omega)
  have h4 := remainder_gap (u := 4*(1+sourceFactorialCollar (n+1))*u)
    (v := 4*u) (by positivity) (by positivity)
  have h2 := remainder_gap (u := 2*(1+sourceFactorialCollar (n+1))*u)
    (v := 2*u) (by positivity) (by positivity)
  have h1 := remainder_gap (u := (1+sourceFactorialCollar (n+1))*u)
    (v := u) (by positivity) hu
  unfold factorialMuntzTailRemainder
  calc
    _ ≤ |(clampedLatticeRemainder (4*(1+sourceFactorialCollar (n+1))*u)-
        clampedLatticeRemainder (4*u))/4-
        2*(clampedLatticeRemainder (2*(1+sourceFactorialCollar (n+1))*u)-
          clampedLatticeRemainder (2*u))|+
        |4*(clampedLatticeRemainder ((1+sourceFactorialCollar (n+1))*u)-
          clampedLatticeRemainder u)| := abs_add_le _ _
    _ ≤ |(clampedLatticeRemainder (4*(1+sourceFactorialCollar (n+1))*u)-
        clampedLatticeRemainder (4*u))/4|+
        |2*(clampedLatticeRemainder (2*(1+sourceFactorialCollar (n+1))*u)-
          clampedLatticeRemainder (2*u))|+
        |4*(clampedLatticeRemainder ((1+sourceFactorialCollar (n+1))*u)-
          clampedLatticeRemainder u)| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ 25/32 := by
      simp only [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

private theorem tail_remainder_lipschitz (n : ℕ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |factorialMuntzTailRemainder n u-factorialMuntzTailRemainder n v| ≤
      14*|u-v| := by
  let e := sourceFactorialCollar (n+1)
  have he : 0 ≤ e := (sourceFactorialCollar_pos (N := n+1) (by omega)).le
  have he1 : e ≤ 1 := collar_le_one n
  have scaled (a : ℝ) (ha : 0 ≤ a) :
      |clampedLatticeRemainder (a*u)-clampedLatticeRemainder (a*v)| ≤ a*|u-v|/2 := by
    have h := remainder_lipschitz (mul_nonneg ha hu) (mul_nonneg ha hv)
    simpa only [← mul_sub, abs_mul, abs_of_nonneg ha] using h
  let D := fun (a x : ℝ) => clampedLatticeRemainder (a*(1+e)*x)-clampedLatticeRemainder (a*x)
  have hD (a : ℝ) (ha : 0 ≤ a) : |D a u-D a v| ≤ a*(2+e)*|u-v|/2 := by
    have h1 := scaled (a*(1+e)) (by positivity)
    have h2 := scaled a ha
    have hid : D a u-D a v =
        (clampedLatticeRemainder (a*(1+e)*u)-clampedLatticeRemainder (a*(1+e)*v))-
        (clampedLatticeRemainder (a*u)-clampedLatticeRemainder (a*v)) := by
      dsimp only [D]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by nlinarith only [h1,h2])
  have h4 := hD 4 (by norm_num)
  have h2 := hD 2 (by norm_num)
  have h1 := hD 1 (by norm_num)
  have hid : factorialMuntzTailRemainder n u-factorialMuntzTailRemainder n v =
      (D 4 u-D 4 v)/4-2*(D 2 u-D 2 v)+4*(D 1 u-D 1 v) := by
    dsimp only [D,e,factorialMuntzTailRemainder]
    simp only [one_mul]
    ring
  rw [hid]
  calc
    _ ≤ |(D 4 u-D 4 v)/4-2*(D 2 u-D 2 v)|+|4*(D 1 u-D 1 v)| := abs_add_le _ _
    _ ≤ |(D 4 u-D 4 v)/4|+|2*(D 2 u-D 2 v)|+|4*(D 1 u-D 1 v)| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ 14*|u-v| := by
      simp only [abs_div,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg (u-v),
        mul_nonneg (sub_nonneg.mpr he1) (abs_nonneg (u-v))]

/-- The literal periodic remainder read along the exponential arithmetic clock. -/
def factorialTailPhase (n : ℕ) (x : ℝ) : ℝ :=
  factorialMuntzTailRemainder n (((n+1 : ℕ) : ℝ)*Real.exp (-x))

/-- Bounded phase amplitude is independent of the arithmetic scale. -/
theorem factorialTailPhase_abs_le (n : ℕ) (x : ℝ) :
    |factorialTailPhase n x| ≤ 25/32 :=
  tail_remainder_abs_le n (by positivity)

/-- The phase increment costs only the displacement of its arithmetic clock. -/
theorem factorialTailPhase_sub_le (n : ℕ) (x y : ℝ) :
    |factorialTailPhase n x-factorialTailPhase n y| ≤
      14*((n+1 : ℕ) : ℝ)*|Real.exp (-x)-Real.exp (-y)| := by
  have h := tail_remainder_lipschitz n
    (u := ((n+1 : ℕ) : ℝ)*Real.exp (-x))
    (v := ((n+1 : ℕ) : ℝ)*Real.exp (-y)) (by positivity) (by positivity)
  simpa only [factorialTailPhase, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ)), mul_assoc] using h

/-- Combining boundedness and Lipschitz control avoids a derivative at integer joins. -/
theorem factorialTailPhase_sub_sq_le (n : ℕ) (x y : ℝ) :
    (factorialTailPhase n x-factorialTailPhase n y)^2 ≤
      28*((n+1 : ℕ) : ℝ)*|Real.exp (-x)-Real.exp (-y)| := by
  have hsmall := factorialTailPhase_sub_le n x y
  have hbig : |factorialTailPhase n x-factorialTailPhase n y| ≤ 2 := by
    have h := abs_sub (factorialTailPhase n x) (factorialTailPhase n y)
    linarith [factorialTailPhase_abs_le n x, factorialTailPhase_abs_le n y]
  have h := mul_le_mul hbig hsmall (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [sq_abs (factorialTailPhase n x-factorialTailPhase n y)]

/-- The arithmetic collar normalization of the correction tail. -/
def factorialTailAmplitude (n : ℕ) : ℝ :=
  1/(((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)*Real.sqrt ((n+1 : ℕ) : ℝ))

theorem factorialTailAmplitude_pos (n : ℕ) : 0 < factorialTailAmplitude n := by
  have he := sourceFactorialCollar_pos (N := n+1) (by omega)
  unfold factorialTailAmplitude
  positivity

/-- The shrinking collar introduces no additional power beyond the square-root normalization. -/
theorem factorialTailAmplitude_le (n : ℕ) :
    factorialTailAmplitude n ≤ 15/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have he := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hlo := (sourceFactorialWidth_bounds (N := n+1) (by omega)).1.trans
    (sourceFactorialWidth_le_collar (n+1))
  have hc := (div_le_iff₀ (by positivity : (0 : ℝ) < 15*((n+1 : ℕ) : ℝ))).mp hlo
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  unfold factorialTailAmplitude
  apply (div_le_div_iff₀ (by positivity) hs).2
  nlinarith [mul_le_mul_of_nonneg_right hc hs.le]

/-- Exact phase representation, including the endpoint jump of the zero extension. -/
theorem factorialMuntzCorrectedTail_eq_phase (n : ℕ) (x : ℝ) :
    factorialMuntzCorrectedTail n x =
      (Iic (0 : ℝ)).indicator
        (fun y => factorialTailAmplitude n*Real.exp (3*y/2)*factorialTailPhase n y) x := by
  by_cases hx : x ≤ 0
  · have he := sourceFactorialCollar_pos (N := n+1) (by omega)
    have hs := factorialMuntzSum_add_half_eq_remainder n (Real.exp_pos x)
    rw [show ((n+1 : ℕ) : ℝ)/Real.exp x =
      ((n+1 : ℕ) : ℝ)*Real.exp (-x) by rw [Real.exp_neg,div_eq_mul_inv]] at hs
    simp only [factorialMuntzCorrectedTail,factorialMuntzBoundaryCorrected,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),factorialMuntzCompletion,
      factorialMuntzBoundaryCoefficient,factorialTailAmplitude,factorialTailPhase]
    have hexp : Real.exp (x/2)*Real.exp x = Real.exp (3*x/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    calc
      _ = Real.exp (x/2)*(factorialMuntzSum n (Real.exp x)+1/2)/
          Real.sqrt ((n+1 : ℕ) : ℝ) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = _ := by
        rw [hs]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
  · simp only [factorialMuntzCorrectedTail,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)]

end
end GaloisForLFunctions.ArithmeticPositivityTheory
