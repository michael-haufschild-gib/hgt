import GaloisForLFunctions.BiScaleUncertainty.ClampedLatticePrimitive
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailSmoothing

/-! Exact bounded-primitive representation of the actual corrected tail. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialMuntzTailRemainder (n : ℕ) (y : ℝ) : ℝ :=
  (clampedLatticeRemainder (4*(1+sourceFactorialCollar (n+1))*y)-
    clampedLatticeRemainder (4*y))/4-
  2*(clampedLatticeRemainder (2*(1+sourceFactorialCollar (n+1))*y)-
    clampedLatticeRemainder (2*y))+
  4*(clampedLatticeRemainder ((1+sourceFactorialCollar (n+1))*y)-
    clampedLatticeRemainder y)

def factorialMuntzTailLatticePrimitive (n : ℕ) (y : ℝ) : ℝ :=
  clampedLatticePrimitive (sourceFactorialCollar (n+1)) 4 y/4-
    2*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 2 y+
    4*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 1 y

theorem factorialMuntzTailLatticePrimitive_abs_le (n : ℕ) (y : ℝ) :
    |factorialMuntzTailLatticePrimitive n y| ≤ 12 := by
  have hε := (sourceFactorialCollar_pos (N := n+1) (by omega)).le
  have h1 := clampedLatticePrimitive_abs_le hε (a := 1) (by norm_num) y
  have h2 := clampedLatticePrimitive_abs_le hε (a := 2) (by norm_num) y
  have h4 := clampedLatticePrimitive_abs_le hε (a := 4) (by norm_num) y
  unfold factorialMuntzTailLatticePrimitive
  calc
    _ ≤ |clampedLatticePrimitive (sourceFactorialCollar (n+1)) 4 y/4-
        2*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 2 y|+
        |4*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 1 y| := abs_add_le _ _
    _ ≤ |clampedLatticePrimitive (sourceFactorialCollar (n+1)) 4 y/4|+
        |2*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 2 y|+
        |4*clampedLatticePrimitive (sourceFactorialCollar (n+1)) 1 y| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ 12 := by
      simp only [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num),
        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      norm_num at h1 h2 h4
      linarith

theorem factorialMuntzTailLatticePrimitive_hasDerivAt (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (factorialMuntzTailLatticePrimitive n) (factorialMuntzTailRemainder n y) y := by
  have hε := (sourceFactorialCollar_pos (N := n+1) (by omega)).le
  have h1 := clampedLatticePrimitive_hasDerivAt hε (a := 1) (by norm_num) hy
  have h2 := clampedLatticePrimitive_hasDerivAt hε (a := 2) (by norm_num) hy
  have h4 := clampedLatticePrimitive_hasDerivAt hε (a := 4) (by norm_num) hy
  simpa only [factorialMuntzTailLatticePrimitive, factorialMuntzTailRemainder, one_mul]
    using! ((h4.div_const 4).sub (h2.const_mul 2)).add (h1.const_mul 4)

theorem factorialMuntzSum_add_half_eq_remainder (n : ℕ) {t : ℝ} (ht : 0 < t) :
    factorialMuntzSum n t+1/2 =
      t/(((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1))*
        factorialMuntzTailRemainder n (((n+1 : ℕ) : ℝ)/t) := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let ε := sourceFactorialCollar (n+1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := sourceFactorialCollar_pos (by omega)
  rw [factorialMuntzSum_eq_clampedLattice n ht,
    clampedLatticeSum_eq hε (by positivity) ht,
    clampedLatticeSum_eq hε (by positivity) ht,
    clampedLatticeSum_eq hε hN ht]
  have hscale (a : ℝ) : a*N*(1+ε)/t = a*(1+ε)*(N/t) := by ring
  have hbase (a : ℝ) : a*N/t = a*(N/t) := by ring
  change (4*N*(1+ε/2)/t-1/2+t/(4*N*ε)*
      (clampedLatticeRemainder (4*N*(1+ε)/t)-clampedLatticeRemainder (4*N/t)))-
    4*(2*N*(1+ε/2)/t-1/2+t/(2*N*ε)*
      (clampedLatticeRemainder (2*N*(1+ε)/t)-clampedLatticeRemainder (2*N/t)))+
    4*(N*(1+ε/2)/t-1/2+t/(N*ε)*
      (clampedLatticeRemainder (N*(1+ε)/t)-clampedLatticeRemainder (N/t)))+1/2 = _
  rw [hscale 4, hscale 2, hbase 4, hbase 2,
    show N*(1+ε)/t = (1+ε)*(N/t) by ring]
  dsimp only [factorialMuntzTailRemainder]
  change _ = t/(N*ε)*((clampedLatticeRemainder (4*(1+ε)*(N/t))-
    clampedLatticeRemainder (4*(N/t)))/4-
    2*(clampedLatticeRemainder (2*(1+ε)*(N/t))-clampedLatticeRemainder (2*(N/t)))+
    4*(clampedLatticeRemainder ((1+ε)*(N/t))-clampedLatticeRemainder (N/t)))
  field_simp
  ring

def factorialMuntzTailPrimitive (n : ℕ) (x : ℝ) : ℝ :=
  factorialMuntzTailLatticePrimitive n (((n+1 : ℕ) : ℝ)*Real.exp (-x))

def factorialMuntzTailPrimitiveScale (n : ℕ) : ℝ :=
  1/(((n+1 : ℕ) : ℝ)^2*sourceFactorialCollar (n+1)*Real.sqrt ((n+1 : ℕ) : ℝ))

theorem factorialMuntzTailPrimitive_abs_le (n : ℕ) (x : ℝ) :
    |factorialMuntzTailPrimitive n x| ≤ 12 :=
  factorialMuntzTailLatticePrimitive_abs_le n _

theorem factorialMuntzTailPrimitive_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (factorialMuntzTailPrimitive n)
      (-((n+1 : ℕ) : ℝ)*Real.exp (-x)*
        factorialMuntzTailRemainder n (((n+1 : ℕ) : ℝ)*Real.exp (-x))) x := by
  have h := (factorialMuntzTailLatticePrimitive_hasDerivAt n (y :=
    ((n+1 : ℕ) : ℝ)*Real.exp (-x)) (by positivity)).comp x
    ((((hasDerivAt_id x).neg).exp).const_mul ((n+1 : ℕ) : ℝ))
  convert h using 1 <;> try rfl
  simp only [Pi.neg_apply, id_eq]
  ring

theorem factorialMuntzTailPrimitive_continuous (n : ℕ) :
    Continuous (factorialMuntzTailPrimitive n) :=
  continuous_iff_continuousAt.mpr fun x =>
    (factorialMuntzTailPrimitive_hasDerivAt n x).continuousAt

theorem factorialMuntzTailPrimitiveScale_pos (n : ℕ) :
    0 < factorialMuntzTailPrimitiveScale n := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  unfold factorialMuntzTailPrimitiveScale
  positivity

theorem factorialMuntzTailPrimitiveScale_le (n : ℕ) :
    factorialMuntzTailPrimitiveScale n ≤ 15/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hlo := (sourceFactorialWidth_bounds (N := n+1) (by omega)).1.trans
    (sourceFactorialWidth_le_collar (n+1))
  have hscaled : (1 : ℝ) ≤ 15*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1) := by
    exact (div_le_iff₀ (by positivity)).mp hlo |>.trans_eq (by ring)
  unfold factorialMuntzTailPrimitiveScale
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right hscaled
    (show 0 ≤ ((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ) by positivity)]

/-- Exact derivative representation on the actual tail half-line. -/
theorem factorialMuntzCorrectedTail_eq_primitive_deriv (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    factorialMuntzCorrectedTail n x = -factorialMuntzTailPrimitiveScale n*
      Real.exp (5*x/2)*deriv (factorialMuntzTailPrimitive n) x := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hsum := factorialMuntzSum_add_half_eq_remainder n (Real.exp_pos x)
  rw [show ((n+1 : ℕ) : ℝ)/Real.exp x =
    ((n+1 : ℕ) : ℝ)*Real.exp (-x) by rw [Real.exp_neg, div_eq_mul_inv]] at hsum
  rw [(factorialMuntzTailPrimitive_hasDerivAt n x).deriv]
  simp only [factorialMuntzCorrectedTail, factorialMuntzBoundaryCorrected,
    indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), factorialMuntzCompletion,
    factorialMuntzBoundaryCoefficient, factorialMuntzTailPrimitiveScale]
  have hexp : Real.exp (5*x/2)*Real.exp (-x) = Real.exp (x/2)*Real.exp x := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (x/2)*factorialMuntzSum n (Real.exp x)/Real.sqrt ((n+1 : ℕ) : ℝ)+
      1/(2*Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp (x/2) =
      Real.exp (x/2)/Real.sqrt ((n+1 : ℕ) : ℝ)*(factorialMuntzSum n (Real.exp x)+1/2) by ring,
    hsum]
  rw [show -(1/(((n+1 : ℕ) : ℝ)^2*sourceFactorialCollar (n+1)*
      Real.sqrt ((n+1 : ℕ) : ℝ)))*Real.exp (5*x/2)*
      (-((n+1 : ℕ) : ℝ)*Real.exp (-x)*
        factorialMuntzTailRemainder n (((n+1 : ℕ) : ℝ)*Real.exp (-x))) =
      (Real.exp (5*x/2)*Real.exp (-x))*
        factorialMuntzTailRemainder n (((n+1 : ℕ) : ℝ)*Real.exp (-x))/
        (((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)*Real.sqrt ((n+1 : ℕ) : ℝ)) by
    field_simp, hexp]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
