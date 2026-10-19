import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseBohrCoercivityAndTailIndependence

/-! Bounded primitives of finite exact factorial phase combinations. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

def criticalFactorialPhasePrimitive (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ n ∈ S, b n * (factorialMuntzTailLatticePrimitive n (((n+1 : ℕ) : ℝ)*v) /
    ((n+1 : ℕ) : ℝ))

theorem criticalFactorialPhasePrimitive_bound (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |criticalFactorialPhasePrimitive S b v| ≤ 12 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ) := by
  dsimp [criticalFactorialPhasePrimitive]
  calc
    _ ≤ ∑ n ∈ S, |b n * (factorialMuntzTailLatticePrimitive n (((n+1 : ℕ) : ℝ)*v) /
        ((n+1 : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, |b n| * (12 / ((n+1 : ℕ) : ℝ)) := Finset.sum_le_sum fun n _ => by
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (factorialMuntzTailLatticePrimitive_abs_le _ _) (by positivity)) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

theorem criticalFactorialPhasePrimitive_hasDerivAt (S : Finset ℕ) (b : ℕ → ℝ)
    {v : ℝ} (hv : 0 < v) :
    HasDerivAt (criticalFactorialPhasePrimitive S b)
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re v := by
  have hsum : (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re =
      ∑ n ∈ S, b n * factorialPhaseProfile (n+1) v := by
    simp [factorialPhaseCombination]
  rw [hsum]
  apply HasDerivAt.fun_sum
  intro n _
  have hd := ((factorialMuntzTailLatticePrimitive_hasDerivAt n
    (y := ((n+1 : ℕ) : ℝ)*v) (by positivity)).comp v
      ((hasDerivAt_id v).const_mul ((n+1 : ℕ) : ℝ))).div_const ((n+1 : ℕ) : ℝ)
  have hd' : HasDerivAt
      (fun u => factorialMuntzTailLatticePrimitive n (((n+1 : ℕ) : ℝ)*u) /
        ((n+1 : ℕ) : ℝ)) (factorialPhaseProfile (n+1) v) v := by
    convert hd using 1 <;> try rfl
    rw [factorialPhaseProfile_eq_tailRemainder n hv.le]
    field_simp
  exact hd'.const_mul (b n)

end GaloisForLFunctions.ArithmeticPositivityTheory
