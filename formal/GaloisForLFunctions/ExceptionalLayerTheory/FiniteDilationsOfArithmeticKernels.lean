import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHarmonicConvolution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite dilations of arithmetic kernels

A Dirichlet convolution composes the finite dilation operators at a real
cutoff. Abel summation expresses such an operator in terms of successive
kernel differences and the ordinary cumulative count.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Sum a test function over all positive integral dilates below a real cutoff. -/
def arithmeticKernel (a : ArithmeticFunction ℝ) (w : ℝ → E) (x : ℝ) : E :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n • w (x/n)

/-- A test vanishing at one uses one finite sum on the whole closed unit cell. -/
theorem arithmeticKernel_on_unit_interval (a : ArithmeticFunction ℝ) (w : ℝ → E) (hw : w 1 = 0)
    {n : ℕ} {x : ℝ} (hl : (n:ℝ) ≤ x) (hr : x ≤ (n:ℝ)+1) :
    arithmeticKernel a w x = ∑ d ∈ Icc 1 n, a d • w (x/d) := by
  rcases hr.lt_or_eq with h | rfl
  · rw [arithmeticKernel,(Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hl)).mpr ⟨hl,h⟩]
  · have hfloor : ⌊(n:ℝ)+1⌋₊ = n+1 := by rw [← Nat.cast_one,← Nat.cast_add,Nat.floor_natCast]
    rw [arithmeticKernel,hfloor,sum_Icc_succ_top (show 1 ≤ n+1 by omega)]
    simp only [Nat.cast_add,Nat.cast_one,div_self (by positivity : (n:ℝ)+1 ≠ 0),hw,smul_zero,add_zero]

/-- Composition is Dirichlet convolution, including nonintegral cutoffs. -/
theorem arithmeticKernel_mul (a b : ArithmeticFunction ℝ) (w : ℝ → E) (x : ℝ) :
    arithmeticKernel (a*b) w x = arithmeticKernel a (arithmeticKernel b w) x := by
  let G := fun p : ℕ × ℕ => (a p.1 * b p.2) • w (x/((p.1:ℝ)*p.2))
  have he (n : ℕ) : (a*b) n • w (x/n) = ∑ p ∈ n.divisorsAntidiagonal, G p := by
    rw [ArithmeticFunction.mul_apply,Finset.sum_smul]
    refine sum_congr rfl fun p hp => ?_
    have hm := (Nat.mem_divisorsAntidiagonal.mp hp).1
    dsimp only [G]
    rw [← Nat.cast_mul,hm]
  unfold arithmeticKernel
  simp_rw [he]
  rw [_root_.RHTower.WeilSingularArithmetic.sum_divisors_hyperbola]
  refine sum_congr rfl fun d _ => ?_
  rw [Nat.floor_div_natCast,Finset.smul_sum]
  exact sum_congr rfl fun m _ => by simp only [G,smul_smul,div_div]

/-- Discrete Abel summation for a scalar count acting on a vector-valued weight. -/
theorem sum_smul_eq_prefix_differences (a : ℕ → ℝ) (w : ℕ → E) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n • w n =
      (∑ j ∈ Icc 1 N, a j) • w (N+1) +
      ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 n, a j) • (w n - w (n+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [sum_Icc_succ_top (show 1 ≤ N+1 by omega),ih,smul_sub,add_smul]
    abel

/-- A kernel vanishing at one and below the first divisor has no terminal term. -/
theorem arithmeticKernel_eq_prefix_differences (a : ArithmeticFunction ℝ) (w : ℝ → E)
    (hw : ∀ y, y ≤ 1 → w y = 0) (N : ℕ) :
    arithmeticKernel a w N =
      ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 n, a j) • (w ((N:ℝ)/n)-w ((N:ℝ)/(n+1))) := by
  rw [arithmeticKernel,Nat.floor_natCast,sum_smul_eq_prefix_differences]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [hw _ (by rw [div_le_one (by positivity)]; linarith), smul_zero,zero_add]

/-- A transitive estimate on adjacent unit cells extends to every real interval above one. -/
theorem of_adjacent_unit_intervals {P : ℝ → ℝ → Prop}
    (hcell : ∀ n : ℕ, 1 ≤ n → ∀ x y : ℝ, n ≤ x → x ≤ y → y ≤ (n:ℝ)+1 → P x y)
    (hjoin : ∀ x y z : ℝ, P x y → P y z → P x z) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    P x y := by
  let N := ⌊x⌋₊
  let M := ⌊y⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hxN : x ≤ (N:ℝ)+1 := (Nat.lt_floor_add_one x).le
  have hMy : (M:ℝ) ≤ y := Nat.floor_le (zero_le_one.trans (hx.trans hxy))
  have hyM : y ≤ (M:ℝ)+1 := (Nat.lt_floor_add_one y).le
  rcases le_or_gt M N with hMN | hMN
  · exact hcell N hN x y hNx hxy (hyM.trans (by exact_mod_cast Nat.add_le_add_right hMN 1))
  have hbridge (j : ℕ) (hj : N+1 ≤ j) : P x j := by
    induction j, hj using Nat.le_induction with
    | base =>
      apply hcell N hN x _ hNx
      · simpa only [Nat.cast_add,Nat.cast_one] using hxN
      · simp
    | succ j hj ih =>
      apply hjoin x j _ ih
      apply hcell j (by omega) _ _ le_rfl <;> simp
  exact hjoin x M y (hbridge M hMN) (hcell M (by omega) _ _ le_rfl hMy hyM)

#print axioms arithmeticKernel_mul
#print axioms arithmeticKernel_eq_prefix_differences

end GaloisForLFunctions.ExceptionalLayerTheory
