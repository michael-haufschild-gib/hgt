import GaloisForLFunctions.HeightHomotopyArithmeticCounts.SpacingKernelMajorant
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedGcdForm

/-!
# Uniform conductor-weighted spacing convergence

Every positive conductor weight controls the full scalar-renormalized spacing
error, uniformly over finite supports. The exact divisor remainder has a power
modulus; the positive gcd-square identity absorbs its divisor growth.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- Absolute mixed errors have a power modulus on every positively weighted unit ball. -/
theorem spacingKernelError_weighted_absolute_rate (δ α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hgap : 2*α < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ),
      0 < ε → (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingKernelError ε m n|) ≤ 
        C*ε^α*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  let κ := (δ-2*α)/8
  let β := (δ-2*α)/2
  let s := α+2*κ
  have hκ : 0 < κ := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hβ : 0 < β := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hexp : β+(s+s) ≤ δ := by
    apply le_of_eq
    dsimp only [β, s, κ]
    ring
  obtain ⟨A, hA, hentry⟩ := spacingKernelError_conductor_bound α κ hα hα1 hκ
  obtain ⟨D, hD, hgcd⟩ := normalized_gcd_form_finite_bound β hβ
  refine ⟨A*D, mul_pos hA hD, ?_⟩
  intro ε S x hε hS
  let y : ℕ → ℝ := fun n => |x n| *(n:ℝ)^s
  have hεpow : 0 ≤ ε^α := Real.rpow_nonneg hε.le _
  have hpoint (m : ℕ) (hm : m∈S) (n : ℕ) (hn : n∈S) :
      |x m*x n*spacingKernelError ε m n| ≤ 
        (A*ε^α)*((Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) := by
    have hm0 : (0:ℝ) < m := by exact_mod_cast hS m hm
    have hn0 : (0:ℝ) < n := by exact_mod_cast hS n hn
    rw [abs_mul, abs_mul]
    calc |x m| *|x n| *|spacingKernelError ε m n| ≤ 
          |x m| *|x n| *(A*ε^α*(Nat.gcd m n:ℝ)*((m:ℝ)*n)^s/Real.sqrt ((m:ℝ)*n)) :=
          mul_le_mul_of_nonneg_left (hentry ε m n hε (hS m hm) (hS n hn))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
         _ = _ := by
          rw [Real.mul_rpow hm0.le hn0.le, Real.sqrt_mul hm0.le]
          dsimp only [y]
          ring
  have hnorm : (∑ n ∈ S, (n:ℝ)^β*(y n)^2) ≤ 
      ∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    apply sum_le_sum
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hS n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hS n hn
    calc (n:ℝ)^β*(y n)^2 =
          ((n:ℝ)^β*((n:ℝ)^s*(n:ℝ)^s))*(x n)^2 := by
          dsimp only [y]
          rw [mul_pow, sq_abs]
          ring
         _ = (n:ℝ)^(β+(s+s))*(x n)^2 := by rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
         _ ≤ (n:ℝ)^δ*(x n)^2 := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hn1 hexp) (sq_nonneg _)
  calc (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingKernelError ε m n|) ≤ 
        ∑ m ∈ S, ∑ n ∈ S,
        (A*ε^α)*((Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n))) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hpoint m hm n hn
       _ = (A*ε^α)*∑ m ∈ S, ∑ n ∈ S,
          (Nat.gcd m n:ℝ)*(y m/Real.sqrt m*(y n/Real.sqrt n)) := by
        simp only [mul_sum]
       _ ≤ (A*ε^α)*(D*∑ n ∈ S, (n:ℝ)^β*(y n)^2) :=
        mul_le_mul_of_nonneg_left (hgcd S y hS) (mul_nonneg hA.le hεpow)
       _ ≤ (A*ε^α)*(D*∑ n ∈ S, (n:ℝ)^δ*(x n)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm hD.le)
          (mul_nonneg hA.le hεpow)
       _ = _ := by ring

/-- An explicit positive power works for every positive conductor weight. -/
theorem spacingKernelError_weighted_absolute_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ),
      0 < ε → (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingKernelError ε m n|) ≤ 
        C*ε^(min (δ/8) 1)*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  apply spacingKernelError_weighted_absolute_rate δ (min (δ/8) 1)
    (lt_min (by positivity) zero_lt_one) (min_le_right _ _)
  have hmin := min_le_left (δ/8) (1:ℝ)
  linarith only [hmin, hδ]

/-- Every rate `0 < α ≤ 1` with `2α < δ` controls the actual spacing-form error. -/
theorem spacingForm_weighted_error_rate (δ α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hgap : 2*α < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ),
      0 < ε → (∀ n ∈ S, 0 < n) →
      |spacingForm ε S x+Real.log (2*ε)*(∑ n ∈ S, (x n)^2)-spacingLimit S x| ≤ 
        C*ε^α*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  obtain ⟨C, hC, hbound⟩ := spacingKernelError_weighted_absolute_rate δ α hα hα1 hgap
  refine ⟨C, hC, ?_⟩
  intro ε S x hε hS
  rw [spacingForm_error_eq]
  exact ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)).trans (hbound ε S x hε hS)

/-- The actual spacing form converges uniformly on every positively weighted unit ball. -/
theorem spacingForm_weighted_error_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (S : Finset ℕ) (x : ℕ → ℝ),
      0 < ε → (∀ n ∈ S, 0 < n) →
      |spacingForm ε S x+Real.log (2*ε)*(∑ n ∈ S, (x n)^2)-spacingLimit S x| ≤ 
        C*ε^(min (δ/8) 1)*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  obtain ⟨C, hC, hbound⟩ := spacingKernelError_weighted_absolute_bound δ hδ
  refine ⟨C, hC, ?_⟩
  intro ε S x hε hS
  rw [spacingForm_error_eq]
  exact ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun m _ => abs_sum_le_sum_abs _ _)).trans (hbound ε S x hε hS)

#print axioms spacingKernelError_weighted_absolute_rate
#print axioms spacingForm_weighted_error_rate
#print axioms spacingKernelError_weighted_absolute_bound
#print axioms spacingForm_weighted_error_bound
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
