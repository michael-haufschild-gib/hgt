import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Navier--Stokes analytic convolution estimate

Finite reciprocal-square convolution bound underlying equation (B.7) and the Banach-algebra
estimate in Lemma B.1 of the Navier--Stokes paper.  Pairing each index with its reverse gives a
constant `4`, improving the paper's sufficient constant `8`.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesAnalyticConvolution

open Finset
open Finset.Nat
open scoped BigOperators

/-- Reciprocal-square coefficient weight used in the analytic profile norm. -/
noncomputable def reciprocalSquareWeight {n : ℕ} (i : Fin n) : ℝ :=
  1 / (((i : ℕ) : ℝ) + 1) ^ 2

private theorem square_div_product_le_two {x a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx0 : 0 ≤ x) (hx : x ≤ a + b) :
    x ^ 2 / (a ^ 2 * b ^ 2) ≤ 2 / a ^ 2 + 2 / b ^ 2 := by
  have hab : 0 < a ^ 2 * b ^ 2 := mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  rw [div_le_iff₀ hab]
  field_simp [ha.ne', hb.ne']
  nlinarith [sq_nonneg (a - b)]

/-- Each convolution summand is controlled by its two endpoint reciprocal-square weights. -/
theorem reciprocalSquareConvolutionTerm_le (N : ℕ) (i : Fin (N + 1)) :
    ((N + 1 : ℕ) : ℝ) ^ 2 * reciprocalSquareWeight i * reciprocalSquareWeight i.rev ≤
      2 * reciprocalSquareWeight i + 2 * reciprocalSquareWeight i.rev := by
  have hsum : ((N + 1 : ℕ) : ℝ) ≤
      (((i : ℕ) : ℝ) + 1) + (((i.rev : ℕ) : ℝ) + 1) := by
    have hnat := i.add_rev_cast
    have hcast : ((i : ℕ) : ℝ) + ((i.rev : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast hnat
    calc
      ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_num
      _ ≤ (N : ℝ) + 2 := by norm_num
      _ = (((i : ℕ) : ℝ) + 1) + (((i.rev : ℕ) : ℝ) + 1) := by
        rw [← hcast]
        ring
  have hcore := square_div_product_le_two
    (show 0 < ((i : ℕ) : ℝ) + 1 by positivity)
    (show 0 < ((i.rev : ℕ) : ℝ) + 1 by positivity)
    (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity) hsum
  simpa [reciprocalSquareWeight, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcore

/-- Reversing a finite coefficient list preserves its reciprocal-square mass. -/
theorem sum_reciprocalSquareWeight_rev (N : ℕ) :
    ∑ i : Fin (N + 1), reciprocalSquareWeight i.rev =
      ∑ i : Fin (N + 1), reciprocalSquareWeight i := by
  exact Equiv.sum_comp Fin.revPerm reciprocalSquareWeight

/--
Reciprocal-square convolution bound.  This proves equation (B.7) with `4` in place of `8`.
-/
theorem reciprocalSquareConvolution_le_four (N : ℕ) :
    ∑ i : Fin (N + 1),
        ((N + 1 : ℕ) : ℝ) ^ 2 * reciprocalSquareWeight i * reciprocalSquareWeight i.rev ≤
      4 * ∑ i : Fin (N + 1), reciprocalSquareWeight i := by
  calc
    _ ≤ ∑ i : Fin (N + 1),
        (2 * reciprocalSquareWeight i + 2 * reciprocalSquareWeight i.rev) :=
      Finset.sum_le_sum fun i _ => reciprocalSquareConvolutionTerm_le N i
    _ = 2 * (∑ i : Fin (N + 1), reciprocalSquareWeight i) +
        2 * (∑ i : Fin (N + 1), reciprocalSquareWeight i.rev) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [sum_reciprocalSquareWeight_rev]; ring

/-- The paper's stated constant `8` follows immediately from the sharper finite bound. -/
theorem reciprocalSquareConvolution_le_eight (N : ℕ) :
    ∑ i : Fin (N + 1),
        ((N + 1 : ℕ) : ℝ) ^ 2 * reciprocalSquareWeight i * reciprocalSquareWeight i.rev ≤
      8 * ∑ i : Fin (N + 1), reciprocalSquareWeight i := by
  refine (reciprocalSquareConvolution_le_four N).trans ?_
  have hsum : 0 ≤ ∑ i : Fin (N + 1), reciprocalSquareWeight i :=
    Finset.sum_nonneg fun _ _ => by simp [reciprocalSquareWeight]; positivity
  nlinarith

/-- The binomial ratio estimate (B.8).  Selecting `k` objects from a first block and `β-k`
from a second block is one summand in Vandermonde's count of all `β`-subsets. -/
theorem splitBlockChooseProduct_le (i k α β : ℕ) (hi : i ≤ α) (hk : k ≤ β) :
    (i + k).choose k * ((α - i) + (β - k)).choose (β - k) ≤
      (α + β).choose β := by
  have hmem : (k, β - k) ∈ antidiagonal β := by
    simp [hk]
  have hterm :
      (i + k).choose k * ((α - i) + (β - k)).choose (β - k) ≤
        ∑ ij ∈ antidiagonal β,
          (i + k).choose ij.1 * ((α - i) + (β - k)).choose ij.2 := by
    exact Finset.single_le_sum (s := antidiagonal β)
      (f := fun ij => (i + k).choose ij.1 *
        ((α - i) + (β - k)).choose ij.2)
      (fun ij _ => Nat.zero_le _) hmem
  calc
    _ ≤ ∑ ij ∈ antidiagonal β,
          (i + k).choose ij.1 * ((α - i) + (β - k)).choose ij.2 := hterm
    _ = ((i + k) + ((α - i) + (β - k))).choose β :=
      (Nat.add_choose_eq _ _ _).symm
    _ = (α + β).choose β := by
      congr 1
      omega

/-- The radial integration weight ratio in equation (B.9) has the paper's uniform bound `80`. -/
theorem radialIntegrationWeightRatio_le (α β : ℕ) :
    20 * (((α : ℝ) + 2) ^ 2 / ((α : ℝ) + 1) ^ 2) *
        (((α : ℝ) + 1) / ((α : ℝ) + (β : ℝ) + 1)) ≤ 80 := by
  have hα : 0 ≤ (α : ℝ) := Nat.cast_nonneg α
  have hβ : 0 ≤ (β : ℝ) := Nat.cast_nonneg β
  have hfirst : (((α : ℝ) + 2) ^ 2 / ((α : ℝ) + 1) ^ 2) ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (α : ℝ) + 1))]
    nlinarith
  have hsecond : ((α : ℝ) + 1) / ((α : ℝ) + (β : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < (α : ℝ) + (β : ℝ) + 1)]
    linarith
  calc
    _ ≤ (20 : ℝ) * 4 * 1 := by gcongr
    _ = 80 := by norm_num

/-- The mixed parameter/radial weight ratio in equation (B.10) has bound `80(i+1)/ρ`. -/
theorem mixedIntegrationWeightRatio_le (i k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (20 / ρ) * ((i : ℝ) + 1) *
        (((i : ℝ) + 2) ^ 2 / ((i : ℝ) + 1) ^ 2) *
        (((k : ℝ) + 1) ^ 2 / ((k : ℝ) + 2) ^ 2) ≤
      (80 / ρ) * ((i : ℝ) + 1) := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hfirst : (((i : ℝ) + 2) ^ 2 / ((i : ℝ) + 1) ^ 2) ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (i : ℝ) + 1))]
    nlinarith
  have hsecond : (((k : ℝ) + 1) ^ 2 / ((k : ℝ) + 2) ^ 2) ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos (by positivity : 0 < (k : ℝ) + 2))]
    nlinarith
  have hscale : 0 ≤ 20 / ρ := by positivity
  calc
    _ ≤ (20 / ρ) * ((i : ℝ) + 1) * 4 * 1 := by gcongr
    _ = (80 / ρ) * ((i : ℝ) + 1) := by field_simp; ring

end GaloisForLFunctions.HTGeometry.NavierStokesAnalyticConvolution
