import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact Boolean parity Gram sectors

The product kernel with local matrices `[[1,r_i],[r_i,1]]` has constant and
parity eigenvectors. Their two nonnegative parity indicators have equal squared
mass, and their cross mass retains the difference of the two product eigenvalues.
All identities follow from the existing finite product-sum API and hold for
arbitrary real local parameters.

This algebraic support for the dyadic-antichain prime-bank construction does not
yet identify the cube with literal squarefree odd-divisor coefficients.
-/

open scoped BigOperators
open Finset


namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false
variable {I : Type*} [Fintype I] [DecidableEq I]

def fermiBooleanGram (r : I → ℝ) (x y : I → Bool) : ℝ :=
  ∏ i, if x i = y i then 1 else r i

def fermiBooleanParity (x : I → Bool) : ℝ :=
  ∏ i, if x i then -1 else 1

theorem fermiBooleanGram_row_sum (r : I → ℝ) (x : I → Bool) :
    (∑ y : I → Bool, fermiBooleanGram r x y) = ∏ i, (1+r i) := by
  unfold fermiBooleanGram
  rw [← Fintype.prod_sum (fun i b => if x i = b then (1 : ℝ) else r i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases x i <;> simp [add_comm]

theorem fermiBooleanGram_parity_eigen (r : I → ℝ) (x : I → Bool) :
    (∑ y : I → Bool, fermiBooleanGram r x y*fermiBooleanParity y) =
      (∏ i, (1-r i))*fermiBooleanParity x := by
  unfold fermiBooleanGram fermiBooleanParity
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if x i = b then (1 : ℝ) else r i)*(if b then -1 else 1))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases x i <;> simp <;> ring

omit [DecidableEq I] in
theorem fermiBooleanParity_square (x : I → Bool) : (fermiBooleanParity x)^2 = 1 := by
  unfold fermiBooleanParity
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> norm_num

theorem fermiBooleanParity_sum [Nonempty I] :
    (∑ x : I → Bool, fermiBooleanParity x) = 0 := by
  unfold fermiBooleanParity
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then (-1 : ℝ) else 1)]
  obtain ⟨i⟩ := ‹Nonempty I›
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [Fintype.sum_bool]
  norm_num


def fermiBooleanGramForm (r : I → ℝ) (f g : (I → Bool) → ℝ) : ℝ :=
  ∑ x : I → Bool, ∑ y : I → Bool, f x*fermiBooleanGram r x y*g y

private theorem affine_row (r : I → ℝ) (x : I → Bool) (c d : ℝ) :
    (∑ y : I → Bool, fermiBooleanGram r x y*(c+d*fermiBooleanParity y)) =
      c*(∏ i, (1+r i)) + d*(∏ i, (1-r i))*fermiBooleanParity x := by
  calc
    _ = c*(∑ y : I → Bool, fermiBooleanGram r x y) +
        d*(∑ y : I → Bool, fermiBooleanGram r x y*fermiBooleanParity y) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [fermiBooleanGram_row_sum, fermiBooleanGram_parity_eigen]; ring

theorem fermiBooleanGramForm_affine_parity [Nonempty I] (r : I → ℝ) (a b c d : ℝ) :
    fermiBooleanGramForm r (fun x => a+b*fermiBooleanParity x)
      (fun y => c+d*fermiBooleanParity y) =
      (Fintype.card (I → Bool) : ℝ)*(a*c*(∏ i, (1+r i)) + b*d*(∏ i, (1-r i))) := by
  have hlocal (x : I → Bool) :
      (∑ y : I → Bool, (a+b*fermiBooleanParity x)*fermiBooleanGram r x y*
        (c+d*fermiBooleanParity y)) =
      (a*c*(∏ i, (1+r i)) + b*d*(∏ i, (1-r i))) +
        (a*d*(∏ i, (1-r i)) + b*c*(∏ i, (1+r i)))*fermiBooleanParity x := by
    calc
      _ = (a+b*fermiBooleanParity x)*
          (∑ y : I → Bool, fermiBooleanGram r x y*(c+d*fermiBooleanParity y)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = a*c*(∏ i, (1+r i)) +
          (a*d*(∏ i, (1-r i)) + b*c*(∏ i, (1+r i)))*fermiBooleanParity x +
          b*d*(∏ i, (1-r i))*(fermiBooleanParity x)^2 := by rw [affine_row]; ring
      _ = _ := by rw [fermiBooleanParity_square]; ring
  unfold fermiBooleanGramForm
  rw [Finset.sum_congr rfl (fun x _ => hlocal x), Finset.sum_add_distrib,
    ← Finset.mul_sum, fermiBooleanParity_sum]
  simp [mul_comm]

/-- The two disjoint nonnegative parity classes on a finite Boolean cube. -/
def fermiBooleanParityIndicator (b : Bool) (x : I → Bool) : ℝ :=
  (1+(if b then -1 else 1)*fermiBooleanParity x)/2

omit [DecidableEq I] in
theorem fermiBooleanParityIndicator_zero_or_one (b : Bool) (x : I → Bool) :
    fermiBooleanParityIndicator b x = 0 ∨ fermiBooleanParityIndicator b x = 1 := by
  have h : (fermiBooleanParity x-1)*(fermiBooleanParity x+1) = 0 := by
    nlinarith [fermiBooleanParity_square x]
  rcases mul_eq_zero.mp h with h | h
  · have hp : fermiBooleanParity x = 1 := by linarith
    cases b <;> simp [fermiBooleanParityIndicator, hp]
  · have hp : fermiBooleanParity x = -1 := by linarith
    cases b <;> norm_num [fermiBooleanParityIndicator, hp]

theorem fermiBooleanParityIndicator_gram [Nonempty I] (r : I → ℝ) (b c : Bool) :
    fermiBooleanGramForm r (fermiBooleanParityIndicator b) (fermiBooleanParityIndicator c) =
      (Fintype.card (I → Bool) : ℝ)/4*
        ((∏ i, (1+r i)) + (if b = c then 1 else -1)*(∏ i, (1-r i))) := by
  have hf (b : Bool) : fermiBooleanParityIndicator b =
      fun x : I → Bool => (1/2 : ℝ) + ((if b then -1 else 1)/2)*fermiBooleanParity x := by
    funext x
    unfold fermiBooleanParityIndicator
    ring
  rw [hf b, hf c, fermiBooleanGramForm_affine_parity]
  cases b <;> cases c <;> norm_num <;> ring

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
