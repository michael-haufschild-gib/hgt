import GaloisForLFunctions.RHTower.MobiusWoldFiniteMomentParityBlindness
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The central Wold patch seam is an exact rank-one coboundary

This file closes the polynomial identity behind the co-moving central-breadth patch proposal.
Adjacent degree-`n` readers of squarefree parity agree on their `n` common Wold layers.  Their
difference is therefore exactly the monic top falling-factorial channel, with coefficient fixed
by the first exterior parity charge.

The transition cochain telescopes on every finite patch chain.  Thus internal scalar patch seams
are algebraically exact; any remaining Route E obstruction must enter through physical
source-to-integer transport, endpoint flux, or premature label fusion.
-/

namespace RHTower

open scoped BigOperators
open Finset Polynomial

/-- Monic top falling-factorial channel of the transition from the breadth patch at `r` to the
patch at `r + 1`. -/
noncomputable def woldPatchSeamPolynomial (r n : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range n, (X - C ((r + j + 1 : ℕ) : ℚ))

theorem woldPatchSeamPolynomial_monic (r n : ℕ) :
    (woldPatchSeamPolynomial r n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

@[simp]
theorem woldPatchSeamPolynomial_natDegree (r n : ℕ) :
    (woldPatchSeamPolynomial r n).natDegree = n := by
  simpa [woldPatchSeamPolynomial] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card
      (R := ℚ) (s := Finset.range n) (fun j => ((r + j + 1 : ℕ) : ℚ)))

/-- Adjacent parity readers have no scalar seam on any of their common Wold layers. -/
theorem woldPatchSeamPolynomial_eval_overlap
    (r n i : ℕ) (hi : i < n) :
    (woldPatchSeamPolynomial r n).eval ((r + i + 1 : ℕ) : ℚ) = 0 := by
  simp only [woldPatchSeamPolynomial, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
  norm_num

/-- The first exterior Wold layer carries exactly one factorial-normalized incidence label. -/
@[simp]
theorem woldPatchSeamPolynomial_eval_firstExterior (r n : ℕ) :
    (woldPatchSeamPolynomial r n).eval ((r + n + 1 : ℕ) : ℚ) =
      n.factorial := by
  simp only [woldPatchSeamPolynomial, eval_prod, eval_sub, eval_X, eval_C]
  calc
    (∏ x ∈ Finset.range n,
      (((r + n + 1 : ℕ) : ℚ) - ((r + x + 1 : ℕ) : ℚ))) =
        ∏ x ∈ Finset.range n, ((n - x : ℕ) : ℚ) := by
          apply Finset.prod_congr rfl
          intro x hx
          rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hx))]
          push_cast
          ring
    _ = ((∏ x ∈ Finset.range n, (n - x : ℕ) : ℕ) : ℚ) := by
          norm_cast
    _ = n.factorial := by
          rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

/-- Exact polynomial form of the rank-one breadth-patch seam.  Factorial scaling avoids division
and is equivalent over `ℚ` to equation (G149). -/
theorem factorial_mul_adjacentParityInterpolants_sub_eq_seamPolynomial
    (n r : ℕ) (P₀ P₁ : ℚ[X])
    (hdeg₀ : P₀.natDegree ≤ n)
    (hdeg₁ : P₁.natDegree ≤ n)
    (hmatch₀ : ∀ k ∈ Finset.range (n + 1),
      P₀.eval ((r + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + k))
    (hmatch₁ : ∀ k ∈ Finset.range (n + 1),
      P₁.eval ((r + 1 + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + 1 + k)) :
    C (n.factorial : ℚ) * (P₁ - P₀) =
      C ((-1 : ℚ) ^ (r + n + 1) * 2 ^ (n + 1)) *
        woldPatchSeamPolynomial r n := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      _ _ (f := fun i : Fin (n + 1) => ((r + i + 1 : ℕ) : ℚ))
  · intro i j hij
    apply Fin.ext
    change (((r + (i : ℕ) + 1 : ℕ) : ℚ) =
      ((r + (j : ℕ) + 1 : ℕ) : ℚ)) at hij
    have hiq : ((i : ℕ) : ℚ) = ((j : ℕ) : ℚ) := by
      push_cast at hij
      linarith
    exact_mod_cast hiq
  · intro i
    rw [eval_mul, eval_C, eval_sub]
    rw [eval_mul, eval_C]
    by_cases hi : (i : ℕ) < n
    · have hi0 : i + 1 < n + 1 := Nat.succ_lt_succ hi
      have hi1 : i < n + 1 := Nat.lt_trans hi (Nat.lt_succ_self n)
      rw [show r + i + 1 = r + 1 + i by omega]
      rw [hmatch₁ i (Finset.mem_range.mpr hi1)]
      rw [show r + 1 + i = r + (i + 1) by omega]
      rw [hmatch₀ (i + 1) (Finset.mem_range.mpr hi0)]
      have hseam :
          (woldPatchSeamPolynomial r n).eval
            ((r + ((i : ℕ) + 1) : ℕ) : ℚ) = 0 := by
        simpa [Nat.add_assoc] using
          woldPatchSeamPolynomial_eval_overlap r n i hi
      rw [hseam]
      ring
    · have hieq : (i : ℕ) = n := by omega
      have hnew := hmatch₁ n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have hnext :=
        eval_next_of_eval_eq_woldParity_on_adjacent n r P₀ hdeg₀ hmatch₀
      rw [hieq]
      rw [show r + n + 1 = r + 1 + n by omega]
      rw [hnew]
      rw [show r + 1 + n = r + n + 1 by omega]
      rw [hnext, woldPatchSeamPolynomial_eval_firstExterior]
      ring
  · have hsub : (P₁ - P₀).natDegree ≤ n :=
      (natDegree_sub_le P₁ P₀).trans (max_le hdeg₁ hdeg₀)
    have hleft :
        (C (n.factorial : ℚ) * (P₁ - P₀)).natDegree ≤ n := by
      exact (natDegree_C_mul_le _ _).trans hsub
    have hright :
        (C ((-1 : ℚ) ^ (r + n + 1) * 2 ^ (n + 1)) *
          woldPatchSeamPolynomial r n).natDegree ≤ n := by
      exact (natDegree_C_mul_le _ _).trans_eq
        (woldPatchSeamPolynomial_natDegree r n)
    simpa only [Fintype.card_fin] using
      (Nat.max_lt.mpr
        ⟨Nat.lt_succ_of_le hleft, Nat.lt_succ_of_le hright⟩)

/-- Adjacent breadth-patch transitions form an exact additive coboundary: every internal seam
cancels in a finite chain, leaving only the two endpoint readers. -/
theorem woldAdjacentPatchTransitions_telescope
    (P : ℕ → ℚ[X]) (a m : ℕ) :
    (∑ i ∈ Finset.range m, (P (a + i + 1) - P (a + i))) =
      P (a + m) - P a := by
  simpa [Nat.add_assoc] using
    (Finset.sum_range_sub (fun i => P (a + i)) m)

end RHTower
