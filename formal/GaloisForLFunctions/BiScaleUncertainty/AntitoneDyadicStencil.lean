import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A uniform dyadic cancellation bound for bounded antitone sequences. -/

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
set_option autoImplicit false

private def pairedDrop (f : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, (f (2*k+1) - f (2*k+2))

private theorem pairedDrop_bounds {f : ℕ → ℝ} (hf : Antitone f)
    (h0 : ∀ j, 0 ≤ f j) (h1 : f 1 ≤ 1) (M : ℕ) :
    0 ≤ pairedDrop f M ∧ pairedDrop f M ≤ 1 := by
  have ht : ∀ M, pairedDrop f M ≤ f 1 - f (2*M+1) := by
    intro M
    induction M with
    | zero => simp [pairedDrop]
    | succ M ih =>
      simp only [pairedDrop, Finset.sum_range_succ] at *
      have hg := hf (show 2*M+2 ≤ 2*(M+1)+1 by omega)
      linarith
  constructor
  · exact Finset.sum_nonneg fun k _ => sub_nonneg.mpr (hf (by omega))
  · have := ht M
    have := h0 (2*M+1)
    linarith

private theorem sum_dyadic_pairs (f : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 (2*M), f j) -
      2*(∑ j ∈ Finset.Icc 1 M, f (2*j)) = pairedDrop f M := by
  induction M with
  | zero => simp [pairedDrop]
  | succ M ih =>
    rw [show 2*(M+1) = (2*M+1)+1 by omega,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ (2*M+1)+1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ 2*M+1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M+1)]
    simp only [pairedDrop, Finset.sum_range_succ] at ih ⊢
    rw [show 2*(M+1) = 2*M+2 by omega]
    linear_combination ih

/-- The bi-null dilation stencil of any decreasing sequence in `[0,1]`
lies in `[-2,1]`, independently of the number of terms. -/
theorem antitone_dyadic_stencil_bounds {f : ℕ → ℝ} (hf : Antitone f)
    (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ 1) (N : ℕ) :
    let D := (∑ j ∈ Finset.Icc 1 (4*N), f j) -
      4*(∑ j ∈ Finset.Icc 1 (2*N), f (2*j)) +
      4*(∑ j ∈ Finset.Icc 1 N, f (4*j));
    -2 ≤ D ∧ D ≤ 1 := by
  have ha := pairedDrop_bounds hf h0 (h1 1) (2*N)
  have hf2 : Antitone (fun j => f (2*j)) := fun a b h => hf (by omega)
  have hb := pairedDrop_bounds hf2 (fun j => h0 (2*j)) (h1 2) N
  have hA := sum_dyadic_pairs f (2*N)
  have hB := sum_dyadic_pairs (fun j => f (2*j)) N
  simp only [show 2*(2*N) = 4*N by omega] at hA
  simp only [show ∀ j : ℕ, 2*(2*j) = 4*j by intro j; omega] at hB
  dsimp
  constructor <;> linarith

end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
