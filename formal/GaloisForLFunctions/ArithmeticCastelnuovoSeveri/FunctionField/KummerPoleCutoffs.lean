import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialCutoffs
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial cutoffs for bounded poles

A reduced radical monomial of pole order `D` admits polynomial multiples
of degree at most `(m-D)/N` when `D≤m`, and none otherwise. These cutoffs
parametrize the one-point pole spaces of the actual normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis

/-- The number of polynomial monomials allowed by a weighted pole bound. -/
def poleDegreeCutoff (N D m : ℕ) : ℕ := if D ≤ m then (m - D) / N + 1 else 0

/-- The degree cutoff is exactly the weighted pole inequality. -/
theorem lt_poleDegreeCutoff_iff (N D m k : ℕ) (hN : 0 < N) :
    k < poleDegreeCutoff N D m ↔ N * k + D ≤ m := by
  unfold poleDegreeCutoff
  split_ifs with hD
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hN]
    rw [Nat.mul_comm k N]
    omega
  · simp only [Nat.not_lt_zero, false_iff]
    omega

/-- Bounded-degree polynomial membership is precisely the nonzero weighted pole bound. -/
theorem mem_degreeLT_poleDegreeCutoff_iff
    {K : Type*} [Field K] (N D m : ℕ) (hN : 0 < N) (f : K[X]) :
    f ∈ degreeLT K (poleDegreeCutoff N D m) ↔
      (f ≠ 0 → N * f.natDegree + D ≤ m) := by
  by_cases hf : f = 0
  · subst f
    simp only [Submodule.zero_mem, ne_eq, not_true_eq_false, false_implies]
  · rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hf, lt_poleDegreeCutoff_iff N D m _ hN]
    exact (imp_iff_right hf).symm

/-- The polynomial cutoff for a reduced radical character in a one-point pole space. -/
def kummerPoleCutoff (p s d r m i : ℕ) : ℕ :=
  poleDegreeCutoff (p ^ (s + 1) + 1)
    (i + (p ^ (d + 1) - 1) *
      (i * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) m

/-- Each character's polynomial degree bound is its exact infinity pole bound. -/
theorem mem_degreeLT_kummerPoleCutoff_iff
    (p : ℕ) [Fact p.Prime] (s d r m : ℕ)
    (i : Fin (p ^ (s + 1) + 1)) (f : (SquareConstantField p s)[X]) :
    f ∈ degreeLT (SquareConstantField p s) (kummerPoleCutoff p s d r m i.val) ↔
      (f ≠ 0 → (p ^ (s + 1) + 1) * f.natDegree +
        (i.val + (p ^ (d + 1) - 1) *
          (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1))) ≤ m) :=
  mem_degreeLT_poleDegreeCutoff_iff _ _ _ (Nat.succ_pos _) f

/-- A zero pole allowance leaves only the constant term of the trivial character. -/
theorem kummerPoleCutoff_zero (p s d r i : ℕ) :
    kummerPoleCutoff p s d r 0 i = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0
  · subst i
    simp only [kummerPoleCutoff, poleDegreeCutoff, zero_mul, Nat.zero_mod,
      mul_zero, zero_add, le_refl, if_true, Nat.sub_self, Nat.zero_div]
  · have h : ¬ i + (p ^ (d + 1) - 1) *
        (i * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)) ≤ 0 := by omega
    rw [kummerPoleCutoff, poleDegreeCutoff, if_neg h, if_neg hi]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
