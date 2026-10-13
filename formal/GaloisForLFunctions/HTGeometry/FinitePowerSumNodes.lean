import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic

/-! Constant power sums on finite nodes have an exact coefficient-dimension threshold. -/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem finite_power_sum_succ_constant_iff (r n : ℕ) (x : Fin (r + 1) → ℝ)
    (hx : Function.Injective x) (hn : n ≤ r) (c : Fin n → ℝ) :
    (∀ i, (∑ j : Fin n, c j * x i ^ ((j : ℕ) + 1)) =
      ∑ j : Fin n, c j * x 0 ^ ((j : ℕ) + 1)) ↔ c = 0 := by
  classical
  constructor
  · intro h
    let p : Polynomial ℝ := ∑ j : Fin n, Polynomial.monomial ((j : ℕ) + 1) (c j)
    have hpdeg : p.natDegree ≤ n := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (Polynomial.natDegree_monomial_le (c j)).trans (Nat.succ_le_of_lt j.isLt)
    have hp : p = Polynomial.C (p.eval (x 0)) :=
      Polynomial.eq_of_natDegree_lt_card_of_eval_eq p (Polynomial.C (p.eval (x 0))) hx
        (fun i => by simpa [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial] using h i)
        (by simpa using lt_of_le_of_lt hpdeg (Nat.lt_succ_of_le hn))
    funext j
    have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff ((j : ℕ) + 1)) hp
    simpa [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj] using hcoeff
  · rintro rfl i
    simp

theorem exists_ne_zero_finite_power_sum_constant (r n : ℕ) (x : Fin (r + 1) → ℝ)
    (hn : r < n) :
    ∃ c : Fin n → ℝ, c ≠ 0 ∧ ∀ i,
      (∑ j : Fin n, c j * x i ^ ((j : ℕ) + 1)) =
        ∑ j : Fin n, c j * x 0 ^ ((j : ℕ) + 1) := by
  classical
  let B : Matrix (Fin r) (Fin n) ℝ :=
    fun i j => x i.succ ^ ((j : ℕ) + 1) - x 0 ^ ((j : ℕ) + 1)
  have hker : LinearMap.ker B.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hn)
  have hex : ∃ c : Fin n → ℝ, c ≠ 0 ∧ B.mulVecLin c = 0 := by
    by_contra hnone
    apply hker
    apply LinearMap.ker_eq_bot.mpr
    intro u v huv
    by_contra hne
    exact hnone ⟨u - v, sub_ne_zero.mpr hne, by simp only [map_sub, huv, sub_self]⟩
  obtain ⟨c, hc, hBc⟩ := hex
  refine ⟨c, hc, fun i => ?_⟩
  refine Fin.cases rfl (fun j => ?_) i
  have h := congrFun hBc j
  change (∑ k : Fin n, (x j.succ ^ ((k : ℕ) + 1) - x 0 ^ ((k : ℕ) + 1)) * c k) = 0 at h
  simp only [sub_mul, Finset.sum_sub_distrib] at h
  simpa only [mul_comm] using sub_eq_zero.mp h

end GaloisForLFunctions.HTGeometry
