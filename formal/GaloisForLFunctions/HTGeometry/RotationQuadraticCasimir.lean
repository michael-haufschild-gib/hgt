import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir

/-!
# Quadratic sums over a rotated triple

If a fixed element rotates a triple of operators by the Pauli structure constants, then the sum of
their squares commutes with it: the structure constants are antisymmetric in the rotated pair while
the anticommutator is symmetric.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem pauliStructureCoeff_antisymmetric_right (c a k : Fin 3) :
    pauliStructureCoeff c k a = -pauliStructureCoeff c a k := by
  fin_cases c <;> fin_cases a <;> fin_cases k <;> simp [pauliStructureCoeff]

section Vanishing

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- An antisymmetric coefficient contracted against a symmetric family vanishes. -/
theorem sum_antisymm_symm_eq_zero (f : Fin 3 → Fin 3 → ℂ) (S : Fin 3 → Fin 3 → Matrix M M ℂ)
    (hf : ∀ a k, f k a = -f a k) (hS : ∀ a k, S k a = S a k) :
    (∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k) = 0 := by
  classical
  have hswap : (∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k) =
      -∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf a k, hS k a, neg_smul]
  have hadd : (∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k) +
      (∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k) = 0 := by
    nth_rewrite 1 [hswap]
    exact neg_add_cancel _
  have h2 : (2 : ℂ) • (∑ a : Fin 3, ∑ k : Fin 3, f a k • S a k) = 0 := by
    rw [two_smul]
    exact hadd
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The sum of squares of a rotated triple commutes with the rotating element.** -/
theorem commute_sum_sq_of_rotation (C : Matrix M M ℂ) (A : Fin 3 → Matrix M M ℂ) (c : Fin 3)
    (hbr : ∀ a : Fin 3, C * A a - A a * C = ∑ k : Fin 3, pauliStructureCoeff c a k • A k) :
    C * (∑ a : Fin 3, A a * A a) = (∑ a : Fin 3, A a * A a) * C := by
  classical
  have hstep : ∀ a : Fin 3, C * (A a * A a) - (A a * A a) * C =
      (C * A a - A a * C) * A a + A a * (C * A a - A a * C) := by
    intro a
    noncomm_ring
  have hsum : C * (∑ a : Fin 3, A a * A a) - (∑ a : Fin 3, A a * A a) * C =
      ∑ a : Fin 3, ∑ k : Fin 3, pauliStructureCoeff c a k • (A k * A a + A a * A k) := by
    rw [Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hstep a, hbr a, Finset.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  have hzero : (∑ a : Fin 3, ∑ k : Fin 3,
      pauliStructureCoeff c a k • (A k * A a + A a * A k)) = 0 := by
    refine sum_antisymm_symm_eq_zero (fun a k => pauliStructureCoeff c a k)
      (fun a k => A k * A a + A a * A k) (fun a k => ?_) (fun a k => ?_)
    · exact pauliStructureCoeff_antisymmetric_right c a k
    · rw [add_comm]
  rw [hzero] at hsum
  exact sub_eq_zero.mp hsum

end Vanishing

end GaloisForLFunctions.HTGeometry
