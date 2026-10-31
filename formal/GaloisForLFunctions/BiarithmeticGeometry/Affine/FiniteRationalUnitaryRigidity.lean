import GaloisForLFunctions.ArithmeticPositiveDuality.AMautnerPhenomenonForTheAffineGroupOfQ
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.NoncommRing

/-!
# Rational affine representations in finite dimension

All nonzero rational translations are conjugate. A finite-dimensional matrix representation
therefore has one trace on them, and finite rank forces this trace to equal the dimension.
For unitary representations, maximal trace forces every translation to be the identity;
the whole representation factors through the slope. No continuity is required.
-/

noncomputable section

open scoped Matrix ComplexOrder
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem trace_translation_ne_zero {n : ℕ}
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : ℚ) (hb : b ≠ 0) :
    (ρ (translation b)).trace = (ρ (translation 1)).trace := by
  have hc := dilation_mul_translation_mul_inv (Units.mk0 b hb) 1
  simp only [Units.val_mk0, mul_one] at hc
  rw [← hc, map_mul, map_mul, Matrix.trace_mul_comm]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- Every finite-dimensional complex affine representation has translation trace equal to its
dimension. A different trace would give too many biorthogonal matrices. -/
theorem finite_rational_affine_translation_trace {n : ℕ}
    (ρ : AffineGroupQ →* Matrix (Fin n) (Fin n) ℂ) (b : ℚ) :
    (ρ (translation b)).trace = (1 : Matrix (Fin n) (Fin n) ℂ).trace := by
  by_cases hb : b = 0
  · simp only [hb, translation_zero, map_one]
  rw [trace_translation_ne_zero ρ b hb]
  by_contra htrace
  have hd : (1 : Matrix (Fin n) (Fin n) ℂ).trace - (ρ (translation 1)).trace ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm htrace)
  let N := n * n + 1
  have hi : LinearIndependent ℂ
      (fun i : Fin N => ρ (translation ((i : ℕ) : ℚ))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    -- Subtracting the outside translation cancels the common off-diagonal trace.
    let A : Matrix (Fin n) (Fin n) ℂ :=
      ρ ((translation ((j : ℕ) : ℚ))⁻¹) - ρ ((translation (N : ℚ))⁻¹)
    have heval (i : Fin N) :
        (A * ρ (translation ((i : ℕ) : ℚ))).trace =
          if i = j then (1 : Matrix (Fin n) (Fin n) ℂ).trace -
            (ρ (translation 1)).trace else 0 := by
      have hlast : ((i : ℕ) : ℚ) - (N : ℚ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (Nat.ne_of_lt i.isLt)
      simp only [A, sub_mul, Matrix.trace_sub, ← map_mul, translation_inv_mul]
      rw [trace_translation_ne_zero ρ _ hlast]
      by_cases hij : i = j
      · subst i
        simp only [sub_self, translation_zero, map_one, if_true]
      · have hdiff : ((i : ℕ) : ℚ) - ((j : ℕ) : ℚ) ≠ 0 := by
          apply sub_ne_zero.mpr
          intro h
          apply hij
          apply Fin.ext
          exact_mod_cast h
        rw [trace_translation_ne_zero ρ _ hdiff, sub_self, if_neg hij]
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (A * M).trace) hc
    simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      heval, mul_zero, Matrix.trace_zero, smul_eq_mul] at h
    have hz : c j * ((1 : Matrix (Fin n) (Fin n) ℂ).trace -
        (ρ (translation 1)).trace) = 0 := by
      simpa only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
    exact (mul_eq_zero.mp hz).resolve_right hd
  have hdim := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_matrix, Module.finrank_self, mul_one] at hdim
  omega

/-- Finite-dimensional unitary representations of `Aff(ℚ)` kill every translation.
The squared Hilbert–Schmidt distance to the identity vanishes by the trace law. -/
theorem finite_rational_affine_unitary_rigidity {n : ℕ}
    (ρ : AffineGroupQ →* Matrix.unitaryGroup (Fin n) ℂ) (b : ℚ) :
    ρ (translation b) = 1 := by
  apply Subtype.ext
  let U : Matrix (Fin n) (Fin n) ℂ := ρ (translation b)
  have hU : Uᴴ * U = 1 := Matrix.UnitaryGroup.star_mul_self (ρ (translation b))
  have ht : U.trace = (1 : Matrix (Fin n) (Fin n) ℂ).trace :=
    finite_rational_affine_translation_trace ((Matrix.unitaryGroup (Fin n) ℂ).subtype.comp ρ) b
  change U = 1
  apply sub_eq_zero.mp
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hexpand : (U - 1)ᴴ * (U - 1) = Uᴴ * U - Uᴴ - U + 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    noncomm_ring
  rw [hexpand, hU, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_conjTranspose, ht]
  simp [Matrix.trace_one]

/-- A finite-dimensional unitary affine representation depends only on the slope. -/
theorem finite_rational_affine_unitary_factors_through_dilations {n : ℕ}
    (ρ : AffineGroupQ →* Matrix.unitaryGroup (Fin n) ℂ) (g : AffineGroupQ) :
    ρ g = ρ (dilation (Units.mk0 (affSlope g) (affSlope_ne_zero g))) := by
  conv_lhs => rw [eq_translation_mul_dilation g]
  rw [map_mul, finite_rational_affine_unitary_rigidity, one_mul]

#print axioms finite_rational_affine_translation_trace
#print axioms finite_rational_affine_unitary_rigidity
#print axioms finite_rational_affine_unitary_factors_through_dilations

end GaloisForLFunctions.BiarithmeticGeometry
