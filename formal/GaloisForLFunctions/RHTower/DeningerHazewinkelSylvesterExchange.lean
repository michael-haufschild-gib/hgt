import GaloisForLFunctions.RHTower.DeningerHazewinkelLocalizedEquivalence
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Sylvester exchange identity for Hazewinkel saturation

This module formalizes the determinant-exchange mechanism used in Appendix A.1--A.2 of
Hazewinkel's proof. Replacing a fixed column of `A` by every column of `Y` produces an ideal that
contains `det(A) * det(Y)`. The stronger displayed equality is Cramer's-rule form of Sylvester's
exchange identity and works over every commutative ring.
-/

open scoped BigOperators

namespace Matrix

theorem det_mul_det_eq_sum_updateCol
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A Y : Matrix ι ι R) (p : ι) :
    A.det * Y.det = ∑ q : ι,
      (Y.cramer (A.col p) q) * (A.updateCol p (Y.col q)).det := by
  have h := congrArg (fun v => A.cramer v p) (Y.mulVec_cramer (A.col p))
  have hself : A.cramer (A.col p) p = A.det := by
    rw [cramer_apply]
    change (A.updateCol p (fun i => A i p)).det = A.det
    rw [updateCol_eq_self]
  have hmul : Y *ᵥ Y.cramer (A.col p) =
      ∑ q : ι, Y.cramer (A.col p) q • Y.col q := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [map_smul, Pi.smul_apply, hself, hmul] at h
  rw [map_sum] at h
  simp only [map_smul, cramer_apply, smul_eq_mul] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    cramer_apply, mul_comm] using h.symm

theorem det_mul_det_mem_updateColIdeal
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A Y : Matrix ι ι R) (p : ι) :
    A.det * Y.det ∈ Ideal.span
      {z : R | ∃ q : ι, z = (A.updateCol p (Y.col q)).det} := by
  rw [det_mul_det_eq_sum_updateCol A Y p]
  apply (Ideal.span _).sum_mem
  intro q hq
  apply Ideal.mul_mem_left
  apply Ideal.subset_span
  exact ⟨q, rfl⟩

end Matrix
