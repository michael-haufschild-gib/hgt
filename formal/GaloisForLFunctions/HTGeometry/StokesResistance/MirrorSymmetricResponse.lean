import GaloisForLFunctions.HTGeometry.StokesResistance.BinaryOctahedralApplication

/-!
# Mirror-fixed reciprocal response tensors

This module formalizes the involution specialization of the projector and character method in
Moreau, *The Stokes resistance of an arbitrary particle: a classification of hydrodynamic
symmetries*, arXiv:2608.23907v1.

If `A² = I` on a `d`-dimensional carrier, the product of the symmetric-tensor projector with the
mirror projector is idempotent. Its rank is

`(d² + 2d + trace(A)²) / 4`.

This gives the exact dimension of reciprocal symmetric response tensors fixed by the involution.
The corpus qubit-factor swap gives a concrete non-hydrodynamic application: exactly seven of the
ten symmetric responses on its four-dimensional carrier survive.
-/

open scoped BigOperators Kronecker Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

variable {i : Type*} [Fintype i] [DecidableEq i]

/-- Symmetric-tensor projection commutes with every doubled action. -/
theorem symmetricTensorProjection_commutes_kronecker_self
    (A : Matrix i i ℂ) :
    symmetricTensorProjection * (A ⊗ₖ A) =
      (A ⊗ₖ A) * symmetricTensorProjection := by
  rw [symmetricTensorProjection, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    tensorSwap_commutes_kronecker_self]

/-- Projection onto reciprocal symmetric tensors fixed by the mirror `A`. -/
def mirrorSymmetricResponseProjection (A : Matrix i i ℂ) :
    Matrix (i × i) (i × i) ℂ :=
  symmetricTensorProjection *
    ((2 : ℂ)⁻¹ • (1 + (A ⊗ₖ A)))

/-- The doubled mirror projector is idempotent when `A` is an involution. -/
theorem mirrorTensorProjection_isIdempotent
    (A : Matrix i i ℂ) (hA : A * A = 1) :
    IsIdempotentElem ((2 : ℂ)⁻¹ •
      (1 + (A ⊗ₖ A))) := by
  rw [IsIdempotentElem, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hAA : (A ⊗ₖ A) * (A ⊗ₖ A) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hA, Matrix.one_kronecker_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hAA]
  module

/-- Symmetric and mirror projections combine to an idempotent response projector. -/
theorem mirrorSymmetricResponseProjection_isIdempotent
    (A : Matrix i i ℂ) (hA : A * A = 1) :
    IsIdempotentElem (mirrorSymmetricResponseProjection A) := by
  let S : Matrix (i × i) (i × i) ℂ := symmetricTensorProjection
  let Q : Matrix (i × i) (i × i) ℂ :=
    (2 : ℂ)⁻¹ • (1 + (A ⊗ₖ A))
  have hS : S * S = S := symmetricTensorProjection_mul_self
  have hQ : Q * Q = Q := (mirrorTensorProjection_isIdempotent A hA).eq
  have hcomm : Q * S = S * Q := by
    dsimp [Q, S]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one,
      symmetricTensorProjection_commutes_kronecker_self]
  rw [IsIdempotentElem]
  change S * Q * (S * Q) = S * Q
  calc
    S * Q * (S * Q) = S * (Q * S) * Q := by noncomm_ring
    _ = S * (S * Q) * Q := by rw [hcomm]
    _ = (S * S) * (Q * Q) := by noncomm_ring
    _ = S * Q := by rw [hS, hQ]

/-- Mirror-fixed symmetric-response character formula. -/
theorem trace_mirrorSymmetricResponseProjection
    (A : Matrix i i ℂ) (hA : A * A = 1) :
    Matrix.trace (mirrorSymmetricResponseProjection A) =
      ((Fintype.card i : ℂ) ^ (2 : ℕ) + 2 * Fintype.card i +
        Matrix.trace A ^ (2 : ℕ)) / 4 := by
  rw [mirrorSymmetricResponseProjection, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add,
    trace_symmetricTensorProjection,
    trace_symmetricTensorProjection_mul_kronecker_self, hA,
    Matrix.trace_one]
  ring

/-- Projector trace equals exact mirror-fixed reciprocal-response dimension. -/
theorem trace_mirrorSymmetricResponseProjection_eq_finrank
    (A : Matrix i i ℂ) (hA : A * A = 1) :
    Matrix.trace (mirrorSymmetricResponseProjection A) =
      (Module.finrank ℂ
        (LinearMap.range (mirrorSymmetricResponseProjection A).toLin') : ℂ) := by
  have hP : IsIdempotentElem (mirrorSymmetricResponseProjection A).toLin' := by
    rw [IsIdempotentElem]
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin'
        (mirrorSymmetricResponseProjection_isIdempotent A hA).eq
  have hproj : LinearMap.IsProj
      (LinearMap.range (mirrorSymmetricResponseProjection A).toLin')
      (mirrorSymmetricResponseProjection A).toLin' :=
    LinearMap.IsIdempotentElem.isProj_range _ hP
  simpa using hproj.trace

open QuantumAlg.QubitTwoDesign

/-- Seven of ten symmetric responses survive the qubit-factor-swap mirror. -/
theorem qubitSwap_mirrorSymmetricResponse_finrank :
    Module.finrank ℂ
      (LinearMap.range
        (mirrorSymmetricResponseProjection qubitSwap).toLin') = 7 := by
  have htrace := trace_mirrorSymmetricResponseProjection_eq_finrank qubitSwap
    (by rw [qubitSwap_eq_tensorSwap]; exact tensorSwap_mul_self)
  rw [trace_mirrorSymmetricResponseProjection qubitSwap
      (by rw [qubitSwap_eq_tensorSwap]; exact tensorSwap_mul_self),
    qubitSwap_trace_from_symmetricTensor] at htrace
  norm_num at htrace
  exact_mod_cast htrace.symm

end GaloisForLFunctions.HTGeometry.StokesResistance
