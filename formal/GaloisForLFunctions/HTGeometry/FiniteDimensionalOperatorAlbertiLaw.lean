import GaloisForLFunctions.HTGeometry.FiniteBuresComparisonLaw
import GaloisForLFunctions.HTGeometry.NuclearTraceLaw
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm

/-!
# Finite-dimensional operator form of Alberti's variational law

The established finite Bures theorem is matrix-valued, while separable compression arguments live
in bounded-operator algebras on finite-dimensional subspaces.  This file gives the exact
star-algebra, positivity, trace, inverse, square-root, fidelity, and reporter bridges between those
two interfaces.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Set
open scoped ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Star-algebra coordinates of a bounded operator in the standard finite orthonormal basis. -/
noncomputable def finiteOperatorMatrixEquiv :
    (E →L[ℂ] E) ≃⋆ₐ[ℂ]
      Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  let e : (E →ₗ[ℂ] E) ≃⋆ₐ[ℂ] (E →L[ℂ] E) :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }
  e.symm.trans (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ E))

/-- Every bounded operator on a finite-dimensional Hilbert space is Hilbert--Schmidt. -/
theorem finiteDimensional_isHilbertSchmidt (T : E →L[ℂ] E) :
    T.IsHilbertSchmidt := by
  rw [isHilbertSchmidt_iff_summable
    (stdOrthonormalBasis ℂ E).toHilbertBasis]
  exact (hasSum_fintype _).summable

@[simp] theorem finiteOperatorMatrixEquiv_apply (T : E →L[ℂ] E) :
    finiteOperatorMatrixEquiv T = LinearMap.toMatrix
      (stdOrthonormalBasis ℂ E).toBasis
      (stdOrthonormalBasis ℂ E).toBasis T.toLinearMap := rfl

/-- Operator trace is literal matrix trace in finite orthonormal coordinates. -/
theorem opTrace_eq_finiteOperatorMatrix_trace (T : E →L[ℂ] E) :
    opTrace T = (finiteOperatorMatrixEquiv T).trace := by
  let b := stdOrthonormalBasis ℂ E
  have hOne : (1 : E →L[ℂ] E).IsHilbertSchmidt :=
    finiteDimensional_isHilbertSchmidt 1
  have hT : T.IsHilbertSchmidt := finiteDimensional_isHilbertSchmidt T
  have hone : (1 ∘L T : E →L[ℂ] E) = T := by ext; rfl
  calc
    opTrace T = opTrace (1 ∘L T) := by rw [hone]
    _ = ∑' i : Fin (Module.finrank ℂ E), inner ℂ (b i) (T (b i)) := by
      rw [opTrace_comp_eq_tsum_basis hOne hT b.toHilbertBasis]
      apply tsum_congr
      intro i
      rw [hone]
      simp
    _ = ∑ i : Fin (Module.finrank ℂ E), inner ℂ (b i) (T (b i)) := tsum_fintype _
    _ = (finiteOperatorMatrixEquiv T).trace := by
      change (∑ i, inner ℂ (b i) (T (b i))) =
        (LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap).trace
      simp [Matrix.trace, LinearMap.toMatrix_apply, b.repr_apply_apply]

/-- Finite matrix coordinates reflect operator positivity exactly. -/
theorem finiteOperatorMatrixEquiv_posSemidef_iff (T : E →L[ℂ] E) :
    (finiteOperatorMatrixEquiv (E := E) T).PosSemidef ↔ T.IsPositive := by
  have h1 := LinearMap.posSemidef_toMatrix_iff
    (A := T.toLinearMap) (stdOrthonormalBasis ℂ E)
  have h2 := LinearMap.isPositive_toContinuousLinearMap_iff T.toLinearMap
  exact h1.trans h2.symm

/-- Finite coordinates carry the semiring inverse of every unit to the semiring inverse. -/
theorem finiteOperatorMatrixEquiv_ringInverse
    (T : E →L[ℂ] E) (hT : IsUnit T) :
    finiteOperatorMatrixEquiv (Ring.inverse T) =
      Ring.inverse (finiteOperatorMatrixEquiv T) := by
  have hm : IsUnit (finiteOperatorMatrixEquiv T) := hT.map finiteOperatorMatrixEquiv
  apply hm.mul_left_cancel
  rw [← map_mul, Ring.mul_inverse_cancel T hT, map_one,
    Ring.mul_inverse_cancel _ hm]

/-- Finite coordinates carry the positive square root of a positive operator to matrix square
root.  The proof uses uniqueness of the nonnegative square root rather than an opaque continuity
transport. -/
theorem finiteOperatorMatrixEquiv_sqrt
    (T : E →L[ℂ] E) (hT : 0 ≤ T) :
    finiteOperatorMatrixEquiv (CFC.sqrt T) =
      CFC.sqrt (finiteOperatorMatrixEquiv T) := by
  have hrootPos : (CFC.sqrt T).IsPositive :=
    (nonneg_iff_isPositive _).1 (CFC.sqrt_nonneg T)
  have hrootMatrixPSD : (finiteOperatorMatrixEquiv (CFC.sqrt T)).PosSemidef :=
    (finiteOperatorMatrixEquiv_posSemidef_iff (CFC.sqrt T)).2 hrootPos
  have hrootMatrix : 0 ≤ finiteOperatorMatrixEquiv (CFC.sqrt T) :=
    Matrix.nonneg_iff_posSemidef.mpr hrootMatrixPSD
  apply Eq.symm
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self T hT]
  · exact hrootMatrix

/-- Operator Bures root fidelity equals the established matrix Bures root fidelity on every
finite-dimensional Hilbert space. -/
theorem operatorBuresRootFidelity_eq_finiteMatrix
    (C M : E →L[ℂ] E) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    operatorBuresRootFidelity C M =
      GaloisForLFunctions.HTGeometry.finiteBuresRootFidelity
        (finiteOperatorMatrixEquiv C) (finiteOperatorMatrixEquiv M) := by
  let RC : E →L[ℂ] E := CFC.sqrt C
  let RM : E →L[ℂ] E := CFC.sqrt M
  let T : E →L[ℂ] E := RC ∘L RM
  have hRCstar : star RC = RC :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C)).star_eq
  have hRMstar : star RM = RM :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq
  have henergy : star T * T = CFC.conjSqrt M C := by
    calc
      star T * T = (RM * RC) * (RC * RM) := by
        change star (RC * RM) * (RC * RM) = _
        rw [star_mul, hRCstar, hRMstar]
      _ = RM * (RC * RC) * RM := by simp only [mul_assoc]
      _ = RM * C * RM := by rw [CFC.sqrt_mul_sqrt_self C hC]
      _ = CFC.conjSqrt M C := by rfl
  have henergyNonneg : 0 ≤ star T * T := star_mul_self_nonneg T
  have habs : finiteOperatorMatrixEquiv (absOp T) =
      CFC.sqrt (CFC.conjSqrt
        (finiteOperatorMatrixEquiv M) (finiteOperatorMatrixEquiv C)) := by
    unfold absOp
    rw [finiteOperatorMatrixEquiv_sqrt (star T * T) henergyNonneg, henergy,
      CFC.conjSqrt_apply, map_mul, map_mul, finiteOperatorMatrixEquiv_sqrt M hM]
    simp only [CFC.conjSqrt_apply]
  have htrace : MemSchattenClass 1 T :=
    memSchattenClass_one_comp
      (finiteDimensional_isHilbertSchmidt RC)
      (finiteDimensional_isHilbertSchmidt RM)
  unfold operatorBuresRootFidelity
  change traceNorm E T = _
  rw [traceNorm_eq_re_opTrace_absOp htrace,
    opTrace_eq_finiteOperatorMatrix_trace, habs]
  exact GaloisForLFunctions.HTGeometry.finiteBuresRootFidelity_comm
    ((finiteOperatorMatrixEquiv_posSemidef_iff M).2
      ((nonneg_iff_isPositive M).1 hM))
    ((finiteOperatorMatrixEquiv_posSemidef_iff C).2
      ((nonneg_iff_isPositive C).1 hC))

/-- Additive Alberti objective in finite-dimensional bounded-operator form. -/
def finiteOperatorReporterHalfSum (C M A : E →L[ℂ] E) : ℝ :=
  ((opTrace (C ∘L A)).re +
    (opTrace (M ∘L Ring.inverse A)).re) / 2

/-- Every positive finite-dimensional operator pair admits a strictly-positive bounded reporter
whose additive Alberti objective is within any positive tolerance of Bures root fidelity. -/
theorem exists_finiteOperatorReporterHalfSum_lt
    (C M : E →L[ℂ] E) (hC : 0 ≤ C) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : E →L[ℂ] E, IsStrictlyPositive A ∧
      finiteOperatorReporterHalfSum C M A <
        operatorBuresRootFidelity C M + ε := by
  let e := finiteOperatorMatrixEquiv (E := E)
  let CM := e C
  let MM := e M
  have hCM : CM.PosSemidef := (finiteOperatorMatrixEquiv_posSemidef_iff C).2
    ((nonneg_iff_isPositive C).1 hC)
  have hMM : MM.PosSemidef := (finiteOperatorMatrixEquiv_posSemidef_iff M).2
    ((nonneg_iff_isPositive M).1 hM)
  let values : Set ℝ := {q | ∃ A : Matrix (Fin (Module.finrank ℂ E))
      (Fin (Module.finrank ℂ E)) ℂ,
    A.PosDef ∧ q = GaloisForLFunctions.HTGeometry.finiteBuresReporterHalfSum CM MM A}
  have hcapacity : sInf values =
      GaloisForLFunctions.HTGeometry.finiteBuresRootFidelity CM MM :=
    GaloisForLFunctions.HTGeometry.finiteBuresReporterHalfSumCapacity_eq_rootFidelity
      hCM hMM
  have hlt : sInf values <
      GaloisForLFunctions.HTGeometry.finiteBuresRootFidelity CM MM + ε := by
    rw [hcapacity]
    linarith
  have hvalues : values.Nonempty :=
    GaloisForLFunctions.HTGeometry.finiteBuresReporterHalfSumCapacity_values_nonempty
      CM MM
  obtain ⟨q, hq, hq_lt⟩ := exists_lt_of_csInf_lt hvalues hlt
  obtain ⟨AM, hAM, rfl⟩ := hq
  let A : E →L[ℂ] E := e.symm AM
  have heA : e A = AM := e.apply_symm_apply AM
  have hAunit : IsUnit A := by
    have hAMunit : IsUnit AM := hAM.isStrictlyPositive.isUnit
    exact hAMunit.map e.symm
  have hAnonneg : 0 ≤ A := by
    apply (nonneg_iff_isPositive A).2
    apply (finiteOperatorMatrixEquiv_posSemidef_iff A).1
    rw [heA]
    exact hAM.posSemidef
  have hA : IsStrictlyPositive A :=
    IsStrictlyPositive.iff_of_unital.2 ⟨hAnonneg, hAunit⟩
  refine ⟨A, hA, ?_⟩
  have heInv : e (Ring.inverse A) = Ring.inverse AM := by
    rw [finiteOperatorMatrixEquiv_ringInverse A hAunit, heA]
  have hsource : opTrace (C ∘L A) = (CM * AM).trace := by
    rw [opTrace_eq_finiteOperatorMatrix_trace]
    change (e (C * A)).trace = _
    rw [map_mul, heA]
  have htarget : opTrace (M ∘L Ring.inverse A) = (MM * AM⁻¹).trace := by
    rw [opTrace_eq_finiteOperatorMatrix_trace]
    change (e (M * Ring.inverse A)).trace = _
    rw [map_mul, heInv, ← Matrix.nonsing_inv_eq_ringInverse]
  rw [finiteOperatorReporterHalfSum, hsource, htarget]
  rw [operatorBuresRootFidelity_eq_finiteMatrix C M hC hM]
  exact hq_lt

end RHTower
