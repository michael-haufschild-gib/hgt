import GaloisForLFunctions.RHTower.RestrictedProjectionCubicTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Restricted-unitary realization of the cubic projection defect

This module passes from the abstract pair-of-projections law to the exact restricted-unitary
normal form.  Unitarity and the Hilbert--Schmidt commutator are bundled as data, so all public
conclusions are closed universal statements over admitted restricted unitaries.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One orthogonal polarization and one unitary whose Hardy commutator is Hilbert--Schmidt. -/
structure RestrictedUnitaryDatum (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  projection : H →L[ℂ] H
  unitary : H →L[ℂ] H
  projection_idempotent : IsIdempotentElem projection
  projection_adjoint : ContinuousLinearMap.adjoint projection = projection
  adjoint_mul_unitary : ContinuousLinearMap.adjoint unitary * unitary = 1
  unitary_mul_adjoint : unitary * ContinuousLinearMap.adjoint unitary = 1
  commutator_isHilbertSchmidt :
    (projection * unitary - unitary * projection).IsHilbertSchmidt

/-- Unitary conjugate of the reference polarization. -/
def RestrictedUnitaryDatum.conjugateProjection (D : RestrictedUnitaryDatum H) :
    H →L[ℂ] H :=
  ContinuousLinearMap.adjoint D.unitary * D.projection * D.unitary

/-- Oriented seam `Q U† P`. -/
def RestrictedUnitaryDatum.adjointHankelSeam (D : RestrictedUnitaryDatum H) :
    H →L[ℂ] H :=
  (1 - D.projection) * ContinuousLinearMap.adjoint D.unitary * D.projection

/-- Oriented seam `Q U P`. -/
def RestrictedUnitaryDatum.forwardHankelSeam (D : RestrictedUnitaryDatum H) :
    H →L[ℂ] H :=
  (1 - D.projection) * D.unitary * D.projection

theorem RestrictedUnitaryDatum.conjugateProjection_idempotent
    (D : RestrictedUnitaryDatum H) :
    IsIdempotentElem D.conjugateProjection := by
  rw [isIdempotentElem_iff]
  have hPP : D.projection * D.projection = D.projection := D.projection_idempotent
  have hUU : D.unitary * ContinuousLinearMap.adjoint D.unitary = 1 :=
    D.unitary_mul_adjoint
  have hcollapse : D.unitary *
      (ContinuousLinearMap.adjoint D.unitary *
        (D.projection * D.unitary)) = D.projection * D.unitary := by
    rw [← mul_assoc, hUU, one_mul]
  have hPPU : D.projection * (D.projection * D.unitary) =
      D.projection * D.unitary := by
    rw [← mul_assoc, hPP]
  rw [RestrictedUnitaryDatum.conjugateProjection]
  simp only [mul_assoc]
  rw [hcollapse, hPPU]

theorem RestrictedUnitaryDatum.conjugateProjection_adjoint
    (D : RestrictedUnitaryDatum H) :
    ContinuousLinearMap.adjoint D.conjugateProjection = D.conjugateProjection := by
  rw [RestrictedUnitaryDatum.conjugateProjection]
  change ContinuousLinearMap.adjoint
      ((ContinuousLinearMap.adjoint D.unitary ∘L D.projection) ∘L D.unitary) =
    (ContinuousLinearMap.adjoint D.unitary ∘L D.projection) ∘L D.unitary
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, D.projection_adjoint]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

theorem RestrictedUnitaryDatum.displacement_eq_adjoint_mul_commutator
    (D : RestrictedUnitaryDatum H) :
    restrictedProjectionDisplacement D.conjugateProjection D.projection =
      ContinuousLinearMap.adjoint D.unitary *
        (D.projection * D.unitary - D.unitary * D.projection) := by
  have hUU : ContinuousLinearMap.adjoint D.unitary * D.unitary = 1 :=
    D.adjoint_mul_unitary
  rw [restrictedProjectionDisplacement, RestrictedUnitaryDatum.conjugateProjection]
  simp only [mul_sub, ← mul_assoc, hUU, one_mul]

theorem RestrictedUnitaryDatum.displacement_isHilbertSchmidt
    (D : RestrictedUnitaryDatum H) :
    (restrictedProjectionDisplacement D.conjugateProjection D.projection).IsHilbertSchmidt := by
  rw [D.displacement_eq_adjoint_mul_commutator]
  exact D.commutator_isHilbertSchmidt.comp_left
    (ContinuousLinearMap.adjoint D.unitary)

theorem RestrictedUnitaryDatum.forwardHankelSeam_isHilbertSchmidt
    (D : RestrictedUnitaryDatum H) : D.forwardHankelSeam.IsHilbertSchmidt := by
  have hP : D.projection * D.projection = D.projection := D.projection_idempotent
  have heq : D.forwardHankelSeam =
      -(D.projection * D.unitary - D.unitary * D.projection) * D.projection := by
    rw [RestrictedUnitaryDatum.forwardHankelSeam]
    noncomm_ring [hP]
  rw [heq]
  exact D.commutator_isHilbertSchmidt.neg.comp_right D.projection

theorem RestrictedUnitaryDatum.adjointHankelSeam_isHilbertSchmidt
    (D : RestrictedUnitaryDatum H) : D.adjointHankelSeam.IsHilbertSchmidt := by
  have hP : D.projection * D.projection = D.projection := D.projection_idempotent
  have hcommAdj :
      (ContinuousLinearMap.adjoint D.unitary * D.projection -
        D.projection * ContinuousLinearMap.adjoint D.unitary).IsHilbertSchmidt := by
    have h := D.commutator_isHilbertSchmidt.adjoint
    simpa only [ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      D.projection_adjoint, ContinuousLinearMap.mul_def] using h
  have heq : D.adjointHankelSeam =
      (ContinuousLinearMap.adjoint D.unitary * D.projection -
        D.projection * ContinuousLinearMap.adjoint D.unitary) * D.projection := by
    rw [RestrictedUnitaryDatum.adjointHankelSeam]
    noncomm_ring [hP]
  rw [heq]
  exact hcommAdj.comp_right D.projection

private theorem hsNormSq_mul_unitary
    (T U : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hU : U * ContinuousLinearMap.adjoint U = 1) :
    hsNormSq (T * U) = hsNormSq T := by
  have hTU : (T * U).IsHilbertSchmidt := hT.comp_right U
  have henergy : MemSchattenClass 1
      (ContinuousLinearMap.adjoint T * T) := by
    have hrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hT hT.adjoint
    exact (memRectSchattenClass_iff_memSchattenClass 1
      (ContinuousLinearMap.adjoint T ∘L T)).mp hrect
  have henergyU : MemSchattenClass 1
      ((ContinuousLinearMap.adjoint T * T) * U) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right henergy U
  rw [← re_opTrace_adjoint_comp_self hTU, ← re_opTrace_adjoint_comp_self hT]
  have hcyc := henergyU.one_opTrace_comp_comm (ContinuousLinearMap.adjoint U)
  have htrace : opTrace
      (ContinuousLinearMap.adjoint (T * U) * (T * U)) =
      opTrace (ContinuousLinearMap.adjoint T * T) := by
    calc
      opTrace (ContinuousLinearMap.adjoint (T * U) * (T * U)) =
          opTrace (ContinuousLinearMap.adjoint U *
            ((ContinuousLinearMap.adjoint T * T) * U)) := by
        congr 1
        change ContinuousLinearMap.adjoint (T ∘L U) ∘L (T ∘L U) =
          ContinuousLinearMap.adjoint U ∘L
            ((ContinuousLinearMap.adjoint T ∘L T) ∘L U)
        rw [ContinuousLinearMap.adjoint_comp]
        simp only [ContinuousLinearMap.comp_assoc]
      _ = opTrace (((ContinuousLinearMap.adjoint T * T) * U) *
          ContinuousLinearMap.adjoint U) := by
        simpa only [ContinuousLinearMap.mul_def] using hcyc
      _ = opTrace (ContinuousLinearMap.adjoint T * T) := by
        congr 1
        noncomm_ring [hU]
  change RCLike.re (opTrace
      (ContinuousLinearMap.adjoint (T * U) * (T * U))) =
    RCLike.re (opTrace (ContinuousLinearMap.adjoint T * T))
  rw [htrace]

private theorem hsNormSq_adjoint_unitary_mul
    (T U : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hU : U * ContinuousLinearMap.adjoint U = 1) :
    hsNormSq (ContinuousLinearMap.adjoint U * T) = hsNormSq T := by
  have hUT : (ContinuousLinearMap.adjoint U * T).IsHilbertSchmidt :=
    hT.comp_left (ContinuousLinearMap.adjoint U)
  rw [← re_opTrace_adjoint_comp_self hUT, ← re_opTrace_adjoint_comp_self hT]
  change RCLike.re (opTrace
      (ContinuousLinearMap.adjoint
        (ContinuousLinearMap.adjoint U * T) *
          (ContinuousLinearMap.adjoint U * T))) =
    RCLike.re (opTrace (ContinuousLinearMap.adjoint T * T))
  congr 2
  change ContinuousLinearMap.adjoint
      (ContinuousLinearMap.adjoint U ∘L T) ∘L
        (ContinuousLinearMap.adjoint U ∘L T) =
    ContinuousLinearMap.adjoint T ∘L T
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change (ContinuousLinearMap.adjoint T ∘L U) ∘L
      (ContinuousLinearMap.adjoint U ∘L T) =
    ContinuousLinearMap.adjoint T ∘L T
  have hmid : U ∘L (ContinuousLinearMap.adjoint U ∘L T) = T := by
    rw [← ContinuousLinearMap.comp_assoc]
    rw [show U ∘L ContinuousLinearMap.adjoint U = 1 by
      simpa only [ContinuousLinearMap.mul_def] using hU]
    rfl
  rw [ContinuousLinearMap.comp_assoc, hmid]

theorem RestrictedUnitaryDatum.forwardProjectionSeam_eq
    (D : RestrictedUnitaryDatum H) :
    restrictedProjectionForwardSeam D.conjugateProjection D.projection =
      D.adjointHankelSeam * D.unitary := by
  have hPP : D.projection * D.projection = D.projection := D.projection_idempotent
  rw [restrictedProjectionForwardSeam, RestrictedUnitaryDatum.conjugateProjection,
    RestrictedUnitaryDatum.adjointHankelSeam]
  noncomm_ring [hPP]

theorem RestrictedUnitaryDatum.backwardProjectionSeam_eq
    (D : RestrictedUnitaryDatum H) :
    restrictedProjectionBackwardSeam D.conjugateProjection D.projection =
      ContinuousLinearMap.adjoint D.unitary * D.forwardHankelSeam := by
  have hUU : ContinuousLinearMap.adjoint D.unitary * D.unitary = 1 :=
    D.adjoint_mul_unitary
  have hUUP : ContinuousLinearMap.adjoint D.unitary *
      (D.unitary * D.projection) = D.projection := by
    rw [← mul_assoc, hUU, one_mul]
  rw [restrictedProjectionBackwardSeam, RestrictedUnitaryDatum.conjugateProjection,
    RestrictedUnitaryDatum.forwardHankelSeam]
  noncomm_ring [hUU, hUUP]

/-- **Exact restricted-unitary two-seam trace law.**  This is `(RUCRI.4)` before the final
circle Fourier-degree identification. -/
theorem RestrictedUnitaryDatum.re_opTrace_cubicDefect_eq_hankelSeams
    (D : RestrictedUnitaryDatum H) :
    (opTrace (restrictedProjectionCubicDefect
      D.conjugateProjection D.projection)).re =
      hsNormSq D.adjointHankelSeam - hsNormSq D.forwardHankelSeam := by
  rw [re_opTrace_restrictedProjectionCubicDefect_eq_seamEnergies
    D.conjugateProjection D.projection D.conjugateProjection_idempotent
    D.projection_idempotent D.conjugateProjection_adjoint D.projection_adjoint
    D.displacement_isHilbertSchmidt]
  rw [D.forwardProjectionSeam_eq, D.backwardProjectionSeam_eq,
    hsNormSq_mul_unitary D.adjointHankelSeam D.unitary
      D.adjointHankelSeam_isHilbertSchmidt D.unitary_mul_adjoint,
    hsNormSq_adjoint_unitary_mul D.forwardHankelSeam D.unitary
      D.forwardHankelSeam_isHilbertSchmidt D.unitary_mul_adjoint]

/-- Closed universal certificate for the exact restricted-unitary cubic operator law. -/
theorem restrictedUnitaryCubicOperator_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (D : RestrictedUnitaryDatum H),
      (restrictedProjectionDisplacement D.conjugateProjection D.projection).IsHilbertSchmidt ∧
      ContinuousLinearMap.adjoint
          (restrictedProjectionDisplacement D.conjugateProjection D.projection) =
        restrictedProjectionDisplacement D.conjugateProjection D.projection ∧
      MemSchattenClass 1
        (restrictedProjectionCubicDefect D.conjugateProjection D.projection) ∧
      ContinuousLinearMap.adjoint
          (restrictedProjectionCubicDefect D.conjugateProjection D.projection) =
        restrictedProjectionCubicDefect D.conjugateProjection D.projection ∧
      restrictedProjectionCubicDefect D.conjugateProjection D.projection =
        restrictedProjectionPositiveChannel D.conjugateProjection D.projection -
          restrictedProjectionPositiveChannel D.projection D.conjugateProjection ∧
      (opTrace (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection)).re =
        hsNormSq D.adjointHankelSeam - hsNormSq D.forwardHankelSeam := by
  intro H _ _ _ D
  exact ⟨D.displacement_isHilbertSchmidt,
    adjoint_restrictedProjectionDisplacement D.conjugateProjection D.projection
      D.conjugateProjection_adjoint D.projection_adjoint,
    restrictedProjectionCubicDefect_memSchattenClass_one
      D.conjugateProjection D.projection D.displacement_isHilbertSchmidt,
    adjoint_restrictedProjectionCubicDefect D.conjugateProjection D.projection
      D.conjugateProjection_adjoint D.projection_adjoint,
    restrictedProjectionCubicDefect_eq_channels
      D.conjugateProjection D.projection D.conjugateProjection_idempotent
        D.projection_idempotent,
    D.re_opTrace_cubicDefect_eq_hankelSeams⟩

end RHTower
