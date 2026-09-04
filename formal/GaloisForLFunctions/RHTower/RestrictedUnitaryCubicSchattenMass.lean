/-
# Exact restricted-unitary cubic Schatten mass

The cubic displacement mass splits into the third Schatten masses of the two oriented Hankel
seams.  This is the unsigned companion of the relative-index trace law.
-/
import GaloisForLFunctions.HTGeometry.SchattenCubicMass
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicIndex

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem adjoint_forwardHankelSeam
    (D : RestrictedUnitaryDatum H) :
    ContinuousLinearMap.adjoint D.forwardHankelSeam =
      D.projection * ContinuousLinearMap.adjoint D.unitary * (1 - D.projection) := by
  rw [RestrictedUnitaryDatum.forwardHankelSeam]
  change ContinuousLinearMap.adjoint
      (((1 - D.projection) ∘L D.unitary) ∘L D.projection) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    D.projection_adjoint, ContinuousLinearMap.adjoint.map_sub,
    ContinuousLinearMap.adjoint_one, D.projection_adjoint]
  ext x
  rfl

private theorem adjoint_adjointHankelSeam
    (D : RestrictedUnitaryDatum H) :
    ContinuousLinearMap.adjoint D.adjointHankelSeam =
      D.projection * D.unitary * (1 - D.projection) := by
  rw [RestrictedUnitaryDatum.adjointHankelSeam]
  change ContinuousLinearMap.adjoint
      (((1 - D.projection) ∘L ContinuousLinearMap.adjoint D.unitary) ∘L
        D.projection) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    D.projection_adjoint, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
    D.projection_adjoint]
  ext x
  rfl

private theorem RestrictedUnitaryDatum.cubicDisplacement_energy_eq_hankelEnergies
    (D : RestrictedUnitaryDatum H) :
    ContinuousLinearMap.adjoint
        (restrictedProjectionDisplacement D.conjugateProjection D.projection) *
          restrictedProjectionDisplacement D.conjugateProjection D.projection =
      ContinuousLinearMap.adjoint D.forwardHankelSeam * D.forwardHankelSeam +
        ContinuousLinearMap.adjoint
            (ContinuousLinearMap.adjoint D.adjointHankelSeam) *
          ContinuousLinearMap.adjoint D.adjointHankelSeam := by
  have hPP : D.projection * D.projection = D.projection := D.projection_idempotent
  have hVU : ContinuousLinearMap.adjoint D.unitary * D.unitary = 1 :=
    D.adjoint_mul_unitary
  have hRR : D.conjugateProjection * D.conjugateProjection =
      D.conjugateProjection := D.conjugateProjection_idempotent
  have hdelta :
      ContinuousLinearMap.adjoint
          (restrictedProjectionDisplacement D.conjugateProjection D.projection) *
        restrictedProjectionDisplacement D.conjugateProjection D.projection =
      D.conjugateProjection + D.projection -
        D.conjugateProjection * D.projection -
          D.projection * D.conjugateProjection := by
    rw [adjoint_restrictedProjectionDisplacement
      D.conjugateProjection D.projection D.conjugateProjection_adjoint
        D.projection_adjoint, restrictedProjectionDisplacement]
    noncomm_ring [hPP, hRR]
  have hforward :
      ContinuousLinearMap.adjoint D.forwardHankelSeam * D.forwardHankelSeam =
        D.projection - D.projection * D.conjugateProjection * D.projection := by
    rw [adjoint_forwardHankelSeam D, RestrictedUnitaryDatum.forwardHankelSeam,
      RestrictedUnitaryDatum.conjugateProjection]
    noncomm_ring [hPP, hVU]
  have hbackward :
      ContinuousLinearMap.adjoint
          (ContinuousLinearMap.adjoint D.adjointHankelSeam) *
        ContinuousLinearMap.adjoint D.adjointHankelSeam =
      (1 - D.projection) * D.conjugateProjection * (1 - D.projection) := by
    rw [ContinuousLinearMap.adjoint_adjoint, adjoint_adjointHankelSeam D,
      RestrictedUnitaryDatum.adjointHankelSeam,
      RestrictedUnitaryDatum.conjugateProjection]
  rw [hdelta, hforward, hbackward]
  noncomm_ring

private theorem RestrictedUnitaryDatum.hankelAbsoluteValues_orthogonal
    (D : RestrictedUnitaryDatum H) :
    absOp D.forwardHankelSeam *
        absOp (ContinuousLinearMap.adjoint D.adjointHankelSeam) = 0 ∧
      absOp (ContinuousLinearMap.adjoint D.adjointHankelSeam) *
        absOp D.forwardHankelSeam = 0 := by
  have hPP : D.projection * D.projection = D.projection := D.projection_idempotent
  have hforward : D.forwardHankelSeam * D.projection = D.forwardHankelSeam := by
    rw [RestrictedUnitaryDatum.forwardHankelSeam]
    noncomm_ring [hPP]
  have hadjoint : ContinuousLinearMap.adjoint D.adjointHankelSeam *
      (1 - D.projection) = ContinuousLinearMap.adjoint D.adjointHankelSeam := by
    rw [adjoint_adjointHankelSeam D]
    noncomm_ring [hPP]
  exact absOp_complementary_right_support
    D.forwardHankelSeam (ContinuousLinearMap.adjoint D.adjointHankelSeam)
      D.projection D.projection_idempotent D.projection_adjoint hforward hadjoint

/-- Both oriented Hankel seams belong to Schatten class three. -/
theorem RestrictedUnitaryDatum.hankelSeams_memSchattenClass_three
    (D : RestrictedUnitaryDatum H) :
    MemSchattenClass 3 D.forwardHankelSeam ∧
      MemSchattenClass 3 D.adjointHankelSeam := by
  constructor
  · exact ((memSchattenClass_two_iff_isHilbertSchmidt D.forwardHankelSeam).2
      D.forwardHankelSeam_isHilbertSchmidt).mono (by norm_num) (by norm_num)
  · exact ((memSchattenClass_two_iff_isHilbertSchmidt D.adjointHankelSeam).2
      D.adjointHankelSeam_isHilbertSchmidt).mono (by norm_num) (by norm_num)

/-- **Exact cubic Schatten mass:** the nuclear mass of the cubic displacement is the sum of the
third Schatten masses of the two oriented Hankel seams. -/
theorem RestrictedUnitaryDatum.traceNorm_cubicDefect_eq_hankelSchattenMass
    (D : RestrictedUnitaryDatum H) :
    traceNorm H (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection) =
      GaloisForLFunctions.HTGeometry.schattenNorm 3 D.forwardHankelSeam ^ (3 : ℝ) +
        GaloisForLFunctions.HTGeometry.schattenNorm 3 D.adjointHankelSeam ^ (3 : ℝ) := by
  let T := restrictedProjectionDisplacement D.conjugateProjection D.projection
  let A := D.forwardHankelSeam
  let B := ContinuousLinearMap.adjoint D.adjointHankelSeam
  have hTself : IsSelfAdjoint T :=
    adjoint_restrictedProjectionDisplacement
      D.conjugateProjection D.projection D.conjugateProjection_adjoint
        D.projection_adjoint
  have hmass := traceNorm_cube_eq_add_schattenNorm_three_rpow
    T A B hTself D.displacement_isHilbertSchmidt
      D.forwardHankelSeam_isHilbertSchmidt D.adjointHankelSeam_isHilbertSchmidt.adjoint
      D.cubicDisplacement_energy_eq_hankelEnergies
      D.hankelAbsoluteValues_orthogonal.1 D.hankelAbsoluteValues_orthogonal.2
  rw [schattenNorm_adjoint] at hmass
  simpa only [T, A, B, restrictedProjectionCubicDefect] using hmass

/-- Absolute cubic trace is bounded by the exact two-seam Schatten mass. -/
theorem RestrictedUnitaryDatum.abs_re_opTrace_cubicDefect_le_hankelSchattenMass
    (D : RestrictedUnitaryDatum H) :
    |(opTrace (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection)).re| ≤
      GaloisForLFunctions.HTGeometry.schattenNorm 3 D.forwardHankelSeam ^ (3 : ℝ) +
        GaloisForLFunctions.HTGeometry.schattenNorm 3 D.adjointHankelSeam ^ (3 : ℝ) := by
  have hnuc := restrictedProjectionCubicDefect_memSchattenClass_one
    D.conjugateProjection D.projection D.displacement_isHilbertSchmidt
  calc
    |(opTrace (restrictedProjectionCubicDefect
        D.conjugateProjection D.projection)).re| ≤
        ‖opTrace (restrictedProjectionCubicDefect
          D.conjugateProjection D.projection)‖ := Complex.abs_re_le_norm _
    _ ≤ traceNorm H (restrictedProjectionCubicDefect
          D.conjugateProjection D.projection) := norm_opTrace_le_traceNorm hnuc
    _ = _ := D.traceNorm_cubicDefect_eq_hankelSchattenMass

/-- A relative index of absolute value one forces at least unit two-seam cubic mass. -/
theorem RestrictedUnitaryDatum.one_le_hankelSchattenMass_of_abs_relativeIndex_eq_one
    (D : RestrictedUnitaryDatum H)
    (hindex : |(restrictedProjectionRelativeIndex
      D.conjugateProjection D.projection : ℝ)| = 1) :
    1 ≤ GaloisForLFunctions.HTGeometry.schattenNorm 3 D.forwardHankelSeam ^ (3 : ℝ) +
      GaloisForLFunctions.HTGeometry.schattenNorm 3 D.adjointHankelSeam ^ (3 : ℝ) := by
  have hbound := D.abs_re_opTrace_cubicDefect_le_hankelSchattenMass
  rw [D.opTrace_cubicDefect_eq_relativeIndex] at hbound
  norm_cast at hbound
  simpa [hindex] using hbound

/-- Closed universal certificate for RUCRI-A+. -/
theorem restrictedUnitaryCubicSchattenMass_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (D : RestrictedUnitaryDatum H),
      MemSchattenClass 3 D.forwardHankelSeam ∧
      MemSchattenClass 3 D.adjointHankelSeam ∧
      traceNorm H (restrictedProjectionCubicDefect
          D.conjugateProjection D.projection) =
        GaloisForLFunctions.HTGeometry.schattenNorm 3 D.forwardHankelSeam ^ (3 : ℝ) +
          GaloisForLFunctions.HTGeometry.schattenNorm 3 D.adjointHankelSeam ^ (3 : ℝ) := by
  intro H _ _ _ D
  exact ⟨D.hankelSeams_memSchattenClass_three.1,
    D.hankelSeams_memSchattenClass_three.2,
    D.traceNorm_cubicDefect_eq_hankelSchattenMass⟩

end RHTower
