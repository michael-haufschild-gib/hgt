import GaloisForLFunctions.HTGeometry.TwoProjectionHilbertSchmidtEnergy
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm

/-!
# Cubic trace law for a Hilbert--Schmidt pair of projections

This module isolates the operator-theoretic core of the restricted-unitary construction.  A
Hilbert--Schmidt difference of two orthogonal projections has a self-adjoint Schatten-one cube.
The cube splits into the two oriented positive seam energies, and its real trace is their exact
Hilbert--Schmidt energy difference.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference of two orthogonal polarizations. -/
def restrictedProjectionDisplacement (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R - P

/-- First odd nuclear polynomial at the Hilbert--Schmidt boundary. -/
def restrictedProjectionCubicDefect (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  restrictedProjectionDisplacement R P ^ 3

/-- Positive channel in which `R` exits the `P` polarization. -/
def restrictedProjectionPositiveChannel (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R * (1 - P) * R

/-- A difference of self-adjoint polarizations is self-adjoint. -/
theorem adjoint_restrictedProjectionDisplacement
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionDisplacement R P) =
      restrictedProjectionDisplacement R P := by
  rw [restrictedProjectionDisplacement, ContinuousLinearMap.adjoint.map_sub, hR, hP]

/-- Two Hilbert--Schmidt factors make the square nuclear; the ideal law then makes the cubic
nuclear without strengthening the displacement to Schatten one. -/
theorem restrictedProjectionCubicDefect_memSchattenClass_one
    (R P : H →L[ℂ] H)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    MemSchattenClass 1 (restrictedProjectionCubicDefect R P) := by
  have hsqRect :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hDelta hDelta
  have hsq : MemSchattenClass 1
      ((restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P) :=
    (memRectSchattenClass_iff_memSchattenClass
      1 (restrictedProjectionDisplacement R P ∘L
        restrictedProjectionDisplacement R P)).mp hsqRect
  have hcube := memSchattenClass_one_comp_right hsq
    (restrictedProjectionDisplacement R P)
  simpa [restrictedProjectionCubicDefect, pow_succ, ContinuousLinearMap.mul_def] using hcube

/-- Cubing preserves self-adjointness of the projection displacement. -/
theorem adjoint_restrictedProjectionCubicDefect
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect R P) =
      restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, show (restrictedProjectionDisplacement R P) ^ 3 =
      ((restrictedProjectionDisplacement R P) ∘L
          restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P by
      simp [pow_succ, ContinuousLinearMap.mul_def]]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictedProjectionDisplacement R P hR hP]
  ext x
  rfl

omit [CompleteSpace H] in
/-- Exact positive-channel decomposition `(R-P)^3 = R(1-P)R - P(1-R)P`. -/
theorem restrictedProjectionCubicDefect_eq_channels
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hP : IsIdempotentElem P) :
    restrictedProjectionCubicDefect R P =
      restrictedProjectionPositiveChannel R P -
        restrictedProjectionPositiveChannel P R := by
  change (R - P) ^ 3 = R * (1 - P) * R - P * (1 - R) * P
  have hRR : R * R = R := hR
  have hPP : P * P = P := hP
  noncomm_ring [hRR, hPP]

/-- Exit seam from the `R` polarization into the complement of `P`. -/
def restrictedProjectionForwardSeam (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - P) * R

/-- Exit seam from the `P` polarization into the complement of `R`. -/
def restrictedProjectionBackwardSeam (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - R) * P

omit [CompleteSpace H] in
/-- The forward seam factors through the Hilbert--Schmidt displacement. -/
theorem restrictedProjectionForwardSeam_eq_comp_displacement
    (R P : H →L[ℂ] H) (hP : IsIdempotentElem P) :
    restrictedProjectionForwardSeam R P =
      (1 - P) * restrictedProjectionDisplacement R P := by
  rw [restrictedProjectionForwardSeam, restrictedProjectionDisplacement]
  have hPP : P * P = P := hP
  noncomm_ring [hPP]

omit [CompleteSpace H] in
/-- The backward seam factors through the oppositely oriented displacement. -/
theorem restrictedProjectionBackwardSeam_eq_comp_neg_displacement
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) :
    restrictedProjectionBackwardSeam R P =
      (1 - R) * (-restrictedProjectionDisplacement R P) := by
  rw [restrictedProjectionBackwardSeam, restrictedProjectionDisplacement]
  have hRR : R * R = R := hR
  noncomm_ring [hRR]

/-- The forward seam is Hilbert--Schmidt at exactly the displacement `S₂` boundary. -/
theorem restrictedProjectionForwardSeam_isHilbertSchmidt
    (R P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    (restrictedProjectionForwardSeam R P).IsHilbertSchmidt := by
  rw [restrictedProjectionForwardSeam_eq_comp_displacement R P hP]
  exact hDelta.comp_left (1 - P)

/-- The backward seam is Hilbert--Schmidt at exactly the displacement `S₂` boundary. -/
theorem restrictedProjectionBackwardSeam_isHilbertSchmidt
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    (restrictedProjectionBackwardSeam R P).IsHilbertSchmidt := by
  rw [restrictedProjectionBackwardSeam_eq_comp_neg_displacement R P hR]
  exact hDelta.neg.comp_left (1 - R)

/-- Adjoint of the forward seam for orthogonal polarizations. -/
theorem adjoint_restrictedProjectionForwardSeam
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionForwardSeam R P) =
      R * (1 - P) := by
  rw [restrictedProjectionForwardSeam]
  change ContinuousLinearMap.adjoint ((1 - P) ∘L R) = R ∘L (1 - P)
  rw [ContinuousLinearMap.adjoint_comp, hR,
    ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one, hP]

/-- Adjoint of the backward seam for orthogonal polarizations. -/
theorem adjoint_restrictedProjectionBackwardSeam
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionBackwardSeam R P) =
      P * (1 - R) := by
  rw [restrictedProjectionBackwardSeam]
  change ContinuousLinearMap.adjoint ((1 - R) ∘L P) = P ∘L (1 - R)
  rw [ContinuousLinearMap.adjoint_comp, hP,
    ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one, hR]

/-- The positive `R → (1-P)` cubic channel is the forward seam energy. -/
theorem restrictedProjectionPositiveChannel_eq_forwardSeamEnergy
    (R P : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hRAdj : ContinuousLinearMap.adjoint R = R)
    (hPAdj : ContinuousLinearMap.adjoint P = P) :
    restrictedProjectionPositiveChannel R P =
      ContinuousLinearMap.adjoint (restrictedProjectionForwardSeam R P) *
        restrictedProjectionForwardSeam R P := by
  rw [restrictedProjectionPositiveChannel,
    adjoint_restrictedProjectionForwardSeam R P hRAdj hPAdj,
    restrictedProjectionForwardSeam]
  have hPP : P * P = P := hP
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hPP]
  symm
  calc
    (R * (1 - P)) * ((1 - P) * R) =
        R * ((1 - P) * (1 - P)) * R := by simp only [mul_assoc]
    _ = R * (1 - P) * R := by rw [hcomp]

/-- The positive `P → (1-R)` cubic channel is the backward seam energy. -/
theorem restrictedProjectionPositiveChannel_eq_backwardSeamEnergy
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hRAdj : ContinuousLinearMap.adjoint R = R)
    (hPAdj : ContinuousLinearMap.adjoint P = P) :
    restrictedProjectionPositiveChannel P R =
      ContinuousLinearMap.adjoint (restrictedProjectionBackwardSeam R P) *
        restrictedProjectionBackwardSeam R P := by
  rw [restrictedProjectionPositiveChannel,
    adjoint_restrictedProjectionBackwardSeam R P hRAdj hPAdj,
    restrictedProjectionBackwardSeam]
  have hRR : R * R = R := hR
  have hcomp : (1 - R) * (1 - R) = 1 - R := by
    noncomm_ring [hRR]
  symm
  calc
    (P * (1 - R)) * ((1 - R) * P) =
        P * ((1 - R) * (1 - R)) * P := by simp only [mul_assoc]
    _ = P * (1 - R) * P := by rw [hcomp]

/-- Each oriented positive channel is Schatten one because it is a Hilbert--Schmidt seam
energy. -/
theorem restrictedProjectionPositiveChannel_memSchattenClass_one
    (R P : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hRAdj : ContinuousLinearMap.adjoint R = R)
    (hPAdj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    MemSchattenClass 1 (restrictedProjectionPositiveChannel R P) := by
  let S := restrictedProjectionForwardSeam R P
  have hS : S.IsHilbertSchmidt :=
    restrictedProjectionForwardSeam_isHilbertSchmidt R P hP hDelta
  have hrect := memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    hS hS.adjoint
  have henergy : restrictedProjectionPositiveChannel R P =
      ContinuousLinearMap.adjoint S ∘L S := by
    simpa only [ContinuousLinearMap.mul_def] using
      restrictedProjectionPositiveChannel_eq_forwardSeamEnergy
        R P hP hRAdj hPAdj
  rw [henergy]
  exact (memRectSchattenClass_iff_memSchattenClass
    1 (ContinuousLinearMap.adjoint S ∘L S)).mp hrect

private theorem opTrace_sub_seamEnergy
    (S T : H →L[ℂ] H) (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) :
    opTrace (ContinuousLinearMap.adjoint S ∘L S -
        ContinuousLinearMap.adjoint T ∘L T) =
      opTrace (ContinuousLinearMap.adjoint S ∘L S) -
        opTrace (ContinuousLinearMap.adjoint T ∘L T) := by
  have hsS := summable_inner_diag_comp hS.adjoint hS (hsBasis ℂ H)
  have hsT := summable_inner_diag_comp hT.adjoint hT (hsBasis ℂ H)
  unfold opTrace
  calc
    (∑' i, inner ℂ (hsBasis ℂ H i)
        ((ContinuousLinearMap.adjoint S ∘L S -
          ContinuousLinearMap.adjoint T ∘L T) (hsBasis ℂ H i))) =
        ∑' i, (inner ℂ (hsBasis ℂ H i)
          ((ContinuousLinearMap.adjoint S ∘L S) (hsBasis ℂ H i)) -
          inner ℂ (hsBasis ℂ H i)
            ((ContinuousLinearMap.adjoint T ∘L T) (hsBasis ℂ H i))) := by
      apply tsum_congr
      intro i
      rw [sub_apply, inner_sub_right]
    _ = _ := hsS.tsum_sub hsT

/-- **Signed two-channel cubic trace.**  The real trace of the cubic projection defect is the
forward Hilbert--Schmidt seam energy minus the backward seam energy. -/
theorem re_opTrace_restrictedProjectionCubicDefect_eq_seamEnergies
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRAdj : ContinuousLinearMap.adjoint R = R)
    (hPAdj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    (opTrace (restrictedProjectionCubicDefect R P)).re =
      hsNormSq (restrictedProjectionForwardSeam R P) -
        hsNormSq (restrictedProjectionBackwardSeam R P) := by
  let S := restrictedProjectionForwardSeam R P
  let T := restrictedProjectionBackwardSeam R P
  have hS : S.IsHilbertSchmidt :=
    restrictedProjectionForwardSeam_isHilbertSchmidt R P hP hDelta
  have hT : T.IsHilbertSchmidt :=
    restrictedProjectionBackwardSeam_isHilbertSchmidt R P hR hDelta
  rw [restrictedProjectionCubicDefect_eq_channels R P hR hP,
    restrictedProjectionPositiveChannel_eq_forwardSeamEnergy
      R P hP hRAdj hPAdj,
    restrictedProjectionPositiveChannel_eq_backwardSeamEnergy
      R P hR hRAdj hPAdj,
    ContinuousLinearMap.mul_def]
  change (opTrace (ContinuousLinearMap.adjoint S ∘L S -
      ContinuousLinearMap.adjoint T ∘L T)).re = hsNormSq S - hsNormSq T
  rw [opTrace_sub_seamEnergy S T hS hT]
  change RCLike.re (opTrace (ContinuousLinearMap.adjoint S ∘L S)) -
      RCLike.re (opTrace (ContinuousLinearMap.adjoint T ∘L T)) =
    hsNormSq S - hsNormSq T
  rw [re_opTrace_adjoint_comp_self hS, re_opTrace_adjoint_comp_self hT]

omit [CompleteSpace H] in
/-- Orientation reversal negates the cubic defect exactly. -/
theorem restrictedProjectionCubicDefect_swap
    (R P : H →L[ℂ] H) :
    restrictedProjectionCubicDefect P R = -restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, restrictedProjectionCubicDefect,
    restrictedProjectionDisplacement, restrictedProjectionDisplacement]
  noncomm_ring

end RHTower
