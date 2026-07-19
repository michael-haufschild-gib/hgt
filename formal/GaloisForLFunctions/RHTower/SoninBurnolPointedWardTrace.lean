import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninLudersPinching

/-!
# Signed pointed Fisher values on the Burnol conductor edge

The Burnol conductor cutoff edge is bounded but generally noncompact.  The finite-rank pointed
Fisher connection supplies a canonical signed trace pairing without asking that edge to be
Hilbert--Schmidt.  Reflection transports the pairing between physical and Fourier cutoffs.
Lüders pinching then removes the position--cutoff commutation premise from the reflected-position
form of the law.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Burnol cancellation persists after one more cutoff commutator: the reflected position
curvature is the involutive reflection of the physical conductor curvature. -/
theorem cutoffWardCurvature_reflectedPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (hJ : J * J = 1)
    (hMA : ccmCommutator M A = 0) :
    cutoffWardCurvature (reflectedCutoff A J) M =
      J * cutoffWardCurvature A (burnolConductor M J) * J := by
  have hedge := ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge
    M J A hJ hMA
  have hedge' :
      cutoffCommutator (reflectedCutoff A J) M =
        J * cutoffCommutator A (burnolConductor M J) * J := by
    simpa only [cutoffCommutator, ccmCommutator,
      ContinuousLinearMap.mul_def] using hedge
  rw [cutoffWardCurvature, hedge', reflectedCutoff]
  exact cutoffCommutator_conjugate_involution J A
    (cutoffCommutator A (burnolConductor M J)) hJ

/-- Burnol cancellation for the unconditional adjoint curvature.  No self-adjointness premise on
the cutoff is needed. -/
theorem cutoffWardAdjointCurvature_reflectedPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (hJ : J * J = 1)
    (hJAdj : adjoint J = J) (hMA : ccmCommutator M A = 0) :
    cutoffWardAdjointCurvature (reflectedCutoff A J) M =
      J * cutoffWardAdjointCurvature A (burnolConductor M J) * J := by
  have hedge := ccmCommutator_reflectedCutoff_eq_reflectedConductorEdge
    M J A hJ hMA
  have hedge' :
      cutoffCommutator (reflectedCutoff A J) M =
        J * cutoffCommutator A (burnolConductor M J) * J := by
    simpa only [cutoffCommutator, ccmCommutator,
      ContinuousLinearMap.mul_def] using hedge
  have hAdjRef : adjoint (reflectedCutoff A J) =
      J * adjoint A * J := by
    rw [reflectedCutoff]
    exact adjoint_conjugate_selfAdjoint_outer J A hJAdj
  rw [cutoffWardAdjointCurvature, hedge', hAdjRef]
  exact cutoffCommutator_conjugate_involution J (adjoint A)
    (cutoffCommutator A (burnolConductor M J)) hJ

/-- **Signed Burnol Ward reflection.**  A reflected position edge and the physical conductor edge
have the same pointed Fisher trace value.  No compactness or Hilbert--Schmidt premise is imposed on
either edge. -/
theorem pointedCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (psi chi : H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hMA : ccmCommutator M A = 0) :
    pointedCutoffWardTrace (reflectedCutoff A J) M (J psi) (J chi) =
      pointedCutoffWardTrace A (burnolConductor M J) psi chi := by
  rw [pointedCutoffWardTrace_eq_adjointCurvature_values,
    pointedCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_reflectedPosition_eq_burnolConductor
      M J A hJ hJAdj hMA]
  rw [inner_conjugate_apply_involution J
      (cutoffWardAdjointCurvature A (burnolConductor M J)) hJ hJAdj,
    inner_conjugate_apply_involution J
      (cutoffWardAdjointCurvature A (burnolConductor M J)) hJ hJAdj]

/-- **Hypothesis-free signed Burnol Ward law.**  Replacing an arbitrary bounded position channel
by its canonical Lüders block discharges the position--cutoff commutation premise exactly. -/
theorem pointedCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (psi chi : H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hA : IsIdempotentElem A) :
    pointedCutoffWardTrace (reflectedCutoff A J) (ludersPinching A M)
        (J psi) (J chi) =
      pointedCutoffWardTrace A
        (burnolConductor (ludersPinching A M) J) psi chi := by
  exact pointedCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (ludersPinching A M) J A psi chi hJ hJAdj
      (ccmCommutator_ludersPinching_eq_zero hA M)

/-- **Arbitrary-channel Burnol/Lüders boundary split.**  The signed reflected-position value of
the original channel is the physical conductor value of its cutoff-commuting Lüders block plus
the exact off-cutoff residual.  No commutation premise on the original channel is required. -/
theorem pointedCutoffWardTrace_reflectedPosition_ludersBoundarySplit
    (M J A : H →L[ℂ] H) (psi chi : H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hA : IsIdempotentElem A) :
    pointedCutoffWardTrace (reflectedCutoff A J) M (J psi) (J chi) =
      pointedCutoffWardTrace A
          (burnolConductor (ludersPinching A M) J) psi chi +
      pointedCutoffWardTrace (reflectedCutoff A J)
          (crossBoundary A M + upperBoundary A M) (J psi) (J chi) := by
  have hsplit := ludersPinching_add_boundaries_eq A M
  nth_rw 1 [← hsplit]
  rw [pointedCutoffWardTrace_add,
    pointedCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
      M J A psi chi hJ hJAdj hA]

/-- Concrete even-Sonin specialization.  For every bounded channel, its physical-cutoff Lüders
block has exactly the same signed reflected-position Ward value as its Burnol conductor edge on
the physical cutoff. -/
theorem pointedCutoffWardTrace_evenFourierLudersPosition_eq_burnolConductor
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace) (psi chi : evenSubspace) :
    pointedCutoffWardTrace (evenFourierCutoff a)
        (ludersPinching (evenIndicatorCutoff a) M)
        (evenFourierTransform psi) (evenFourierTransform chi) =
      pointedCutoffWardTrace (evenIndicatorCutoff a)
        (burnolConductor (ludersPinching (evenIndicatorCutoff a) M)
          evenFourierTransform) psi chi := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact pointedCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
    M evenFourierTransform (evenIndicatorCutoff a) psi chi
      evenFourierTransform_mul_self adjoint_evenFourierTransform
      (evenIndicatorCutoff_idempotent a)

/-- Concrete hypothesis-free split for the original even-Sonin channel.  Its Fourier-cutoff Ward
value is a physical Burnol-conductor value plus the two explicit physical-cutoff boundary
corners. -/
theorem pointedCutoffWardTrace_evenFourierPosition_ludersBoundarySplit
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace) (psi chi : evenSubspace) :
    pointedCutoffWardTrace (evenFourierCutoff a) M
        (evenFourierTransform psi) (evenFourierTransform chi) =
      pointedCutoffWardTrace (evenIndicatorCutoff a)
          (burnolConductor (ludersPinching (evenIndicatorCutoff a) M)
            evenFourierTransform) psi chi +
        pointedCutoffWardTrace (evenFourierCutoff a)
          (crossBoundary (evenIndicatorCutoff a) M +
            upperBoundary (evenIndicatorCutoff a) M)
          (evenFourierTransform psi) (evenFourierTransform chi) := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact pointedCutoffWardTrace_reflectedPosition_ludersBoundarySplit
    M evenFourierTransform (evenIndicatorCutoff a) psi chi
      evenFourierTransform_mul_self adjoint_evenFourierTransform
      (evenIndicatorCutoff_idempotent a)

end RHTower
