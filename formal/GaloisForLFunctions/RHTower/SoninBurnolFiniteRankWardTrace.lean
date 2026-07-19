import GaloisForLFunctions.HTGeometry.FiniteRankCutoffWardTrace
import GaloisForLFunctions.RHTower.SoninBurnolPointedWardTrace

/-!
# Finite-rank source packets on the Burnol conductor edge

Every finite-rank packet inherits the pointed Burnol reflection and Lüders boundary split.  The
result admits arbitrary finite arithmetic source decompositions while retaining a signed value
pairing against a bounded, generally noncompact conductor edge.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- **Finite-packet Burnol Ward reflection.**  Reflection carries every finite-rank source packet
from the position edge to the physical conductor edge. -/
theorem finiteRankCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hMA : ccmCommutator M A = 0) :
    finiteRankCutoffWardTrace (reflectedCutoff A J) M c
        (fun i ↦ J (x i)) (fun i ↦ J (y i)) =
      finiteRankCutoffWardTrace A (burnolConductor M J) c x y := by
  rw [finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    finiteRankCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_reflectedPosition_eq_burnolConductor
      M J A hJ hJAdj hMA]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_conjugate_apply_involution J
    (cutoffWardAdjointCurvature A (burnolConductor M J)) hJ hJAdj]

/-- **Hypothesis-discharged finite-packet Burnol law.**  Lüders pinching supplies the required
position--cutoff commutation for every bounded channel. -/
theorem finiteRankCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
    (M J A : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hA : IsIdempotentElem A) :
    finiteRankCutoffWardTrace (reflectedCutoff A J) (ludersPinching A M) c
        (fun i ↦ J (x i)) (fun i ↦ J (y i)) =
      finiteRankCutoffWardTrace A
        (burnolConductor (ludersPinching A M) J) c x y := by
  exact finiteRankCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (ludersPinching A M) J A c x y hJ hJAdj
      (ccmCommutator_ludersPinching_eq_zero hA M)

/-- **Finite-packet Burnol/Lüders boundary split.**  The original reflected-position value is the
physical conductor value of the canonical cutoff-commuting block plus the exact two-corner
residual. -/
theorem finiteRankCutoffWardTrace_reflectedPosition_ludersBoundarySplit
    (M J A : H →L[ℂ] H) (c : ι → ℂ) (x y : ι → H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (hA : IsIdempotentElem A) :
    finiteRankCutoffWardTrace (reflectedCutoff A J) M c
        (fun i ↦ J (x i)) (fun i ↦ J (y i)) =
      finiteRankCutoffWardTrace A
          (burnolConductor (ludersPinching A M) J) c x y +
        finiteRankCutoffWardTrace (reflectedCutoff A J)
          (crossBoundary A M + upperBoundary A M) c
          (fun i ↦ J (x i)) (fun i ↦ J (y i)) := by
  have hsplit := ludersPinching_add_boundaries_eq A M
  nth_rw 1 [← hsplit]
  rw [finiteRankCutoffWardTrace_add_channel,
    finiteRankCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
      M J A c x y hJ hJAdj hA]

/-- Concrete even-Sonin finite-packet reflection after Lüders pinching. -/
theorem finiteRankCutoffWardTrace_evenFourierLudersPosition_eq_burnolConductor
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace)
    (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardTrace (evenFourierCutoff a)
        (ludersPinching (evenIndicatorCutoff a) M) c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) =
      finiteRankCutoffWardTrace (evenIndicatorCutoff a)
        (burnolConductor (ludersPinching (evenIndicatorCutoff a) M)
          evenFourierTransform) c x y := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact finiteRankCutoffWardTrace_reflectedLudersPosition_eq_burnolConductor
    M evenFourierTransform (evenIndicatorCutoff a) c x y
      evenFourierTransform_mul_self adjoint_evenFourierTransform
      (evenIndicatorCutoff_idempotent a)

/-- Concrete hypothesis-free even-Sonin split for an arbitrary finite-rank source packet. -/
theorem finiteRankCutoffWardTrace_evenFourierPosition_ludersBoundarySplit
    (a : ℝ) (M : evenSubspace →L[ℂ] evenSubspace)
    (c : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardTrace (evenFourierCutoff a) M c
        (fun i ↦ evenFourierTransform (x i))
        (fun i ↦ evenFourierTransform (y i)) =
      finiteRankCutoffWardTrace (evenIndicatorCutoff a)
          (burnolConductor (ludersPinching (evenIndicatorCutoff a) M)
            evenFourierTransform) c x y +
        finiteRankCutoffWardTrace (evenFourierCutoff a)
          (crossBoundary (evenIndicatorCutoff a) M +
            upperBoundary (evenIndicatorCutoff a) M) c
          (fun i ↦ evenFourierTransform (x i))
          (fun i ↦ evenFourierTransform (y i)) := by
  rw [evenFourierCutoff_eq_reflectedCutoff]
  exact finiteRankCutoffWardTrace_reflectedPosition_ludersBoundarySplit
    M evenFourierTransform (evenIndicatorCutoff a) c x y
      evenFourierTransform_mul_self adjoint_evenFourierTransform
      (evenIndicatorCutoff_idempotent a)

end RHTower
