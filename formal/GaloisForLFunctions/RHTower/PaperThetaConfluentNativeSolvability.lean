import GaloisForLFunctions.RHTower.PaperThetaConfluentNativeChannel

/-!
# Whole-space confluent native resonance solving

Actual iterated theta readings reconstruct the entire original Meyer block
from arbitrary bounded continuous forcing. The resulting bounded projection
has the intrinsic stabilized range as kernel. Every pencil power receives a
bounded solution operator and an exact original-packet defect, retaining all
Xi multiplicities. No packet membership or simplicity premise is required.
-/

noncomputable section
open Complex Set Module
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HTGeometry

def nativeConfluentReconstruction (rho : XiDivisorSupport) :
    (Fin (nativeResonantChannel rho).rank → ℂ) →L[ℂ] NativeContinuousSpace :=
  ((nativeResonantChannel rho).rootSpace.subtype.comp
    (nativeResonantChannel rho).rootCoordinates.symm.toLinearMap).toContinuousLinearMap

def nativeConfluentProjection (rho : XiDivisorSupport) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (nativeConfluentReconstruction rho).comp
    (ContinuousLinearMap.pi (fun j => nativeConfluentMoment rho j.val))

@[simp] theorem nativeConfluentProjection_linear (rho : XiDivisorSupport) :
    (nativeConfluentProjection rho).toLinearMap = (nativeResonantChannel rho).projection := by
  ext g : 1
  change (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm (fun j => nativeConfluentMoment rho j.val g)) =
    (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm ((nativeResonantChannel rho).observations _ g))
  congr 2
  funext j
  exact nativeConfluentMoment_apply rho j.val g

def nativeConfluentComplementInverse (rho : XiDivisorSupport) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  nativeResonantPartialInverse (xiSpectralPointSupport rho) -
    (nativeConfluentMoment rho (nativeResonantChannel rho).rank).smulRight
      (((nativeResonantChannel rho).moment
        ((nativeResonantChannel rho).chain ((nativeResonantChannel rho).rank-1)))⁻¹ •
          nativeResonantVector (xiSpectralPointSupport rho))

@[simp] theorem nativeConfluentComplementInverse_linear (rho : XiDivisorSupport) :
    (nativeConfluentComplementInverse rho).toLinearMap =
      (nativeResonantChannel rho).complementInverse := by
  ext g : 1
  change nativeResonantPartialInverse (xiSpectralPointSupport rho) g -
      nativeConfluentMoment rho _ g • _ =
    (nativeResonantChannel rho).partialInverse g - (nativeResonantChannel rho).row _ g • _
  rw [nativeConfluentMoment_apply]
  rfl

def nativeConfluentPowerDefect (rho : XiDivisorSupport) (n : ℕ) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (nativeConfluentReconstruction rho).comp (ContinuousLinearMap.pi
    (fun j => if j.val<n then nativeConfluentMoment rho j.val else 0))

def nativeConfluentRootPowerLift (rho : XiDivisorSupport) (n : ℕ) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (nativeConfluentReconstruction rho).comp (ContinuousLinearMap.pi
    (fun j => if j.val+n<(nativeResonantChannel rho).rank then
      nativeConfluentMoment rho (j.val+n) else 0))

@[simp] theorem nativeConfluentPowerDefect_linear (rho : XiDivisorSupport) (n : ℕ) :
    (nativeConfluentPowerDefect rho n).toLinearMap = (nativeResonantChannel rho).powerDefect n := by
  ext g : 1
  change (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm _) =
    (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm _)
  congr 2
  funext j
  change (if j.val<n then nativeConfluentMoment rho j.val else 0) g =
    (if j.val<n then (nativeResonantChannel rho).row j.val else 0) g
  split_ifs
  · exact nativeConfluentMoment_apply rho _ g
  · rfl

@[simp] theorem nativeConfluentRootPowerLift_linear (rho : XiDivisorSupport) (n : ℕ) :
    (nativeConfluentRootPowerLift rho n).toLinearMap = (nativeResonantChannel rho).rootPowerLift n := by
  ext g : 1
  change (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm _) =
    (nativeResonantChannel rho).rootSpace.subtype
      ((nativeResonantChannel rho).rootCoordinates.symm _)
  congr 2
  funext j
  change (if j.val+n<(nativeResonantChannel rho).rank then nativeConfluentMoment rho (j.val+n) else 0) g =
    (if j.val+n<(nativeResonantChannel rho).rank then (nativeResonantChannel rho).row (j.val+n) else 0) g
  split_ifs
  · exact nativeConfluentMoment_apply rho _ g
  · rfl

def nativeConfluentPowerSolver (rho : XiDivisorSupport) (n : ℕ) :
    NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (nativeConfluentComplementInverse rho^n).comp (1-nativeConfluentProjection rho)+
    nativeConfluentRootPowerLift rho n

@[simp] theorem nativeConfluentPowerSolver_linear (rho : XiDivisorSupport) (n : ℕ) :
    (nativeConfluentPowerSolver rho n).toLinearMap = (nativeResonantChannel rho).powerSolver n := by
  simp only [nativeConfluentPowerSolver,ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_comp,ContinuousLinearMap.coe_pow,
    nativeConfluentComplementInverse_linear,ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one,nativeConfluentProjection_linear,
    nativeConfluentRootPowerLift_linear,OneChannelParametrix.powerSolver]

theorem nativeConfluentProjection_range (rho : XiDivisorSupport) :
    LinearMap.range (nativeConfluentProjection rho).toLinearMap =
      LinearMap.range (nativeFiniteSynthesis {rho}) := by
  rw [nativeConfluentProjection_linear,(nativeResonantChannel rho).projection_range,
    nativeResonantChannel_root,nativeXiRootBlock_eq_original_packet]

/-- The complement is intrinsic to the original pencil, with its exact
Xi multiplicity. It does not depend on the auxiliary compact counter-source. -/
theorem nativeConfluentProjection_kernel (rho : XiDivisorSupport) :
    LinearMap.ker (nativeConfluentProjection rho).toLinearMap =
      LinearMap.range ((nativePencil (xiSpectralPointSupport rho)).toLinearMap^
        xiSupportMultiplicity rho) := by
  change LinearMap.ker (nativeConfluentProjection rho).toLinearMap =
    LinearMap.range ((nativeResonantChannel rho).pencil^xiSupportMultiplicity rho)
  rw [nativeConfluentProjection_linear,(nativeResonantChannel rho).projection_kernel,
    nativeResonantChannel_rank]

theorem nativeConfluentProjection_idempotent (rho : XiDivisorSupport) (g : NativeContinuousSpace) :
    nativeConfluentProjection rho (nativeConfluentProjection rho g) = nativeConfluentProjection rho g := by
  change (nativeConfluentProjection rho).toLinearMap
    ((nativeConfluentProjection rho).toLinearMap g) = (nativeConfluentProjection rho).toLinearMap g
  simp only [nativeConfluentProjection_linear,(nativeResonantChannel rho).projection_idempotent]

theorem nativeConfluentProjection_pencil (rho : XiDivisorSupport) (g : NativeContinuousSpace) :
    nativeConfluentProjection rho (nativePencil (xiSpectralPointSupport rho) g) =
      nativePencil (xiSpectralPointSupport rho) (nativeConfluentProjection rho g) := by
  change (nativeConfluentProjection rho).toLinearMap ((nativeResonantChannel rho).pencil g) =
    (nativeResonantChannel rho).pencil ((nativeConfluentProjection rho).toLinearMap g)
  rw [nativeConfluentProjection_linear,(nativeResonantChannel rho).projection_pencil]

theorem nativeConfluentPowerSolver_equation (rho : XiDivisorSupport) (n : ℕ)
    (g : NativeContinuousSpace) :
    (nativePencil (xiSpectralPointSupport rho)^n) (nativeConfluentPowerSolver rho n g) =
      g-nativeConfluentPowerDefect rho n g := by
  change ((nativePencil (xiSpectralPointSupport rho)^n).toLinearMap)
    ((nativeConfluentPowerSolver rho n).toLinearMap g) =
      g-(nativeConfluentPowerDefect rho n).toLinearMap g
  rw [ContinuousLinearMap.coe_pow,nativeConfluentPowerSolver_linear,nativeConfluentPowerDefect_linear]
  exact (nativeResonantChannel rho).powerSolver_equation n g

theorem nativeConfluentPowerDefect_exact (rho : XiDivisorSupport) (n : ℕ)
    (g : NativeContinuousSpace) :
    nativeConfluentPowerDefect rho n g=0 ↔
      ∀ j < min n (xiSupportMultiplicity rho), nativeConfluentMoment rho j g=0 := by
  change (nativeConfluentPowerDefect rho n).toLinearMap g=0 ↔ _
  rw [nativeConfluentPowerDefect_linear,(nativeResonantChannel rho).powerDefect_eq_zero_iff,
    nativeResonantChannel_rank]
  simp only [nativeConfluentMoment_apply]

theorem nativeConfluentPowerDefect_original_packet (rho : XiDivisorSupport) (n : ℕ)
    (g : NativeContinuousSpace) :
    nativeConfluentPowerDefect rho n g ∈ LinearMap.range (nativeFiniteSynthesis {rho}) := by
  rw [← nativeXiRootBlock_eq_original_packet,← nativeResonantChannel_root]
  change (nativeConfluentPowerDefect rho n).toLinearMap g ∈ _
  rw [nativeConfluentPowerDefect_linear]
  exact (nativeResonantChannel rho).powerDefect_mem n g

theorem nativeConfluentPowerDefect_idempotent (rho : XiDivisorSupport) (n : ℕ)
    (g : NativeContinuousSpace) :
    nativeConfluentPowerDefect rho n (nativeConfluentPowerDefect rho n g) =
      nativeConfluentPowerDefect rho n g := by
  change (nativeConfluentPowerDefect rho n).toLinearMap
      ((nativeConfluentPowerDefect rho n).toLinearMap g) =
    (nativeConfluentPowerDefect rho n).toLinearMap g
  rw [nativeConfluentPowerDefect_linear]
  exact (nativeResonantChannel rho).powerDefect_idempotent n g

end RHTower.PaperThetaEndpoint
