import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers
import GaloisForLFunctions.HTGeometry.PaperConstantVectorFieldTermination
import GaloisForLFunctions.HTGeometry.PaperIntrinsicFiberClocks
import GaloisForLFunctions.HTGeometry.PaperStabilizedPolynomialClock

/-!
# Exact rescaling boundaries for native polynomial clocks

The source top-iterate argument now applies to every constant vector
field, every exact-fibre clock, and both stabilized clock presentations.
A shared multiplier preserves all three intrinsic fibre clocks precisely
when it is scalar. Coordinate multipliers give an exact shear/Euler
boundary, uniformly across every fibre and every pair of coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

local instance nativeMultiplierFiberDomain (t : ℂ) : IsDomain (FiberRing t) :=
  Function.Injective.isDomain (exactFiberEquiv t).toRingHom (exactFiberEquiv t).injective

local instance nativeMultiplierFiberCharZero (t : ℂ) : CharZero (FiberRing t) :=
  ⟨fun m n h => Nat.cast_injective
    (by simpa only [map_natCast] using congrArg (exactFiberEquiv t) h)⟩

/-- Every native constant vector field has the exact invariant-multiplier boundary. -/
theorem paperConstantVectorField_multiplier_iff
    {K ι : Type*} [Field K] [CharZero K] (v : ι → K) (q : MvPolynomial ι K) :
    IsLocallyNilpotent (q • constVectorField v) ↔ constVectorField v q = 0 :=
  paperLND_smul_iff _ (paperConstantVectorField_locallyNilpotent v) q

/-- Exact rescaling criterion for the clock on the actual stabilized source polynomial. -/
theorem paperStabilizedClock_multiplier_iff (q : R 5) :
    IsLocallyNilpotent (q • paperStabilizedClock) ↔ paperStabilizedClock q = 0 :=
  paperLND_smul_iff _ paperStabilizedClock_locallyNilpotent q

/-- The literal polynomial-extension clock has the same exact rescaling criterion. -/
theorem paperPolynomialExtensionClock_multiplier_iff (q : Polynomial (R 4)) :
    IsLocallyNilpotent (q • paperPolynomialExtensionClock) ↔
      paperPolynomialExtensionClock q = 0 :=
  paperLND_smul_iff _ paperPolynomialExtensionClock_locallyNilpotent q

/-- Weighting the stabilized clock by its own distinguished coordinate destroys termination. -/
theorem paperStabilizedClock_own_coordinate_not_locallyNilpotent :
    ¬ IsLocallyNilpotent (stabilize f • paperStabilizedClock) := by
  rw [paperStabilizedClock_multiplier_iff, paperStabilizedClock_slice]
  exact one_ne_zero

/-- Every clock on every exact fibre has the invariant-multiplier criterion. -/
theorem paperIntrinsicFiberClock_multiplier_iff (t : ℂ) (i : Fin 3) (q : FiberRing t) :
    IsLocallyNilpotent (q • paperIntrinsicFiberClock t i) ↔
      paperIntrinsicFiberClock t i q = 0 :=
  paperLND_smul_iff _ (paperIntrinsicFiberClock_locallyNilpotent t i) q

/-- Only scalar common speeds preserve all three intrinsic fibre clocks. -/
theorem paperIntrinsicFiberClock_common_multiplier_iff (t : ℂ) (q : FiberRing t) :
    (∀ i : Fin 3, IsLocallyNilpotent (q • paperIntrinsicFiberClock t i)) ↔
      ∃ c : ℂ, q = algebraMap ℂ (FiberRing t) c := by
  rw [← paperIntrinsicFiberClock_common_kernel t q]
  constructor
  · intro h i
    exact (paperIntrinsicFiberClock_multiplier_iff t i q).mp (h i)
  · intro h i
    exact (paperIntrinsicFiberClock_multiplier_iff t i q).mpr (h i)

/-- Cross-coordinate shears terminate; the same-coordinate Euler rescaling does not. -/
theorem paperIntrinsicFiberClock_coordinate_multiplier_iff (t : ℂ) (i j : Fin 3) :
    IsLocallyNilpotent (paperIntrinsicFiberCoordinate t j • paperIntrinsicFiberClock t i) ↔
      i ≠ j := by
  rw [paperIntrinsicFiberClock_multiplier_iff, paperIntrinsicFiberClock_coordinate]
  by_cases h : i = j
  · simp [h]
  · simp [h]

end

end GaloisForLFunctions.HTGeometry
