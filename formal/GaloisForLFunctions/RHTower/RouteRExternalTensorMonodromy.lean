import GaloisForLFunctions.RHTower.RouteRNilpotentMonodromy
import Mathlib.LinearAlgebra.Dual.Lemmas

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.DerivedSelection

namespace RHTower

noncomputable section

/-- A nonzero vector over a field has nonzero external tensor square. -/
theorem self_tmul_ne_zero_of_ne_zero
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {v : V} (hv : v ≠ 0) : v ⊗ₜ[k] v ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv
  intro hzero
  have hmap := congrArg (TensorProduct.map f f) hzero
  rw [TensorProduct.map_tmul, hf, map_zero] at hmap
  have hunit := congrArg (TensorProduct.lid k k) hmap
  rw [TensorProduct.lid_tmul, one_smul, map_zero] at hunit
  exact one_ne_zero hunit

/-- External tensor carrier for the critical-wall square-zero tangent. -/
abbrev RouteRExternalMonodromyTensor :=
  TensorProduct ℂ RouteRSummableHadamardCorona RouteRSummableHadamardCorona

/-- Multiplicative/group-like two-leg formation. -/
def routeRExternalGroupLikeFormation (t : ℝ) : RouteRExternalMonodromyTensor :=
  routeRNilpotentMonodromy t ⊗ₜ[ℂ] routeRNilpotentMonodromy t

/-- Primitive first-order two-leg formation. -/
def routeRExternalPrimitiveFormation (t : ℝ) : RouteRExternalMonodromyTensor :=
  (1 : RouteRSummableHadamardCorona) ⊗ₜ[ℂ] 1 +
    routeRNilpotentMonodromyWallClass t ⊗ₜ[ℂ] 1 +
    (1 : RouteRSummableHadamardCorona) ⊗ₜ[ℂ]
      routeRNilpotentMonodromyWallClass t

/-- External tensor curvature discarded by internal multiplication. -/
def routeRExternalTensorCurvature (t : ℝ) : RouteRExternalMonodromyTensor :=
  routeRNilpotentMonodromyWallClass t ⊗ₜ[ℂ]
    routeRNilpotentMonodromyWallClass t

/-- Diagonal multiplication observer from external polarization back to the corona. -/
def routeRExternalDiagonalMultiplication :
    RouteRExternalMonodromyTensor →ₗ[ℂ] RouteRSummableHadamardCorona :=
  TensorProduct.lift (LinearMap.mul ℂ RouteRSummableHadamardCorona)

/-- Multiplicative formation equals primitive formation plus external tensor curvature. -/
theorem routeRExternalGroupLikeFormation_eq_primitive_add_curvature (t : ℝ) :
    routeRExternalGroupLikeFormation t =
      routeRExternalPrimitiveFormation t + routeRExternalTensorCurvature t := by
  simp only [routeRExternalGroupLikeFormation, routeRExternalPrimitiveFormation,
    routeRExternalTensorCurvature, routeRNilpotentMonodromy,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- Diagonal multiplication erases external curvature because the wall tangent is square-zero. -/
theorem routeRExternalDiagonalMultiplication_curvature_eq_zero (t : ℝ) :
    routeRExternalDiagonalMultiplication (routeRExternalTensorCurvature t) = 0 := by
  rw [routeRExternalDiagonalMultiplication, routeRExternalTensorCurvature,
    TensorProduct.lift.tmul]
  simpa [pow_two] using
    routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero t

/-- External tensor curvature vanishes exactly at neutral grade. -/
theorem routeRExternalTensorCurvature_eq_zero_iff (t : ℝ) :
    routeRExternalTensorCurvature t = 0 ↔ t = 0 := by
  constructor
  · intro hzero
    by_contra ht
    exact self_tmul_ne_zero_of_ne_zero
      ((routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t).2 ht) hzero
  · intro ht
    rw [routeRExternalTensorCurvature,
      (routeRNilpotentMonodromyWallClass_eq_zero_iff t).2 ht]
    simp

/-- Multiplicative and primitive formations agree exactly on the wall. -/
theorem routeRExternalGroupLikeFormation_eq_primitive_iff (t : ℝ) :
    routeRExternalGroupLikeFormation t = routeRExternalPrimitiveFormation t ↔ t = 0 := by
  rw [routeRExternalGroupLikeFormation_eq_primitive_add_curvature]
  simpa using routeRExternalTensorCurvature_eq_zero_iff t

/-- Functional-equation reflection fixes external tensor curvature. -/
theorem routeRExternalTensorCurvature_neg (t : ℝ) :
    routeRExternalTensorCurvature (-t) = routeRExternalTensorCurvature t := by
  rw [routeRExternalTensorCurvature, routeRExternalTensorCurvature]
  dsimp only [routeRNilpotentMonodromyWallClass]
  rw [routeRPrimeGammaCriticalWallSummableHadamardClass_neg]
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

/-- External curvature retains cofinal memory in both tensor factors. -/
theorem routeRExternalTensorCurvature_shift_fixed (t : ℝ) :
    routeRSummableHadamardShiftEquiv (routeRNilpotentMonodromyWallClass t) ⊗ₜ[ℂ]
        routeRSummableHadamardShiftEquiv (routeRNilpotentMonodromyWallClass t) =
      routeRExternalTensorCurvature t := by
  rw [routeRPrimeGammaCriticalWallSummableHadamardClass_shift_fixed]
  rfl

/-- Closed internal/external phase-separation law. -/
theorem routeRExternalTensorMonodromy_law :
    ∀ t : ℝ,
      reflEnergy (routeRNilpotentMonodromy t) (routeRNilpotentMonodromyInv t) = 0 ∧
      routeRExternalDiagonalMultiplication (routeRExternalTensorCurvature t) = 0 ∧
      routeRExternalGroupLikeFormation t =
        routeRExternalPrimitiveFormation t + routeRExternalTensorCurvature t ∧
      (routeRExternalTensorCurvature t = 0 ↔ t = 0) ∧
      routeRExternalTensorCurvature (-t) = routeRExternalTensorCurvature t := by
  intro t
  exact ⟨routeRNilpotentMonodromy_energy_eq_zero t,
    routeRExternalDiagonalMultiplication_curvature_eq_zero t,
    routeRExternalGroupLikeFormation_eq_primitive_add_curvature t,
    routeRExternalTensorCurvature_eq_zero_iff t,
    routeRExternalTensorCurvature_neg t⟩

end

end RHTower
