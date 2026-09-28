import GaloisForLFunctions.RHTower.RouteRExternalTensorMonodromy
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SquareZeroMonodromy

/-!
# Critical-line chains for square-zero wall monodromy

At centered grade `a(ρ) = Re ρ - 1/2` the critical-wall monodromy is the identity exactly on the
critical line, and the group-like and primitive external formations agree exactly there.  The
external tensor square of a vector over a field vanishes exactly when the vector does.
-/

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.DerivedSelection

namespace RHTower

noncomputable section

/-- **(ETP.1)** `v ⊗ v = 0 ↔ v = 0` over a field. -/
theorem self_tmul_eq_zero_iff {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (v : V) :
    v ⊗ₜ[k] v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact self_tmul_ne_zero_of_ne_zero hv h
  · rintro rfl
    simp

/-- The functional-equation leg is the unit inverse of the wall monodromy. -/
theorem routeRNilpotentMonodromyUnit_inv (t : ℝ) :
    ((routeRNilpotentMonodromyUnit t)⁻¹ : RouteRSummableHadamardCoronaˣ).val =
      routeRNilpotentMonodromyInv t := rfl

/-- The wall monodromy is the square-zero unit `1 + h` of the abstract law. -/
theorem routeRNilpotentMonodromy_squareZero (t : ℝ) :
    (routeRNilpotentMonodromyWallClass t) ^ 2 = 0 :=
  routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero t

/-- **(NIMM.9)** Identity wall monodromy at the centered grade of `ρ` is the critical line. -/
theorem routeRNilpotentMonodromy_eq_one_iff_re (ρ : ℂ) :
    routeRNilpotentMonodromy (ρ.re - 1 / 2) = 1 ↔ ρ.re = 1 / 2 := by
  rw [routeRNilpotentMonodromy_eq_one_iff, sub_eq_zero]

/-- **(NIMM.9)** The wall tangent at the centered grade of `ρ` vanishes exactly on the critical
line. -/
theorem routeRNilpotentMonodromyWallClass_eq_zero_iff_re (ρ : ℂ) :
    routeRNilpotentMonodromyWallClass (ρ.re - 1 / 2) = 0 ↔ ρ.re = 1 / 2 := by
  rw [routeRNilpotentMonodromyWallClass_eq_zero_iff, sub_eq_zero]

/-- **(ETP.8)** Group-like and primitive external formations agree at the centered grade of `ρ`
exactly on the critical line. -/
theorem routeRExternalGroupLikeFormation_eq_primitive_iff_re (ρ : ℂ) :
    routeRExternalGroupLikeFormation (ρ.re - 1 / 2) =
        routeRExternalPrimitiveFormation (ρ.re - 1 / 2) ↔ ρ.re = 1 / 2 := by
  rw [routeRExternalGroupLikeFormation_eq_primitive_iff, sub_eq_zero]

/-- **Corollary 4.3 (ETP.7)** Internal energy is neutral, the group-like/primitive defect is the
external curvature, and that curvature detects the wall exactly. -/
theorem routeRExternal_phaseSeparation (t : ℝ) :
    reflEnergy (routeRNilpotentMonodromy t) (routeRNilpotentMonodromyInv t) = 0 ∧
      routeRExternalGroupLikeFormation t - routeRExternalPrimitiveFormation t =
        routeRExternalTensorCurvature t ∧
      (routeRExternalTensorCurvature t = 0 ↔ t = 0) := by
  refine ⟨routeRNilpotentMonodromy_energy_eq_zero t, ?_,
    routeRExternalTensorCurvature_eq_zero_iff t⟩
  rw [routeRExternalGroupLikeFormation_eq_primitive_add_curvature, add_sub_cancel_left]

end

end RHTower
