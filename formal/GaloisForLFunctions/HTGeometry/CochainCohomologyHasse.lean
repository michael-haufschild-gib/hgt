import GaloisForLFunctions.HTGeometry.CochainComplexCohomology
import Mathlib.Algebra.Exact.Basic

/-!
# Hasse classification of cohomology classes

For every cochain complex, cocycles map onto cohomology with kernel the coboundaries.  This file
bundles that projection as a linear map and records exactness, local congruence, and existence with
uniqueness modulo coboundaries.
-/

namespace HTGeometry.DeningerCochainComplex

variable {k : Type*} [CommRing k] {M : ℕ → Type*}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module k (M n)]
variable (C : DeningerCochainComplex k M)

/-- Quotient projection from cocycles to cohomology, bundled as a linear map. -/
def cohomologyProjection (n : ℕ) : C.cocycles n →ₗ[k] C.cohomology n :=
  Submodule.mkQ (C.coboundariesInCocycles n)

/-- The bundled cohomology projection agrees with the existing class constructor. -/
@[simp] theorem cohomologyProjection_apply (n : ℕ) (x : C.cocycles n) :
    cohomologyProjection C n x = C.cohomologyMk x := by
  rfl

/-- Kernel of the cohomology projection is exactly the coboundary submodule inside cocycles. -/
theorem cohomologyProjection_ker (n : ℕ) :
    LinearMap.ker (cohomologyProjection C n) = C.coboundariesInCocycles n := by
  ext x
  change C.cohomologyMk x = 0 ↔ (x : M n) ∈ C.coboundaries n
  exact C.cohomologyMk_eq_zero_iff x

/-- Coboundaries, cocycles, and cohomology form an exact sequence in every degree. -/
theorem cohomologyProjection_exact (n : ℕ) : Function.Exact
    (C.coboundariesInCocycles n).subtype (cohomologyProjection C n) := by
  rw [LinearMap.exact_iff, cohomologyProjection_ker]
  ext x
  simp

/-- Two cocycles determine the same cohomology class exactly when their difference is a
coboundary. -/
theorem cohomologyMk_congr_hasse_iff {n : ℕ} (x y : C.cocycles n) :
    ((x - y : C.cocycles n) : M n) ∈ C.coboundaries n ↔
      C.cohomologyMk x = C.cohomologyMk y := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    change C.cohomologyMk (x - y) = 0
    exact (C.cohomologyMk_eq_zero_iff (x - y)).mpr h
  · intro h
    apply (C.cohomologyMk_eq_zero_iff (x - y)).mp
    change C.cohomologyMk x - C.cohomologyMk y = 0
    exact sub_eq_zero.mpr h

/-- Every cohomology class has a cocycle representative, unique modulo coboundaries. -/
theorem cohomology_exists_unique_mod_coboundary (n : ℕ) (z : C.cohomology n) :
    ∃ x : C.cocycles n,
      C.cohomologyMk x = z ∧
      ∀ y : C.cocycles n,
        C.cohomologyMk y = z ↔
          ((y - x : C.cocycles n) : M n) ∈ C.coboundaries n := by
  obtain ⟨x, hx⟩ := C.cohomologyMk_surjective n z
  refine ⟨x, hx, fun y => ?_⟩
  simpa only [hx] using (cohomologyMk_congr_hasse_iff C y x).symm

end HTGeometry.DeningerCochainComplex
