import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Factoring a functional through the range of a linear map

A functional vanishing on the kernel of a linear map factors through its range: choosing a
preimage of each element of the range is well defined modulo the kernel, so the resulting map is
linear.  If the functional is dominated by a constant times the norm of the image, the factored
functional is bounded by the same constant.

* `GaloisForLFunctions.HTGeometry.factorRange`;
* `GaloisForLFunctions.HTGeometry.factorRange_apply_of_eq`;
* `GaloisForLFunctions.HTGeometry.factorRangeCLM`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [SeminormedAddCommGroup N] [NormedSpace ℝ N]

/-- A chosen preimage of an element of the range. -/
def rangePreim (T : M →ₗ[ℝ] N) (v : LinearMap.range T) : M :=
  Classical.choose (LinearMap.mem_range.mp v.2)

theorem rangePreim_spec (T : M →ₗ[ℝ] N) (v : LinearMap.range T) :
    T (rangePreim T v) = (v : N) :=
  Classical.choose_spec (LinearMap.mem_range.mp v.2)

/-- **A functional killing the kernel factors through the range.** -/
def factorRange (T : M →ₗ[ℝ] N) (f : M →ₗ[ℝ] ℝ) (hker : ∀ x : M, T x = 0 → f x = 0) :
    (LinearMap.range T) →ₗ[ℝ] ℝ where
  toFun := fun v => f (rangePreim T v)
  map_add' := fun v w => by
    have h : T (rangePreim T (v + w) - (rangePreim T v + rangePreim T w)) = 0 := by
      rw [map_sub, map_add, rangePreim_spec, rangePreim_spec, rangePreim_spec]
      simp
    have h2 := hker _ h
    rw [map_sub, map_add] at h2
    linarith
  map_smul' := fun c v => by
    have h : T (rangePreim T (c • v) - c • rangePreim T v) = 0 := by
      rw [map_sub, map_smul, rangePreim_spec, rangePreim_spec]
      simp
    have h2 := hker _ h
    rw [map_sub, map_smul, smul_eq_mul] at h2
    simp only [RingHom.id_apply, smul_eq_mul]
    linarith

theorem factorRange_apply_of_eq (T : M →ₗ[ℝ] N) (f : M →ₗ[ℝ] ℝ)
    (hker : ∀ x : M, T x = 0 → f x = 0) {x : M} {v : LinearMap.range T} (hx : T x = (v : N)) :
    factorRange T f hker v = f x := by
  have h : T (rangePreim T v - x) = 0 := by
    rw [map_sub, rangePreim_spec, hx, sub_self]
  have h2 := hker _ h
  rw [map_sub] at h2
  show f (rangePreim T v) = f x
  linarith

/-- The factored functional, as a continuous functional on the range. -/
def factorRangeCLM (T : M →ₗ[ℝ] N) (f : M →ₗ[ℝ] ℝ) (hker : ∀ x : M, T x = 0 → f x = 0)
    (C : ℝ) (hbd : ∀ x : M, |f x| ≤ C * ‖T x‖) : (LinearMap.range T) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (factorRange T f hker) C fun v => by
    have h := hbd (rangePreim T v)
    rw [rangePreim_spec] at h
    exact le_trans (le_of_eq (Real.norm_eq_abs _)) h

theorem factorRangeCLM_apply_of_eq (T : M →ₗ[ℝ] N) (f : M →ₗ[ℝ] ℝ)
    (hker : ∀ x : M, T x = 0 → f x = 0) (C : ℝ) (hbd : ∀ x : M, |f x| ≤ C * ‖T x‖)
    {x : M} {v : LinearMap.range T} (hx : T x = (v : N)) :
    factorRangeCLM T f hker C hbd v = f x := by
  show factorRange T f hker v = f x
  exact factorRange_apply_of_eq T f hker hx

end GaloisForLFunctions.HTGeometry
