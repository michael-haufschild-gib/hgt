import GaloisForLFunctions.RHTower.WeilLogShiftFactorialMajorant
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialRegularization
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# The affine space of factorial-regular perturbation amplitudes

Existence of any regular shift is an affine inverse image of a real sequence
submodule. A native late impulse in the perturbation range forces this affine
subspace to be proper, without assuming independence of different columns.
-/

noncomputable section

open scoped BoundedContinuousFunction

namespace RHTower

/-- Sequences with an eventual majorant of some finite factorial order form a
real submodule; the order and all other majorant parameters may vary. -/
def weilLogShiftFactorialSequenceSubmodule : Submodule ℝ (ℕ → ℝ) where
  carrier := {f | WeilLogShiftHasFactorialMajorant f}
  zero_mem' := weilLogShiftHasFactorialMajorant_zero
  add_mem' := fun hf hg => weilLogShiftHasFactorialMajorant_add hf hg
  smul_mem' := fun c _ hf => weilLogShiftHasFactorialMajorant_mul c hf

/-- The full origin moment sequence is affine in arbitrary linear history errors. -/
def weilLogShiftRecoveryAmplitudeMoment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) : E →ᵃ[ℝ] (ℕ → ℝ) where
  toFun a := weilLogShiftRecoveryMoment 0 (center + T a)
  linear := LinearMap.pi fun n => (weilLogShiftRecoveryMomentCLM 0 n).toLinearMap.comp T
  map_vadd' p v := by
    ext n
    change weilLogShiftRecoveryMoment 0 (center + T (v + p)) n =
      weilLogShiftRecoveryMomentCLM 0 n (T v) +
        weilLogShiftRecoveryMoment 0 (center + T p) n
    have h := weilLogShiftRecoveryMoment_sub_eq 0 n
      (center + T (v + p)) (center + T p)
    have he : (center + T (v + p)) - (center + T p) = T v := by
      rw [map_add]
      abel
    rw [he] at h
    exact (sub_eq_iff_eq_add).mp h

/-- All amplitudes admitting a factorial-regular shift, as a possibly empty
affine subspace. No finite-dimensional assumption is needed for this definition. -/
def weilLogShiftFactorialAmplitudeSpace {E : Type*} [AddCommGroup E] [Module ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) : AffineSubspace ℝ E :=
  weilLogShiftFactorialSequenceSubmodule.toAffineSubspace.comap
    (weilLogShiftRecoveryAmplitudeMoment center T)

/-- One affine subspace captures existence over every real shift and all
factorial-majorant parameters simultaneously. -/
theorem mem_weilLogShiftFactorialAmplitudeSpace {E : Type*}
    [AddCommGroup E] [Module ℝ E] (center : ℕ →ᵇ ℝ)
    (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) (a : E) :
    a ∈ weilLogShiftFactorialAmplitudeSpace center T ↔
      ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y (center + T a)) := by
  change WeilLogShiftHasFactorialMajorant
    (weilLogShiftRecoveryMoment 0 (center + T a)) ↔ _
  exact (weilLogShiftHasFactorialMajorant_some_shift_iff_origin (center + T a)).symm

/-- Whenever a regular amplitude exists, all regular amplitudes are exactly
its translate by the direction submodule. This does not assert existence. -/
theorem weilLogShiftFactorialAmplitudeSpace_eq_mk' {E : Type*}
    [AddCommGroup E] [Module ℝ E] (center : ℕ →ᵇ ℝ)
    (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) (a : E)
    (ha : ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment y (center + T a))) :
    weilLogShiftFactorialAmplitudeSpace center T =
      AffineSubspace.mk' a (weilLogShiftFactorialAmplitudeSpace center T).direction := by
  exact (AffineSubspace.mk'_eq
    ((mem_weilLogShiftFactorialAmplitudeSpace center T a).mpr ha)).symm

/-- A common native threshold forces properness for every linear perturbation
map whose range contains one late unit impulse, in any real amplitude module. -/
theorem exists_weilLogShiftFactorialAmplitudeSpace_ne_top :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (E : Type*) [AddCommGroup E] [Module ℝ E]
      (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) (k : ℕ), K ≤ k →
      (∃ v : E, T v = weilLogShiftRecoveryUnitHistory k) →
      weilLogShiftFactorialAmplitudeSpace center T ≠ ⊤ := by
  obtain ⟨K, hK, hno⟩ := exists_weilLogShiftRecoveryMomentResponse_no_factorial_majorant
  refine ⟨K, hK, ?_⟩
  intro E _ _ center T k hk hdir htop
  obtain ⟨v, hv⟩ := hdir
  have hzero : WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment 0 (center + T (0 : E))) := by
    change (0 : E) ∈ weilLogShiftFactorialAmplitudeSpace center T
    rw [htop]
    exact AffineSubspace.mem_top _ _ _
  have hvreg : WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment 0 (center + T v)) := by
    change v ∈ weilLogShiftFactorialAmplitudeSpace center T
    rw [htop]
    exact AffineSubspace.mem_top _ _ _
  have heq (n : ℕ) :
      weilLogShiftRecoveryMoment 0 (center + T v) n -
        weilLogShiftRecoveryMoment 0 (center + T (0 : E)) n =
      weilLogShiftRecoveryMomentResponse 0 n k := by
    calc
      _ = weilLogShiftRecoveryMomentCLM 0 n ((center + T v) - (center + T (0 : E))) :=
        weilLogShiftRecoveryMoment_sub_eq 0 n (center + T v) (center + T (0 : E))
      _ = weilLogShiftRecoveryMomentResponse 0 n k := by
        rw [map_zero, add_zero, add_sub_cancel_left, hv]
        rfl
  have hreg : WeilLogShiftHasFactorialMajorant
      (fun n => weilLogShiftRecoveryMomentResponse 0 n k) := by
    simpa only [heq] using weilLogShiftHasFactorialMajorant_sub hvreg hzero
  obtain ⟨m, A, D, N, hN⟩ := hreg
  exact hno k hk 0 m A D ⟨N, hN⟩

end RHTower
