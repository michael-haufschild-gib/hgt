import GaloisForLFunctions.HTGeometry.BoundedDegreeOperationalHorizonCertificate
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Finite-depth operational-horizon law

Consider a finite interferometric response written as a sum over paths.  A
depth-`m` path contains `m` affine factors in one tunable coupling.  Every
path amplitude and their arbitrary finite weighted sum have polynomial
degree at most `m`.

Consequently any `m + 1` distinct coupling settings decide whether the
complete response is identically zero.  If a nonzero response vanishes at
the disconnected setting, its first unlocking order lies in `{1, ..., m}`.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Polynomial amplitude of one depth-`m` path with affine coupling at each
step. -/
noncomputable def affinePathResponse
    {m : ℕ} (constant coupling : Fin m → ℂ) : Polynomial ℂ :=
  ∏ i, (Polynomial.C (constant i) +
    Polynomial.X * Polynomial.C (coupling i))

/-- Finite weighted sum of depth-`m` affine path amplitudes. -/
noncomputable def finiteDepthAffineResponse
    {m : ℕ} {Path : Type*} [Fintype Path]
    (weight : Path → ℂ)
    (constant coupling : Path → Fin m → ℂ) : Polynomial ℂ :=
  ∑ path, Polynomial.C (weight path) *
    affinePathResponse (constant path) (coupling path)

/-- One affine response factor has polynomial degree at most one. -/
theorem natDegree_affineFactor_le_one (a b : ℂ) :
    (Polynomial.C a + Polynomial.X * Polynomial.C b).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · calc
      (Polynomial.X * Polynomial.C b).natDegree ≤
          Polynomial.X.natDegree + (Polynomial.C b).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by simp

/-- A depth-`m` affine path response has degree at most `m`. -/
theorem natDegree_affinePathResponse_le
    {m : ℕ} (constant coupling : Fin m → ℂ) :
    (affinePathResponse constant coupling).natDegree ≤ m := by
  unfold affinePathResponse
  calc
    (∏ i, (Polynomial.C (constant i) +
        Polynomial.X * Polynomial.C (coupling i))).natDegree ≤
        ∑ i, (Polynomial.C (constant i) +
          Polynomial.X * Polynomial.C (coupling i)).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ _i : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact natDegree_affineFactor_le_one _ _
    _ = m := by simp

/-- Finite interference among depth-`m` paths does not increase the coupling
degree beyond `m`. -/
theorem natDegree_finiteDepthAffineResponse_le
    {m : ℕ} {Path : Type*} [Fintype Path]
    (weight : Path → ℂ)
    (constant coupling : Path → Fin m → ℂ) :
    (finiteDepthAffineResponse weight constant coupling).natDegree ≤ m := by
  unfold finiteDepthAffineResponse
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro path hpath
  calc
    (Polynomial.C (weight path) *
        affinePathResponse (constant path) (coupling path)).natDegree ≤
      (Polynomial.C (weight path)).natDegree +
        (affinePathResponse (constant path) (coupling path)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ m := by
      have hpathDegree :=
        natDegree_affinePathResponse_le
          (constant path) (coupling path)
      simpa using hpathDegree

/-- **Finite-depth operational-horizon certificate.** For an arbitrary
finite family of depth-`m` affine paths, `m + 1` distinct coupling samples
decide whether their total response is identically zero.  Every nonzero
response that vanishes at disconnection unlocks by order `m`. -/
theorem finiteDepthAffineResponse_horizonCertificate
    {m : ℕ} {Path : Type*} [Fintype Path]
    (weight : Path → ℂ)
    (constant coupling : Path → Fin m → ℂ)
    (sample : Fin (m + 1) → ℂ)
    (hsample : Function.Injective sample) :
    let response :=
      finiteDepthAffineResponse weight constant coupling
    (response = 0 ↔ ∀ i, response.eval (sample i) = 0) ∧
    (response ≠ 0 → response.eval 0 = 0 →
      ∃ b : ℕ, 0 < b ∧ b ≤ m) := by
  dsimp
  exact boundedDegreeOperationalHorizon_finiteCertificate
    (finiteDepthAffineResponse weight constant coupling)
    sample hsample
    (natDegree_finiteDepthAffineResponse_le
      weight constant coupling)

end GaloisForLFunctions.HTGeometry
