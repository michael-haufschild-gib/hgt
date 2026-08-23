import GaloisForLFunctions.HTGeometry.SymmetricMultilinearPolarization

/-!
# Diagonal Hasse principle for symmetric continuous multilinear forms

Symmetry is encoded in a submodule.  The diagonal restriction is then a faithful linear
observable, and the all-orders polarization formula supplies its explicit reconstruction law.
Thus equality or vanishing can be checked on the one-parameter diagonal family alone.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric complex continuous multilinear forms of fixed order. -/
def symmetricContinuousMultilinearMapSubmodule
    (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] (n : ℕ) :
    Submodule ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) ℂ) where
  carrier := {B | ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → E), B (m ∘ σ) = B m}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC σ m
    change B (m ∘ σ) + C (m ∘ σ) = B m + C m
    rw [hB σ m, hC σ m]
  smul_mem' := by
    intro c B hB σ m
    change c • B (m ∘ σ) = c • B m
    rw [hB σ m]

/-- Restriction of a symmetric multilinear form to the diagonal, as a linear observable. -/
def symmetricContinuousMultilinearDiagonalLinearMap
    (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] (n : ℕ) :
    symmetricContinuousMultilinearMapSubmodule E n →ₗ[ℂ] (E → ℂ) where
  toFun B x := B.1 (fun _ ↦ x)
  map_add' B C := by ext x; rfl
  map_smul' c B := by ext x; rfl

@[simp] theorem symmetricContinuousMultilinearDiagonalLinearMap_apply
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] {n : ℕ}
    (B : symmetricContinuousMultilinearMapSubmodule E n) (x : E) :
    symmetricContinuousMultilinearDiagonalLinearMap E n B x = B.1 (fun _ ↦ x) := rfl

/-- Polarization reconstructs every symmetric form from its diagonal observable. -/
theorem symmetricContinuousMultilinearMap_polarization_reconstruction
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] {n : ℕ}
    (B : symmetricContinuousMultilinearMapSubmodule E n) (dirs : Fin n → E) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      ((-1 : ℂ) ^ (n - s.card) / (n.factorial : ℂ)) •
        symmetricContinuousMultilinearDiagonalLinearMap E n B
          (∑ j ∈ s, dirs j)) = B.1 dirs := by
  apply continuousMultilinearMap_symmetric_polarization B.1 dirs
  intro σ
  exact B.2 σ dirs

/-- Diagonal restriction is faithful on symmetric multilinear forms. -/
theorem symmetricContinuousMultilinearDiagonalLinearMap_injective
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] {n : ℕ} :
    Function.Injective (symmetricContinuousMultilinearDiagonalLinearMap E n) := by
  intro B C h
  apply Subtype.ext
  ext dirs
  rw [← symmetricContinuousMultilinearMap_polarization_reconstruction B dirs,
    ← symmetricContinuousMultilinearMap_polarization_reconstruction C dirs, h]

/-- Symmetric forms are linearly equivalent to their realized diagonal observables. -/
noncomputable def symmetricContinuousMultilinearDiagonalRangeEquiv
    (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] (n : ℕ) :
    symmetricContinuousMultilinearMapSubmodule E n ≃ₗ[ℂ]
      LinearMap.range (symmetricContinuousMultilinearDiagonalLinearMap E n) :=
  LinearEquiv.ofInjective (symmetricContinuousMultilinearDiagonalLinearMap E n)
    symmetricContinuousMultilinearDiagonalLinearMap_injective

/-- Hasse congruence: symmetric forms agree globally iff all diagonal probes agree. -/
theorem symmetricContinuousMultilinearMap_congr_hasse_iff
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] {n : ℕ}
    (B C : symmetricContinuousMultilinearMapSubmodule E n) :
    B = C ↔ ∀ x : E, B.1 (fun _ ↦ x) = C.1 (fun _ ↦ x) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply symmetricContinuousMultilinearDiagonalLinearMap_injective
    funext x
    exact h x

/-- Hasse vanishing: a symmetric form vanishes iff all diagonal probes vanish. -/
theorem symmetricContinuousMultilinearMap_eq_zero_hasse_iff
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E] {n : ℕ}
    (B : symmetricContinuousMultilinearMapSubmodule E n) :
    B = 0 ↔ ∀ x : E, B.1 (fun _ ↦ x) = 0 := by
  rw [symmetricContinuousMultilinearMap_congr_hasse_iff]
  simp

end

end GaloisForLFunctions.HTGeometry
