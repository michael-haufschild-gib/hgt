import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Generalized eigenspaces under an injective intertwiner

Finite Hilbert--Schmidt sections are realized inside the ambient `ℓ²` space by zero extension.
Their matrix and operator models are related by an injective intertwiner, not a global
equivalence.  This file supplies the exact algebraic transport needed for multiplicities.
-/

namespace GaloisForLFunctions.HTGeometry

open Module.End

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Powers of a shifted endomorphism commute with an intertwining linear map. -/
theorem map_pow_sub_smul_of_intertwining (f : Module.End R V) (g : Module.End R W)
    (L : V →ₗ[R] W) (hL : ∀ x, L (f x) = g (L x)) (mu : R) (n : ℕ) (x : V) :
    L (((f - mu • 1) ^ n) x) = ((g - mu • 1) ^ n) (L x) := by
  have hshift (y : V) : L ((f - mu • 1) y) = (g - mu • 1) (L y) := by
    change L (f y - mu • y) = g (L y) - mu • L y
    rw [map_sub, map_smul, hL]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change L ((f - mu • 1) (((f - mu • 1) ^ n) x)) =
        (g - mu • 1) (((g - mu • 1) ^ n) (L x))
      rw [hshift, ih]

/-- If every generalized `mu`-eigenvector of the target lies in the range of an injective
intertwiner, that intertwiner identifies the two generalized eigenspaces exactly. -/
theorem map_maxGenEigenspace_eq_of_intertwining (f : Module.End R V) (g : Module.End R W)
    (L : V →ₗ[R] W) (hLinj : Function.Injective L) (hL : ∀ x, L (f x) = g (L x)) (mu : R)
    (hle : g.maxGenEigenspace mu ≤ LinearMap.range L) :
    Submodule.map L (f.maxGenEigenspace mu) = g.maxGenEigenspace mu := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace f mu x).mp hx
    refine (Module.End.mem_maxGenEigenspace g mu (L x)).mpr ⟨n, ?_⟩
    rw [← map_pow_sub_smul_of_intertwining f g L hL]
    simp [hn]
  · intro y hy
    obtain ⟨x, hx⟩ := hle hy
    subst y
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace g mu (L x)).mp hy
    have hzero : ((f - mu • 1) ^ n) x = 0 := by
      apply hLinj
      rw [map_zero, map_pow_sub_smul_of_intertwining f g L hL]
      exact hn
    exact ⟨x, (Module.End.mem_maxGenEigenspace f mu x).mpr ⟨n, hzero⟩, rfl⟩

/-- The exact generalized-eigenspace transport preserves algebraic multiplicity. -/
theorem finrank_maxGenEigenspace_eq_of_intertwining (f : Module.End R V) (g : Module.End R W)
    (L : V →ₗ[R] W) (hLinj : Function.Injective L) (hL : ∀ x, L (f x) = g (L x)) (mu : R)
    (hle : g.maxGenEigenspace mu ≤ LinearMap.range L) :
    Module.finrank R (f.maxGenEigenspace mu) = Module.finrank R (g.maxGenEigenspace mu) := by
  rw [← map_maxGenEigenspace_eq_of_intertwining f g L hLinj hL mu hle]
  exact (Submodule.equivMapOfInjective L hLinj (f.maxGenEigenspace mu)).finrank_eq

end GaloisForLFunctions.HTGeometry
