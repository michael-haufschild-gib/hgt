import Mathlib

/-!
# Separation forces rationality

The sign-free mechanism behind Riemann hypotheses proved by Newton polygons: an invariant of the
symmetry that takes distinct values on distinct roots forces every root to be fixed.

* Involution form (`fixed_of_injOn`): a self-map of a set preserving a function injective on that
  set is the identity there.
* Galois form (`mem_range_algebraMap_of_injOn`): for a Galois extension `L/K` and a function on
  `L` invariant under `Gal(L/K)`, a polynomial over `K` on whose roots the function is injective
  has all its roots in `K`.
* Ultrametric instance (`mem_range_algebraMap_of_spectralNorm_injOn`): the invariant is the
  spectral norm, the extension of the norm of `K` read from minimal polynomials.
* Archimedean instance (`im_eq_zero_of_norm_injOn`): a real polynomial whose complex roots have
  pairwise distinct absolute values has only real roots.
-/

open Polynomial

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- A self-map of `Z` preserving a function that is injective on `Z` fixes every point of `Z`. -/
theorem fixed_of_injOn {α β : Type*} {Z : Set α} {τ : α → α} {h : α → β}
    (hτ : Set.MapsTo τ Z Z) (hh : ∀ z ∈ Z, h (τ z) = h z) (hinj : Set.InjOn h Z)
    {z : α} (hz : z ∈ Z) : τ z = z :=
  hinj (hτ hz) hz (hh z hz)

/-- An algebra automorphism over the coefficient field permutes the roots of a polynomial. -/
theorem mapsTo_rootSet_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L] (f : K[X])
    (σ : L ≃ₐ[K] L) : Set.MapsTo σ (f.rootSet L) (f.rootSet L) := fun y hy => by
  rw [mem_rootSet] at hy ⊢
  have h := aeval_algHom_apply (σ : L →ₐ[K] L) y f
  rw [hy.2, map_zero] at h
  exact ⟨hy.1, h⟩

/-- **Separation principle.** A Galois-invariant function that separates the roots of a polynomial
over the base field forces all roots into the base field. -/
theorem mem_range_algebraMap_of_injOn {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (v : L → Γ) (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (f : K[X]) (hinj : Set.InjOn v (f.rootSet L)) {x : L} (hx : x ∈ f.rootSet L) :
    x ∈ Set.range (algebraMap K L) := by
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  exact fun σ => fixed_of_injOn (mapsTo_rootSet_algEquiv f σ) (fun y _ => hv σ y) hinj hx

/-- **Ultrametric separation.** If the spectral norm separates the roots of a polynomial over a
normed field `K` in a Galois extension, the roots lie in `K`. -/
theorem mem_range_algebraMap_of_spectralNorm_injOn {K L : Type*} [NormedField K] [Field L]
    [Algebra K L] [IsGalois K L] (f : K[X]) (hinj : Set.InjOn (spectralNorm K L) (f.rootSet L))
    {x : L} (hx : x ∈ f.rootSet L) : x ∈ Set.range (algebraMap K L) :=
  mem_range_algebraMap_of_injOn (spectralNorm K L)
    (fun σ y => (spectralNorm_eq_of_equiv σ y).symm) f hinj hx

/-- **Archimedean separation.** A real polynomial whose complex roots have pairwise distinct
absolute values has only real roots: conjugate roots share their absolute value. -/
theorem im_eq_zero_of_norm_injOn (f : ℝ[X]) (hinj : Set.InjOn (fun z : ℂ => ‖z‖) (f.rootSet ℂ))
    {z : ℂ} (hz : z ∈ f.rootSet ℂ) : z.im = 0 := by
  have hfix : Complex.conjAe z = z :=
    fixed_of_injOn (mapsTo_rootSet_algEquiv f Complex.conjAe)
      (fun y _ => by simp) hinj hz
  exact Complex.conj_eq_iff_im.mp hfix

#print axioms mem_range_algebraMap_of_injOn
#print axioms mem_range_algebraMap_of_spectralNorm_injOn
#print axioms im_eq_zero_of_norm_injOn

end GaloisForLFunctions.SignFreePurityMechanisms
