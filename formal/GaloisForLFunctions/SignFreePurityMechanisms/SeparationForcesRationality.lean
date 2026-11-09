import Mathlib

/-!
# Separation forces rationality

The sign-free mechanism behind Riemann hypotheses proved by Newton polygons: an invariant of the
symmetry group that takes distinct values on distinct roots forces every root to be fixed.

* Galois form (`mem_range_algebraMap_of_injOn`): for a Galois extension `L/K` and a function on
  `L` invariant under `Gal(L/K)`, a polynomial over `K` on whose roots the function is injective
  has all its roots in `K`.
* Archimedean form (`im_eq_zero_of_norm_injOn`): a real polynomial whose complex roots have
  pairwise distinct absolute values has only real roots.
* Involution form (`fixed_of_injOn`): a self-map of a set preserving a function injective on that
  set is the identity there.
-/

open Polynomial

namespace GaloisForLFunctions.SignFreePurityMechanisms

/-- A self-map of `Z` preserving a function that is injective on `Z` fixes every point of `Z`. -/
theorem fixed_of_injOn {α β : Type*} {Z : Set α} {τ : α → α} {h : α → β}
    (hτ : Set.MapsTo τ Z Z) (hh : ∀ z ∈ Z, h (τ z) = h z) (hinj : Set.InjOn h Z)
    {z : α} (hz : z ∈ Z) : τ z = z :=
  hinj (hτ hz) hz (hh z hz)

/-- **Separation principle.** A Galois-invariant function that separates the roots of a polynomial
over the base field forces all roots into the base field. -/
theorem mem_range_algebraMap_of_injOn {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (v : L → Γ) (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), v (σ x) = v x)
    (f : K[X]) (hinj : Set.InjOn v (f.rootSet L)) {x : L} (hx : x ∈ f.rootSet L) :
    x ∈ (algebraMap K L).range := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  refine fixed_of_injOn (Z := f.rootSet L) (τ := σ) (fun y hy => ?_) (fun y _ => hv σ y) hinj hx
  rw [mem_rootSet] at hy ⊢
  exact ⟨hy.1, by rw [aeval_algHom_apply, hy.2, map_zero]⟩

/-- **Archimedean separation.** A real polynomial whose complex roots have pairwise distinct
absolute values has only real roots: conjugate roots share their absolute value. -/
theorem im_eq_zero_of_norm_injOn (f : ℝ[X]) (hinj : Set.InjOn (fun z : ℂ => ‖z‖) (f.rootSet ℂ))
    {z : ℂ} (hz : z ∈ f.rootSet ℂ) : z.im = 0 := by
  have hfix : Complex.conjAe z = z :=
    fixed_of_injOn (Z := f.rootSet ℂ) (τ := Complex.conjAe) (fun y hy => by
      rw [mem_rootSet] at hy ⊢
      exact ⟨hy.1, by rw [aeval_algHom_apply, hy.2, map_zero]⟩)
      (fun y _ => by simp) hinj hz
  exact Complex.conj_eq_iff_im.mp hfix

end GaloisForLFunctions.SignFreePurityMechanisms
