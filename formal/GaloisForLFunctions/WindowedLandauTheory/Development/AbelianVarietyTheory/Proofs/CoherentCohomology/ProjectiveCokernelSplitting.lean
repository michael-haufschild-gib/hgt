import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A generalized inverse describes a projective cokernel by a finite equation. -/

namespace GlobalTheory.SmoothDescent

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- For a map into a projective module, its cokernel is projective precisely
when the map has a generalized inverse. -/
theorem projective_cokernel_iff [Module.Projective R N] (f : M →ₗ[R] N) :
    Module.Projective R (N ⧸ LinearMap.range f) ↔
      ∃ g : N →ₗ[R] M, f ∘ₗ g ∘ₗ f = f := by
  let E := LinearMap.range f
  have hzero (x : M) : E.mkQ (f x) = 0 :=
    (Submodule.Quotient.mk_eq_zero E).2 (LinearMap.mem_range_self f x)
  rw [Module.Projective.iff_split_of_projective E.mkQ E.mkQ_surjective]
  constructor
  · rintro ⟨s, hs⟩
    let u : N →ₗ[R] N := LinearMap.id - s ∘ₗ E.mkQ
    have hu (n : N) : u n ∈ E := by
      apply (Submodule.Quotient.mk_eq_zero E).1
      change E.mkQ (n - s (E.mkQ n)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hs (E.mkQ n)).symm
    have hsurj : Function.Surjective f.rangeRestrict := by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
    obtain ⟨g, hg⟩ := Module.projective_lifting_property f.rangeRestrict (u.codRestrict E hu) hsurj
    refine ⟨g, LinearMap.ext fun x => ?_⟩
    have e := congrArg Subtype.val (LinearMap.congr_fun hg (f x))
    change f (g (f x)) = f x - s (E.mkQ (f x)) at e
    rwa [hzero, map_zero, sub_zero] at e
  · rintro ⟨g, hg⟩
    let u : N →ₗ[R] N := LinearMap.id - f ∘ₗ g
    have hu : E ≤ LinearMap.ker u := by
      rintro _ ⟨x, rfl⟩
      change f x - f (g (f x)) = 0
      exact sub_eq_zero.mpr (LinearMap.congr_fun hg x).symm
    let s := E.liftQ u hu
    refine ⟨s, LinearMap.ext fun y => ?_⟩
    obtain ⟨n, rfl⟩ := E.mkQ_surjective y
    change E.mkQ (n - f (g n)) = E.mkQ n
    rw [map_sub, hzero, sub_zero]

end GlobalTheory.SmoothDescent
