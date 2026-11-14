import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.Projective

/-!
# Normal form of an acyclic square-zero operator

Over a field, `ker d = im d` identifies the underlying space with two copies of `ker d`,
and identifies `d` with the shift `(x,y) ↦ (0,x)`. A linear section of `d` supplies the
coordinates. No finite-dimensional assumption is needed.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Acyclic square-zero modules are free dual-number modules in explicit coordinates. -/
theorem acyclic_squareZero_normalForm (d : Module.End k V)
    (hexact : LinearMap.range d = LinearMap.ker d) :
    ∃ e : V ≃ₗ[k] (LinearMap.ker d × LinearMap.ker d),
      ∀ v, e (d v) = (0, (e v).1) := by
  have hsq (v : V) : d (d v) = 0 := by
    have h : d v ∈ LinearMap.range d := ⟨v, rfl⟩
    rw [hexact] at h
    exact h
  let f : V →ₗ[k] LinearMap.ker d := d.codRestrict _ hsq
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : V) ∈ LinearMap.range d := by rw [hexact]; exact z.property
    obtain ⟨v, hv⟩ := hz
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hs_apply (z : LinearMap.ker d) : f (s z) = z := LinearMap.congr_fun hs z
  have hfsq (v : V) : f (d v) = 0 := Subtype.ext (hsq v)
  let e₀ : V →ₗ[k] (LinearMap.ker d × LinearMap.ker d) :=
    f.prod ((LinearMap.id - s.comp f).codRestrict (LinearMap.ker d) (by
      intro v
      change d (v - s (f v)) = 0
      rw [map_sub]
      have h := congrArg Subtype.val (hs_apply (f v))
      change d (s (f v)) = d v at h
      rw [h, sub_self]))
  have he (v : V) : (e₀ v).1 = f v := rfl
  have he₂ (v : V) : ((e₀ v).2 : V) = v - s (f v) := rfl
  have he_bij : Function.Bijective e₀ := by
    constructor
    · intro v w h
      have h₁ : f v = f w := congrArg Prod.fst h
      have h₂ := congrArg (fun z : LinearMap.ker d × LinearMap.ker d => (z.2 : V)) h
      change v - s (f v) = w - s (f w) at h₂
      rw [h₁] at h₂
      exact sub_left_inj.mp h₂
    · intro p
      refine ⟨s p.1 + p.2, ?_⟩
      have hz : f (p.2 : V) = 0 := Subtype.ext p.2.property
      have hfirst : f (s p.1 + p.2) = p.1 := by rw [map_add, hs_apply, hz, add_zero]
      apply Prod.ext
      · exact hfirst
      · apply Subtype.ext
        rw [he₂, hfirst]
        abel
  refine ⟨LinearEquiv.ofBijective e₀ he_bij, ?_⟩
  intro v
  apply Prod.ext
  · exact hfsq v
  · apply Subtype.ext
    change d v - s (f (d v)) = d v
    rw [hfsq, map_zero, sub_zero]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.acyclic_squareZero_normalForm
