import Mathlib.RepresentationTheory.Invariants

/-!
# Invariants are exact under normalized averaging

When the order of the group is invertible in the coefficients, the averaging projector onto the
invariants is natural in the representation: it commutes with every equivariant map, because it is a
fixed linear combination of the group elements.  Naturality turns the projector into a splitting of
the invariants functor, so invariants preserve surjections and exactness — not only injections and
kernels, which they preserve for formal reasons.

This is the normalized Haar averaging argument for a compact group acting through a finite quotient:
applying continuous invariants to a strict short exact sequence of coefficient modules leaves it
strict and exact.

* `invariantsMap` : the map induced on invariants by an equivariant map.
* `averageMap_apply` : the averaging projector as a normalized sum over the group.
* `map_averageMap` : **the averaging projector is natural in the representation.**
* `invariantsMap_surjective` : **invariants preserve surjections.**
* `range_invariantsMap` : **invariants preserve exactness.**
* `invariants_shortExact` : a short exact sequence of representations stays short exact.
-/

open MonoidAlgebra Representation

noncomputable section

namespace GaloisForLFunctions

variable {k G V W U : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)

/-! ## The induced map on invariants -/

section Induced

variable {ρ σ}

/-- The map induced on the invariants by an equivariant map. -/
def invariantsMap (f : V →ₗ[k] W) (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)) :
    ρ.invariants →ₗ[k] σ.invariants :=
  (f ∘ₗ ρ.invariants.subtype).codRestrict σ.invariants fun v g => by
    show σ g (f (v : V)) = f (v : V)
    rw [← hf g (v : V), v.2 g]

@[simp] theorem invariantsMap_coe (f : V →ₗ[k] W) (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v))
    (v : ρ.invariants) : (invariantsMap f hf v : W) = f (v : V) := rfl

theorem invariantsMap_injective (f : V →ₗ[k] W)
    (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)) (hinj : Function.Injective f) :
    Function.Injective (invariantsMap (ρ := ρ) (σ := σ) f hf) := by
  intro v w h
  refine Subtype.ext (hinj ?_)
  have := congrArg Subtype.val h
  rwa [invariantsMap_coe, invariantsMap_coe] at this

end Induced

/-! ## The averaging projector is natural -/

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The averaging projector onto the invariants, as a normalized sum over the group. -/
theorem averageMap_apply (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp

/-- **The averaging projector is natural in the representation**: it commutes with every equivariant
map, being a fixed linear combination of the group elements. -/
theorem map_averageMap (f : V →ₗ[k] W) (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)) (v : V) :
    f (ρ.averageMap v) = σ.averageMap (f v) := by
  rw [averageMap_apply, averageMap_apply, map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun g _ => hf g v)

/-! ## Exactness -/

section Exact

variable {ρ σ τ}

/-- **Invariants preserve surjections**: an equivariant surjection stays surjective on invariants,
because the averaging projector produces an invariant preimage. -/
theorem invariantsMap_surjective (f : V →ₗ[k] W)
    (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v)) (hsurj : Function.Surjective f) :
    Function.Surjective (invariantsMap (ρ := ρ) (σ := σ) f hf) := by
  rintro ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := hsurj w
  refine ⟨⟨ρ.averageMap v, ρ.averageMap_invariant v⟩, Subtype.ext ?_⟩
  rw [invariantsMap_coe, map_averageMap ρ σ f hf, σ.averageMap_id (f v) hw]

/-- **Invariants preserve exactness**: the image of the induced map is the kernel of the next one.
The averaging projector lifts an invariant element of the kernel to an invariant preimage. -/
theorem range_invariantsMap (f : V →ₗ[k] W) (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v))
    (f' : W →ₗ[k] U) (hf' : ∀ (g : G) (w : W), f' (σ g w) = τ g (f' w))
    (hex : LinearMap.range f = LinearMap.ker f') :
    LinearMap.range (invariantsMap (ρ := ρ) (σ := σ) f hf)
      = LinearMap.ker (invariantsMap (ρ := σ) (σ := τ) f' hf') := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
    rw [invariantsMap_coe, invariantsMap_coe]
    have hmem : f (v : V) ∈ LinearMap.range f := ⟨(v : V), rfl⟩
    rw [hex, LinearMap.mem_ker] at hmem
    exact hmem
  · rintro ⟨w, hw⟩ hker
    have hw0 : f' w = 0 := by
      have := congrArg Subtype.val (LinearMap.mem_ker.mp hker)
      rwa [invariantsMap_coe] at this
    have hmem : w ∈ LinearMap.range f := by
      rw [hex]
      exact LinearMap.mem_ker.mpr hw0
    obtain ⟨v, rfl⟩ := hmem
    refine ⟨⟨ρ.averageMap v, ρ.averageMap_invariant v⟩, Subtype.ext ?_⟩
    rw [invariantsMap_coe, map_averageMap ρ σ f hf, σ.averageMap_id (f v) hw]

/-- **A short exact sequence of representations stays short exact after invariants.**  This is the
normalized averaging argument: continuous invariants are exact on the coefficient modules, so
applying them to a strict quasi-isomorphism preserves it. -/
theorem invariants_shortExact (f : V →ₗ[k] W) (hf : ∀ (g : G) (v : V), f (ρ g v) = σ g (f v))
    (f' : W →ₗ[k] U) (hf' : ∀ (g : G) (w : W), f' (σ g w) = τ g (f' w))
    (hinj : Function.Injective f) (hex : LinearMap.range f = LinearMap.ker f')
    (hsurj : Function.Surjective f') :
    Function.Injective (invariantsMap (ρ := ρ) (σ := σ) f hf)
      ∧ LinearMap.range (invariantsMap (ρ := ρ) (σ := σ) f hf)
          = LinearMap.ker (invariantsMap (ρ := σ) (σ := τ) f' hf')
      ∧ Function.Surjective (invariantsMap (ρ := σ) (σ := τ) f' hf') :=
  ⟨invariantsMap_injective f hf hinj, range_invariantsMap f hf f' hf' hex,
    invariantsMap_surjective f' hf' hsurj⟩

end Exact

end GaloisForLFunctions

end
