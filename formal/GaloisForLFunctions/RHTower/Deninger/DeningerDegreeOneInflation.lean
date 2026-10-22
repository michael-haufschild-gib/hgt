import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Degree one along a surjection

With trivial coefficients, first cohomology is the group of homomorphisms into the coefficients.
Along a surjection, restriction of homomorphisms is injective, and its image is exactly the
homomorphisms killing the kernel.  So a degree-one comparison along a surjection is an isomorphism
precisely when every homomorphism out of the source kills the kernel — which is the shape in which
a rational-homology computation enters.

* `deningerHomRestrict_injective` : restriction along a surjection is injective.
* `deningerHomRestrict_mem_range_iff` : its image is the homomorphisms killing the kernel.
* `deningerHomRestrict_bijective_iff` : the degree-one comparison is an isomorphism exactly when
  the kernel is killed by every homomorphism.
-/

namespace RHTower

section DegreeOne

variable {R A M : Type*} [Group R] [Group A] [CommGroup M]

/-- Restriction of homomorphisms along a group homomorphism. -/
def deningerHomRestrict (f : R →* A) (phi : A →* M) : R →* M := phi.comp f

/-- **Restriction along a surjection is injective.** -/
theorem deningerHomRestrict_injective {f : R →* A} (hf : Function.Surjective f) :
    Function.Injective (deningerHomRestrict (M := M) f) := by
  intro phi psi h
  refine MonoidHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := hf a
  exact congrFun (congrArg (fun g : R →* M => (g : R → M)) h) r

/-- **The image of restriction is the homomorphisms killing the kernel.** -/
theorem deningerHomRestrict_mem_range_iff {f : R →* A} (hf : Function.Surjective f)
    (psi : R →* M) :
    (∃ phi : A →* M, deningerHomRestrict f phi = psi) ↔ ∀ k ∈ f.ker, psi k = 1 := by
  constructor
  · rintro ⟨phi, rfl⟩ k hk
    show phi (f k) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
  · intro hpsi
    refine ⟨(QuotientGroup.lift f.ker psi hpsi).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, ?_⟩
    refine MonoidHom.ext fun r => ?_
    show (QuotientGroup.lift f.ker psi hpsi)
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f r)) = psi r
    have hsymm : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f r)
        = QuotientGroup.mk r := by
      refine (QuotientGroup.quotientKerEquivOfSurjective f hf).injective ?_
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hsymm]
    rfl

/-- **The degree-one comparison is an isomorphism exactly when the kernel is killed.** -/
theorem deningerHomRestrict_bijective_iff {f : R →* A} (hf : Function.Surjective f) :
    Function.Bijective (deningerHomRestrict (M := M) f)
      ↔ ∀ (psi : R →* M), ∀ k ∈ f.ker, psi k = 1 := by
  constructor
  · rintro ⟨_, hsurj⟩ psi k hk
    obtain ⟨phi, rfl⟩ := hsurj psi
    show phi (f k) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
  · intro h
    refine ⟨deningerHomRestrict_injective hf, fun psi => ?_⟩
    exact (deningerHomRestrict_mem_range_iff hf psi).mpr (h psi)

end DegreeOne

end RHTower
