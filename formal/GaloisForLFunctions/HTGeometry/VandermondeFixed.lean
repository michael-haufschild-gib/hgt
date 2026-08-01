import GaloisForLFunctions.HTGeometry.VandermondeSign
import GaloisForLFunctions.HTGeometry.GaloisFixedByAll

/-!
# The discriminant lies in the base field

An automorphism permutes the roots, and permuting the arguments of the Vandermonde product only
changes its sign.  So the square of the Vandermonde product is fixed by every automorphism, and in a
Galois extension that means it comes from the base field.

That square is the discriminant, and this is what makes the discriminant a base-field element whose
square root generates the quadratic subextension.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ}

theorem map_vandermondeProd (σ : E ≃ₐ[F] E) (v : Fin d → E) :
    σ (vandermondeProd v) = vandermondeProd (fun i => σ (v i)) := by
  rw [vandermondeProd, vandermondeProd, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub]

/-- **The Vandermonde square is fixed by every automorphism permuting the roots.** -/
theorem vandermondeSq_fixed (v : Fin d → E) (σ : E ≃ₐ[F] E) (e : Equiv.Perm (Fin d))
    (hσ : ∀ i, σ (v i) = v (e i)) :
    σ (vandermondeProd v * vandermondeProd v) =
      vandermondeProd v * vandermondeProd v := by
  have hmap : σ (vandermondeProd v) = (Equiv.Perm.sign e : ℤ) • vandermondeProd v := by
    rw [map_vandermondeProd]
    have hcomp : (fun i => σ (v i)) = v ∘ e := by
      funext i
      exact hσ i
    rw [hcomp, vandermondeProd_comp]
  rw [map_mul, hmap]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1 <;> rw [h1] <;> simp

/-- **The discriminant comes from the base field.** -/
theorem exists_algebraMap_vandermondeSq [FiniteDimensional F E] [IsGalois F E]
    (v : Fin d → E) (hperm : ∀ σ : E ≃ₐ[F] E, ∃ e : Equiv.Perm (Fin d), ∀ i, σ (v i) = v (e i)) :
    ∃ y : F, algebraMap F E y = vandermondeProd v * vandermondeProd v := by
  refine exists_algebraMap_of_forall_fixed fun σ => ?_
  obtain ⟨e, he⟩ := hperm σ
  exact vandermondeSq_fixed v σ e he

/-- **An odd permutation of the roots moves the Vandermonde product.**  So if some automorphism acts
oddly, the product is not in the base field. -/
theorem vandermondeProd_notMem_bot [CharZero E] (v : Fin d → E) (hinj : Function.Injective v)
    (σ : E ≃ₐ[F] E) (e : Equiv.Perm (Fin d)) (hσ : ∀ i, σ (v i) = v (e i))
    (hsign : Equiv.Perm.sign e = -1) :
    vandermondeProd v ∉ (⊥ : IntermediateField F E) := by
  intro hmem
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hmem
  have hfix : σ (vandermondeProd v) = vandermondeProd v := by
    rw [← hy]
    exact σ.commutes y
  have hneg : σ (vandermondeProd v) = -vandermondeProd v := by
    rw [map_vandermondeProd]
    have hcomp : (fun i => σ (v i)) = v ∘ e := by
      funext i
      exact hσ i
    rw [hcomp, vandermondeProd_comp, hsign]
    simp
  have hzero : vandermondeProd v = 0 := by
    have h := hfix.symm.trans hneg
    linear_combination h / 2
  exact vandermondeProd_ne_zero hinj hzero

/-- **The Vandermonde product of members of a subfield lies in it.** -/
theorem vandermondeProd_mem (S : IntermediateField F E) (v : Fin d → E) (hv : ∀ i, v i ∈ S) :
    vandermondeProd v ∈ S := by
  rw [vandermondeProd]
  exact prod_mem fun i _ => prod_mem fun j _ => sub_mem (hv _) (hv _)

/-- **A subfield element outside the base of the subfield is outside the base of the ambient.** -/
theorem notMem_bot_of_notMem_bot_coe {S : IntermediateField F E} {x : S}
    (hx : x ∉ (⊥ : IntermediateField F S)) : (x : E) ∉ (⊥ : IntermediateField F E) := by
  intro hmem
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hmem
  refine hx (IntermediateField.mem_bot.2 ⟨y, ?_⟩)
  exact Subtype.ext (by
    rw [← hy]
    exact (IsScalarTower.algebraMap_apply F S E y).symm)

end GaloisForLFunctions.HTGeometry
