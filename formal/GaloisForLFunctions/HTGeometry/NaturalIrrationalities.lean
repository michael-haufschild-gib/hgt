import GaloisForLFunctions.HTGeometry.AlgEquivAdjoinExt
import GaloisForLFunctions.HTGeometry.GaloisFixedByAll

/-!
# Natural irrationalities

Restricting an automorphism of a compositum over one factor to the other factor is a group
homomorphism.  It is injective because an automorphism fixing both factors fixes everything, and
the fixed field of its image is the intersection of the factors.

So when the factors meet in the base, the restriction is an isomorphism: base change along the
second factor does not shrink the Galois group of the first.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Restriction of an automorphism over one factor of a compositum to the other factor. -/
noncomputable def compositumRestrict (E M : IntermediateField F L) [Normal F E] :
    (L ≃ₐ[M] L) →* (E ≃ₐ[F] E) :=
  (AlgEquiv.restrictNormalHom E).comp
    { toFun := fun σ : L ≃ₐ[M] L => σ.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem compositumRestrict_commutes (E M : IntermediateField F L) [Normal F E]
    (σ : L ≃ₐ[M] L) (x : E) :
    (algebraMap E L) (compositumRestrict E M σ x) = σ (algebraMap E L x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars F) E x

theorem smul_eq_of_mem_second (M : IntermediateField F L) (σ : L ≃ₐ[M] L)
    {x : L} (hx : x ∈ M) : σ x = x := by
  have h := σ.commutes (⟨x, hx⟩ : M)
  exact h

/-- **The restriction is injective.** -/
theorem compositumRestrict_injective {E M : IntermediateField F L} [Normal F E]
    (hEM : E ⊔ M = ⊤) : Function.Injective (compositumRestrict E M) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  have hE : ∀ x ∈ E, (σ.restrictScalars F) x = x := by
    intro x hx
    have h := compositumRestrict_commutes E M σ ⟨x, hx⟩
    rw [hσ] at h
    exact h.symm
  have hM : ∀ x ∈ M, (σ.restrictScalars F) x = x := fun x hx => smul_eq_of_mem_second M σ hx
  have hrefl : σ.restrictScalars F = AlgEquiv.refl :=
    algEquiv_eq_refl_of_sup_eq_top hEM hE hM
  refine AlgEquiv.ext fun x => ?_
  have := AlgEquiv.ext_iff.1 hrefl x
  exact this

/-- **The restriction is surjective when the factors meet in the base.** -/
theorem compositumRestrict_surjective {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E]
    [FiniteDimensional M L] [IsGalois M L]
    (hinf : E ⊓ M = ⊥) : Function.Surjective (compositumRestrict E M) := by
  have hfix : IntermediateField.fixedField (compositumRestrict E M).range = ⊥ := by
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hy
    have hfixL : ∀ σ : L ≃ₐ[M] L, σ (algebraMap E L y) = algebraMap E L y := by
      intro σ
      have hmem : compositumRestrict E M σ ∈ (compositumRestrict E M).range := ⟨σ, rfl⟩
      have h := compositumRestrict_commutes E M σ y
      rw [hy _ hmem] at h
      exact h.symm
    have hEmem : (algebraMap E L) y ∈ E := y.2
    have hinter := mem_inf_of_forall_fixed (E := E) (M := M) hEmem hfixL
    rw [hinf] at hinter
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hinter
    refine IntermediateField.mem_bot.2 ⟨c, ?_⟩
    have hinj : Function.Injective (algebraMap E L) := (algebraMap E L).injective
    refine hinj ?_
    rw [← hc, ← IsScalarTower.algebraMap_apply F E L]
  have htop : (compositumRestrict E M).range = ⊤ := by
    have h1 := IntermediateField.fixingSubgroup_fixedField (compositumRestrict E M).range
    rw [hfix, IntermediateField.fixingSubgroup_bot] at h1
    exact h1.symm
  intro τ
  have hmem : τ ∈ (compositumRestrict E M).range := by
    rw [htop]
    exact Subgroup.mem_top τ
  exact hmem

/-- **Natural irrationalities.**  If the two factors of a compositum meet in the base, restriction
is an isomorphism from the automorphisms over one factor to the Galois group of the other. -/
noncomputable def compositumRestrictEquiv {E M : IntermediateField F L} [Normal F E]
    [FiniteDimensional F E] [IsGalois F E]
    [FiniteDimensional M L] [IsGalois M L]
    (hEM : E ⊔ M = ⊤) (hinf : E ⊓ M = ⊥) :
    (L ≃ₐ[M] L) ≃* (E ≃ₐ[F] E) :=
  MulEquiv.ofBijective (compositumRestrict E M)
    ⟨compositumRestrict_injective hEM, compositumRestrict_surjective hinf⟩

end GaloisForLFunctions.HTGeometry
