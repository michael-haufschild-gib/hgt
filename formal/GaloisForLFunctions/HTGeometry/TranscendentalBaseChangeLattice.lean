import GaloisForLFunctions.HTGeometry.TranscendentalBaseChange
import GaloisForLFunctions.HTGeometry.NaturalIrrationalities

/-!
# Base change along a free parameter preserves the intermediate-field lattice

Restriction identifies the Galois group of a compositum over one factor with the Galois group of the
other factor, so it carries the lattice of intermediate fields across.  For a factor of the form
`F(t)` with `t` transcendental the two factors meet in the base, which is what makes the restriction
an isomorphism, and the trace of an intermediate field of `Ω/F(t)` on the Galois factor is the fixed
field of the restricted subgroup.

Consequently a primitive step — no field strictly between `F` and `J` — stays primitive after
adjoining `t`.
-/

open IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- The fixed field of a restricted subgroup is the trace of the fixed field. -/
theorem mem_fixedField_map_compositumRestrict_iff
    (N M : IntermediateField F Ω) [Normal F N]
    (H : Subgroup (Ω ≃ₐ[↥M] Ω)) (x : ↥N) :
    x ∈ IntermediateField.fixedField (H.map (compositumRestrict N M)) ↔
      ∀ σ ∈ H, σ (x : Ω) = (x : Ω) := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ hσ
    have hx := h (compositumRestrict N M σ) ⟨σ, hσ, rfl⟩
    have hc := compositumRestrict_commutes N M σ x
    rw [hx] at hc
    have hcoe : (algebraMap (↥N) Ω) x = (x : Ω) := rfl
    rw [hcoe] at hc
    exact hc.symm
  · rintro h τ ⟨σ, hσ, rfl⟩
    have hc := compositumRestrict_commutes N M σ x
    have hcoe : (algebraMap (↥N) Ω) x = (x : Ω) := rfl
    rw [hcoe, h σ hσ] at hc
    exact (algebraMap (↥N) Ω).injective (by rw [hc, hcoe])

/-- **Base change along a transcendental element preserves primitivity.**  If no field lies strictly
between `F` and `J`, then none lies strictly between `F(t)` and `J(t)`. -/
theorem eq_bot_or_eq_adjoin_of_primitive_base_change
    (N : IntermediateField F Ω) [FiniteDimensional F N] [IsGalois F N]
    (t : Ω) (ht : Transcendental F t) (htN : Transcendental (↥N) t)
    (htop : N ⊔ F⟮t⟯ = ⊤)
    (J : IntermediateField F Ω) (hJN : J ≤ N)
    (hprim : ∀ P : IntermediateField F Ω, P ≤ J → P = ⊥ ∨ P = J)
    (M : IntermediateField (↥F⟮t⟯) Ω)
    (hM : M ≤ IntermediateField.adjoin (↥F⟮t⟯) (J : Set Ω)) :
    M = ⊥ ∨ M = IntermediateField.adjoin (↥F⟮t⟯) (J : Set Ω) := by
  classical
  haveI : Normal F ↥N := IsGalois.to_normal
  haveI hfin : FiniteDimensional (↥F⟮t⟯) Ω := finiteDimensional_of_sup_eq_top N t htN htop
  haveI hgal : IsGalois (↥F⟮t⟯) Ω := isGalois_of_sup_eq_top N t htop
  have hinf : N ⊓ F⟮t⟯ = ⊥ :=
    inf_adjoin_simple_eq_bot_of_isAlgebraic N
      (fun x hx => isAlgebraic_of_mem_of_finiteDimensional N hx) t ht
  have hρinj : Function.Injective (compositumRestrict N F⟮t⟯) :=
    compositumRestrict_injective htop
  have hρsurj : Function.Surjective (compositumRestrict N F⟮t⟯) :=
    compositumRestrict_surjective hinf
  set Jt : IntermediateField (↥F⟮t⟯) Ω := IntermediateField.adjoin (↥F⟮t⟯) (J : Set Ω) with hJt
  set J' : IntermediateField F ↥N := IntermediateField.restrict hJN with hJ'
  -- the trace of `J(t)` on `N` is `J`
  have hmemJ' : ∀ x : ↥N, x ∈ J' ↔ (x : Ω) ∈ J := by
    intro x
    rw [hJ']
    exact IntermediateField.mem_restrict hJN x
  have hJfix : (Jt.fixingSubgroup).map (compositumRestrict N F⟮t⟯) = J'.fixingSubgroup := by
    refine le_antisymm ?_ ?_
    · rintro τ ⟨σ, hσ, rfl⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hxJ : (x : Ω) ∈ J := (hmemJ' x).1 hx
      have hxJt : (x : Ω) ∈ Jt := IntermediateField.subset_adjoin _ _ hxJ
      have hfixed : σ (x : Ω) = (x : Ω) :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ hxJt
      have hc := compositumRestrict_commutes N F⟮t⟯ σ x
      have hcoe : (algebraMap (↥N) Ω) x = (x : Ω) := rfl
      rw [hcoe, hfixed] at hc
      exact (algebraMap (↥N) Ω).injective (by rw [hc, hcoe])
    · intro τ hτ
      obtain ⟨σ, rfl⟩ := hρsurj τ
      refine ⟨σ, ?_, rfl⟩
      show σ ∈ Jt.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      have hJσ : ∀ y ∈ (J : Set Ω), σ y = y := by
        intro y hy
        have hyN : y ∈ N := hJN hy
        have hτy := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ (⟨y, hyN⟩ : ↥N)
          ((hmemJ' ⟨y, hyN⟩).2 hy)
        have hc := compositumRestrict_commutes N F⟮t⟯ σ (⟨y, hyN⟩ : ↥N)
        rw [hτy] at hc
        have hcoe : (algebraMap (↥N) Ω) (⟨y, hyN⟩ : ↥N) = y := rfl
        rw [hcoe] at hc
        exact hc.symm
      intro x hx
      have hle : Jt ≤ IntermediateField.fixedField (Subgroup.closure {σ}) := by
        rw [hJt]
        refine IntermediateField.adjoin_le_iff.2 fun y hy => ?_
        show y ∈ IntermediateField.fixedField (Subgroup.closure {σ})
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
        · rintro h rfl
          exact hJσ y hy
        · rfl
        · intro g₁ g₂ _ _ h₁ h₂
          simp only [AlgEquiv.mul_apply]
          rw [h₂, h₁]
        · intro g _ h
          have := congrArg (fun z : Ω => g.symm z) h
          simpa using this.symm
      have := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ
        (Subgroup.subset_closure rfl)
      exact this
  -- the trace of `M` on `N`
  set H : Subgroup (Ω ≃ₐ[↥F⟮t⟯] Ω) := M.fixingSubgroup with hH
  have hMfixed : IntermediateField.fixedField H = M :=
    IsGalois.fixedField_fixingSubgroup M
  have htrace : ∀ x : ↥N,
      x ∈ IntermediateField.fixedField (H.map (compositumRestrict N F⟮t⟯)) ↔ (x : Ω) ∈ M := by
    intro x
    rw [mem_fixedField_map_compositumRestrict_iff N F⟮t⟯ H x]
    constructor
    · intro h
      rw [← hMfixed, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => h σ hσ
    · intro h σ hσ
      rw [← hMfixed] at h
      exact (IntermediateField.mem_fixedField_iff _ _).1 h σ hσ
  -- the trace is contained in `J`
  set P : IntermediateField F Ω := M.restrictScalars F ⊓ N with hP
  have hPJ : P ≤ J := by
    intro x hx
    have hxN : x ∈ N := hx.2
    have hxM : x ∈ M := hx.1
    have hxJt : x ∈ Jt := hM hxM
    have hxfix : (⟨x, hxN⟩ : ↥N)
        ∈ IntermediateField.fixedField ((Jt.fixingSubgroup).map (compositumRestrict N F⟮t⟯)) := by
      rw [mem_fixedField_map_compositumRestrict_iff N F⟮t⟯ _ (⟨x, hxN⟩ : ↥N)]
      intro σ hσ
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ hxJt
    rw [hJfix, IsGalois.fixedField_fixingSubgroup] at hxfix
    exact (hmemJ' (⟨x, hxN⟩ : ↥N)).1 hxfix
  rcases hprim P hPJ with hPbot | hPJeq
  · -- the trace is the base: the subgroup is everything
    left
    have hHtop : H.map (compositumRestrict N F⟮t⟯) = ⊤ := by
      have hfixbot : IntermediateField.fixedField (H.map (compositumRestrict N F⟮t⟯)) = ⊥ := by
        refine le_antisymm (fun x hx => ?_) bot_le
        have hxM : (x : Ω) ∈ M := (htrace x).1 hx
        have hxP : (x : Ω) ∈ P := ⟨hxM, x.2⟩
        rw [hPbot] at hxP
        obtain ⟨c, hc⟩ := hxP
        exact ⟨c, Subtype.ext hc⟩
      have := IntermediateField.fixingSubgroup_fixedField (H.map (compositumRestrict N F⟮t⟯))
      rw [hfixbot, IntermediateField.fixingSubgroup_bot] at this
      exact this.symm
    have hHfull : H = ⊤ := by
      refine le_antisymm le_top fun σ _ => ?_
      have hmem : compositumRestrict N F⟮t⟯ σ ∈ H.map (compositumRestrict N F⟮t⟯) := by
        rw [hHtop]
        exact Subgroup.mem_top _
      obtain ⟨σ', hσ', heq⟩ := hmem
      have : σ' = σ := hρinj heq
      rwa [this] at hσ'
    rw [← hMfixed, hHfull]
    have hbotfix : (⊥ : IntermediateField (↥F⟮t⟯) Ω).fixingSubgroup = ⊤ :=
      IntermediateField.fixingSubgroup_bot
    have := IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (↥F⟮t⟯) Ω)
    rwa [hbotfix] at this
  · -- the trace is `J`: the field contains `J(t)`
    right
    refine le_antisymm hM ?_
    rw [hJt]
    refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hxP : x ∈ P := by
      rw [hPJeq]
      exact hx
    exact hxP.1

end GaloisForLFunctions.HTGeometry

end
