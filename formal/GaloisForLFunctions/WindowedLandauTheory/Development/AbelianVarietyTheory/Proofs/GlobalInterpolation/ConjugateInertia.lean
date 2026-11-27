import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! Conjugation transports inertia, wild inertia, and tame generators
between the extensions of conjugate places. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory.ConjugateInertia

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

/-- The valuation with its place transported by a field automorphism. -/
abbrev move (c : Ω ≃+* Ω) (A : ValuationSubring Ω) := A.comap c.symm.toRingHom

theorem valuation_move_lt_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (x : Ω) :
    (move c A).valuation x < 1 ↔ A.valuation (c.symm x) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff']
  change c.symm x ∈ A ∧ (x = 0 ∨ c.symm x⁻¹ ∉ A) ↔
    c.symm x ∈ A ∧ (c.symm x = 0 ∨ (c.symm x)⁻¹ ∉ A)
  rw [map_inv₀, map_eq_zero_iff _ c.symm.injective]

/-- Conjugation by a field automorphism preserving the base field acts on
the base field's absolute Galois group. -/
def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[E] Ω) where
  toFun σ :=
    { (c.symm.trans σ.toRingEquiv).trans c with
      commutes' := fun x => by
        obtain ⟨y, hy⟩ := hc x
        change c (σ (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hy, σ.commutes, ← hy, RingEquiv.apply_symm_apply] }
  map_one' := AlgEquiv.ext fun x => c.apply_symm_apply x
  map_mul' σ τ := AlgEquiv.ext fun x => by
    change c (σ (τ (c.symm x))) = c (σ (c.symm (c (τ (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem valuation_move_le_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (x : Ω) :
    (move c A).valuation x ≤ 1 ↔ A.valuation (c.symm x) ≤ 1 := by
  exact ((move c A).valuation_le_one_iff x).trans (A.valuation_le_one_iff (c.symm x)).symm

variable [NumberField E]

theorem conjHom_mem_Dec (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E,
      c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    {A : ValuationSubring Ω} {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ Dec (F := E) A) :
    conjHom c hc σ ∈ Dec (F := E) (move c A) := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  obtain ⟨z, rfl⟩ := (conjHom c hc σ).surjective x
  rw [show ((conjHom c hc σ)⁻¹ : Ω ≃ₐ[E] Ω) (conjHom c hc σ z) = z from
    (conjHom c hc σ).symm_apply_apply z]
  change c.symm z ∈ A ↔ c.symm (c (σ (c.symm z))) ∈ A
  rw [RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ]

theorem conjHom_mem_Ine (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E,
      c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    {A : ValuationSubring Ω} {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ Ine (F := E) A) :
    conjHom c hc σ ∈ Ine (F := E) (move c A) := by
  obtain ⟨hd, hi⟩ := mem_Ine.mp hσ
  refine mem_Ine.mpr ⟨conjHom_mem_Dec c hc hd, fun x hx => ?_⟩
  rw [valuation_move_lt_one, map_sub]
  change A.valuation (c.symm (c (σ (c.symm x))) - c.symm x) < 1
  rw [RingEquiv.symm_apply_apply]
  exact hi _ ((valuation_move_le_one c A x).mp hx)

theorem isFrob_conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E,
      c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    {A : ValuationSubring Ω} {q : ℕ} {σ : Ω ≃ₐ[E] Ω} (hσ : IsFrob A q σ) :
    IsFrob (move c A) q (conjHom c hc σ) := by
  refine ⟨conjHom_mem_Dec c hc hσ.1, fun x hx => ?_⟩
  rw [valuation_move_lt_one, map_sub, map_pow]
  change A.valuation (c.symm (c (σ (c.symm x))) - (c.symm x) ^ q) < 1
  rw [RingEquiv.symm_apply_apply]
  exact hσ.2 _ ((valuation_move_le_one c A x).mp hx)

omit [NumberField E] in
theorem conjHom_wild (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E,
      c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    {A : ValuationSubring Ω} {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ x : Ω, x ≠ 0 → A.valuation (σ x / x - 1) < 1)
    (y : Ω) (hy : y ≠ 0) : (move c A).valuation (conjHom c hc σ y / y - 1) < 1 := by
  rw [valuation_move_lt_one, map_sub, map_div₀, map_one]
  change A.valuation (c.symm (c (σ (c.symm y))) / c.symm y - 1) < 1
  rw [RingEquiv.symm_apply_apply]
  exact hσ _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

variable [IsAlgClosure E Ω]

omit [NumberField E] in
/-- Transporting the points fixed by an open subgroup gives an open
neighborhood in the Krull topology. -/
theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hf, hL⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  letI : FiniteDimensional E L := hf
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun j => c.symm (b j : Ω)
  letI : Finite S := (Set.finite_range _).to_subtype
  let M := IntermediateField.adjoin E S
  letI : FiniteDimensional E M := IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.mpr (Filter.mem_of_superset
    (M.fixingSubgroup_isOpen.mem_nhds (one_mem M.fixingSubgroup)) fun σ hσ => hL ?_)
  apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
  intro x hx
  have he : (conjHom c hc σ).toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap := by
    apply b.ext
    intro j
    change c (σ (c.symm (b j : Ω))) = (b j : Ω)
    rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
      (IntermediateField.subset_adjoin E S (Set.mem_range_self j)), c.apply_symm_apply]
  exact LinearMap.congr_fun he ⟨x, hx⟩

/-- A tame generator remains a tame generator at the transported valuation. -/
theorem tameGenAt_move (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y)
    {A : ValuationSubring Ω} {γ : Ω ≃ₐ[E] Ω} (hγ : TameGenAt A γ) :
    TameGenAt (move c A) (conjHom c hc γ) := by
  refine ⟨conjHom_mem_Ine c hc hγ.1, fun σ hσ => ?_⟩
  have hI := conjHom_mem_Ine c.symm hc' hσ
  have hA : move c.symm (move c A) = A := by
    ext x
    change c.symm (c x) ∈ A ↔ x ∈ A
    rw [RingEquiv.symm_apply_apply]
  rw [hA] at hI
  have hσ' : σ = conjHom c hc (conjHom c.symm hc' σ) := by
    ext x
    change σ x = c (c.symm (σ (c (c.symm x))))
    simp only [RingEquiv.apply_symm_apply]
  rw [hσ']
  refine map_mem_closure (continuous_conjHom c hc) (hγ.2 hI) fun τ hτ => ?_
  have hmem := Subgroup.mem_map_of_mem (conjHom c hc) hτ
  rw [MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨s, hs, rfl⟩
  rcases Set.mem_insert_iff.mp hs with rfl | hs
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjHom_wild c hc hs)

end GlobalTheory.ConjugateInertia
