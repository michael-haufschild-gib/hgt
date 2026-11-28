import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeExponentKummerBound

/-! An abelian extension of exponent dividing n and degree equal to the
number of power classes contains every subextension of that exponent
in the same overfield. -/

noncomputable section

open IntermediateField Module

namespace GlobalTheory.Kummer

variable {F M : Type*} [Field F] [CharZero F] [Field M] [Algebra F M]
  [Algebra.IsAlgebraic F M] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity F n]
  [Finite (PowerClasses F n)]

theorem le_of_abelian_exponent_of_finrank_eq_powerClasses (R S : IntermediateField F M)
    [FiniteDimensional F R] [FiniteDimensional F S] [IsAbelianGalois F R] [IsAbelianGalois F S]
    (hR : ∀ σ : Gal(R/F), σ ^ n = 1) (hS : ∀ σ : Gal(S/F), σ ^ n = 1)
    (hrank : finrank F R = Nat.card (PowerClasses F n)) : S ≤ R := by
  let Ω := AlgebraicClosure F
  let j : M →ₐ[F] Ω := IsAlgClosed.lift
  let r := j.comp R.val
  let s := j.comp S.val
  let C := radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F n))
  letI : FiniteDimensional F C := radicalField_finiteDimensional Ω _
  letI : FiniteDimensional F r.fieldRange :=
    FiniteDimensional.of_injective r.equivFieldRange.symm.toLinearMap r.equivFieldRange.symm.injective
  have hr : r.fieldRange ≤ C := le_radicalField_top_of_exponent r hR
  have hs : s.fieldRange ≤ C := le_radicalField_top_of_exponent s hS
  have hd : finrank F r.fieldRange = finrank F C := by
    rw [← r.equivFieldRange.toLinearEquiv.finrank_eq, hrank]
    change Nat.card (PowerClasses F n) = finrank F (radicalField (Ω := Ω) (⊤ : Subgroup (PowerClasses F n)))
    rw [finrank_radicalField, Nat.card_congr Subgroup.topEquiv.toEquiv]
  have he : r.fieldRange = C := IntermediateField.eq_of_le_of_finrank_eq hr hd
  intro x hx
  obtain ⟨y, hy⟩ := (hs.trans he.ge) (show j x ∈ s.fieldRange from ⟨⟨x, hx⟩, rfl⟩)
  exact (j.injective hy : (y : M) = x) ▸ y.2

/-- A finite-exponent character kills automorphisms fixing the full radical field. -/
theorem character_eq_one_of_mem_fixingSubgroup_of_saturation
    [FiniteDimensional F M] [IsGalois F M] {H : Type*} [CommGroup H]
    (R : IntermediateField F M) [IsAbelianGalois F R]
    (hR : ∀ σ : Gal(R/F), σ ^ n = 1)
    (hrank : finrank F R = Nat.card (PowerClasses F n))
    (χ : Gal(M/F) →* H) (hχ : ∀ σ, χ σ ^ n = 1)
    {σ : Gal(M/F)} (hσ : σ ∈ R.fixingSubgroup) : χ σ = 1 := by
  let S := fixedField χ.ker
  letI : IsGalois F S := IsGalois.of_fixedField_normal_subgroup χ.ker
  let e := (IsGalois.normalAutEquivQuotient χ.ker).symm.trans (QuotientGroup.quotientKerEquivRange χ)
  letI : IsAbelianGalois F S := {
    is_comm.comm s t := e.injective (by rw [map_mul, map_mul, mul_comm]) }
  have hS (τ : Gal(S/F)) : τ ^ n = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    obtain ⟨z, hz⟩ := (e τ).2
    apply Subtype.ext
    change (e τ).val ^ n = 1
    rw [← hz]
    exact hχ z
  have hSR := le_of_abelian_exponent_of_finrank_eq_powerClasses R S hR hS hrank
  apply MonoidHom.mem_ker.mp
  rw [← fixingSubgroup_fixedField χ.ker]
  exact S.fixingSubgroup_antitone hSR hσ

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.le_of_abelian_exponent_of_finrank_eq_powerClasses

#print axioms GlobalTheory.Kummer.character_eq_one_of_mem_fixingSubgroup_of_saturation
