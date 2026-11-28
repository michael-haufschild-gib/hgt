import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitRadicalReciprocity

/-! One finite radical field contains the roots of all global integer
units, by taking the empty set of finite places in the S-unit construction. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions

namespace GlobalTheory.Kummer

attribute [local instance] primeMulAction

variable {E K Ω : Type} [Field E] [NumberField E] [Field K] [NumberField K]
  [Field Ω] [IsAlgClosed Ω] [Algebra E K] [Algebra E Ω] [Algebra K Ω]
  [IsScalarTower E K Ω] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

theorem exists_finite_galois_contains_roots_of_integer_units :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧ IsAbelianGalois K M ∧
      ∀ (u : (𝓞 E)ˣ) {y : Ω}, y ^ n = algebraMap E Ω ((u : 𝓞 E) : E) → y ∈ M := by
  let S := sUnitPrimeSet K (∅ : Finset (HeightOneSpectrum (𝓞 K)))
  let Δ := sUnitRadicalClasses K Gal(K/K) S n
  refine ⟨radicalField Δ, inferInstance, radicalField_isAbelianGalois Δ, fun u y hy => ?_⟩
  let uK : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 E) (𝓞 K)).toMonoidHom u
  let a : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom uK
  have ha : Additive.ofMul a ∈ sUnits K Gal(K/K) S := by
    have h : Additive.ofMul a ∈ (unitsIncl K).range := ⟨Additive.ofMul uK, rfl⟩
    rw [← sUnits_inf_ker_divMap K Gal(K/K) S] at h
    exact h.1
  have hr : (a : PowerClasses K n) ∈ Δ :=
    ⟨Multiplicative.ofAdd (⟨Additive.ofMul a, ha⟩ : sUnits K Gal(K/K) S), rfl⟩
  have he : (a : K) = algebraMap E K ((u : 𝓞 E) : E) := by
    change algebraMap (𝓞 K) K (algebraMap (𝓞 E) (𝓞 K) (u : 𝓞 E)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 E) E K]
  exact mem_radicalField hr (by rwa [he, ← IsScalarTower.algebraMap_apply E K Ω])

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.exists_finite_galois_contains_roots_of_integer_units
