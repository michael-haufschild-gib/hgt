import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinData
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SmoothWeilCharacterAbelianization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.SmoothArtinDescent

/-! Local Artin reciprocity at a number field's finite completion.
The geometric normalization sends arithmetic Frobenius of degree one
to valuation minus one. All smooth Weil characters descend. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GaloisForLFunctions.HTGeometry
open scoped WithZero

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

local notation "C" => CompactIdeleClassQuotient K
local notation "M" => maximalAbelianExtension K Ω
local notation "Fv" => v.adicCompletion K
local notation "ν" => tameValHom (Valued.v : Valuation Fv ℤᵐ⁰)

theorem eq_globalIdelicArtin_of_matchesFinite
    (a b : C →* Gal(M/K)) (ha : MatchesFiniteIdelicArtin K Ω a) (hb : MatchesFiniteIdelicArtin K Ω b) :
    a = b := by
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  apply injective_restrictAbPi
  funext V
  let L := (V : IntermediateField K Ω)
  letI : FiniteDimensional K L := V.2.1
  letI : IsAbelianGalois K L := V.2.2
  letI : NumberField L := NumberField.of_module_finite K L
  let f := finiteStageArtin K Ω a V
  let g := finiteStageArtin K Ω b V
  have h := finiteIdelicArtin_restrict_eq K L L f g
    (finiteStageArtin_isFiniteIdelicArtin K Ω a ha V) (finiteStageArtin_isFiniteIdelicArtin K Ω b hb V)
    (finiteStageArtin_diagonal K Ω a V) (finiteStageArtin_diagonal K Ω b V)
  change f y = g y
  rw [← h, MonoidHom.comp_apply]
  apply AlgEquiv.ext
  intro z
  exact (AlgEquiv.restrictNormal_commutes (f y) L z).symm

theorem existsUnique_localArtin (h : IsPlaceOver A v) :
    ∃! α : Weil h →* Fvˣ, IsLocalArtin K Ω α := by
  obtain ⟨a, hca, ha, -⟩ := exists_global_idelic_artin K Ω
  obtain ⟨b, hbs, hbd, hb⟩ := exists_inverse_arithmeticArtin_on_Weil K Ω a hca ha h
  let α : Weil h →* Fvˣ := b⁻¹
  have hαs : Function.Surjective α := by
    intro x
    obtain ⟨σ, hσ⟩ := hbs x⁻¹
    exact ⟨σ, by change (b σ)⁻¹ = x; rw [hσ, inv_inv]⟩
  have hαc : Continuous fun σ : Ine (F := K) A => α (ineIncl h σ) :=
    (continuous_inverseArtin_on_inertia K Ω a hca ha b hbd hb).inv
  have hαd (σ : Weil h) : Multiplicative.toAdd (ν (α σ)) = -deg σ := by
    change Multiplicative.toAdd (ν ((b σ)⁻¹)) = -deg σ
    rw [map_inv, hbd]
    rfl
  have hglob (σ : Weil h) : a (toCompactIdeleClassQuotient K (finiteEmbedding v (α σ)⁻¹)) =
      toMaxAb K Ω σ.val := by
    change a (toCompactIdeleClassQuotient K (finiteEmbedding v ((b σ)⁻¹)⁻¹)) = _
    rw [inv_inv]
    exact hb σ
  have hν : IsOpen ((ν).ker : Set Fvˣ) := by
    have he : (ν).ker = unitsLevel (K := K) v 0 := by
      ext x
      exact (unitsLevel_zero_iff_tameValHom_eq_one x).symm
    rw [he]
    exact isOpen_unitsLevel (K := K) v 0
  refine ⟨α, ⟨hαs, hαc, hαd, ?_, ?_⟩, ?_⟩
  · intro ξ hξ
    have hk : α.ker ≤ ξ.ker := by
      intro σ hσ
      apply MonoidHom.mem_ker.mpr
      apply smooth_weilCharacter_eq_one_of_toMaxAb_eq_one K Ω h ξ hξ σ
      rw [← hglob σ, MonoidHom.mem_ker.mp hσ, inv_one, map_one, map_one, map_one]
    let χ := α.liftOfSurjective hαs ⟨ξ, hk⟩
    have he : χ.comp α = ξ :=
      α.liftOfRightInverse_comp _ (Function.rightInverse_surjInv hαs) ⟨ξ, hk⟩
    exact ⟨χ, (isSmooth_comp_iff_of_degree α hαs hαc ν hν hαd χ).mp (he.symm ▸ hξ), he.symm⟩
  · intro a' ha' σ
    rw [eq_globalIdelicArtin_of_matchesFinite K Ω a' a ha' ha]
    exact hglob σ
  · intro a' ha'
    apply MonoidHom.ext
    intro σ
    apply inv_injective
    apply globalArtin_injective_finiteEmbedding a hca ha v
    exact (ha'.glob a ha σ).trans (hglob σ).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.existsUnique_localArtin
