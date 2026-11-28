import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentOfRayNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayCharacterOfArtinNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArtinFactorOnNormRefinement
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayFactorFromIdeals
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicArtinFactorFixedField

/-! A finite Artin factor for a norm pullback descends through a cyclic
extension. The faithful factor determines the upper field, and the
relative ideal norm description of the Artin kernel gives descent. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

section RefinedAgreement

variable {K L G : Type} {A : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [Group A]

private theorem rational_ray_factor_of_agreement_on_ideals {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (q : Modulus K) (hqd : (normModulus K d).fin ≤ q.fin)
    (a : IdeleGroup K →* G) (hd : ∀ u : Kˣ, a (diagonal K u) = 1)
    (ha : ∀ x : idelesOneMod q, a x.val = artinMap K L G (toFractionalIdeal x.val))
    (g : G →* A) (χ : RayClassGroup (normModulus K c) →* A)
    (hg : ∀ I : idealGroup (normModulus K d),
      g (artinMap K L G I.val) =
        (χ.comp (rationalRayReduction K hcd)) (rayClass (normModulus K d) I)) :
    g.comp a = χ.comp (toRayClass (normModulus K c)) := by
  calc
    g.comp a =
        (χ.comp (rationalRayReduction K hcd)).comp (toRayClass (normModulus K d)) :=
      artin_factor_of_agreement_on_ideals (normModulus K d) q hqd (Set.subset_univ _)
        a hd ha g (χ.comp (rationalRayReduction K hcd)) hg
    _ = χ.comp (toRayClass (normModulus K c)) := by
      rw [MonoidHom.comp_assoc, rationalRayReduction_comp_toRayClass]

end RefinedAgreement

variable {K E M : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Field M]
  [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  [FiniteDimensional K E] [FiniteDimensional E M]
  [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)] [IsAbelianGalois E M]
  {A : Type*} [Group A]

local notation "G" => (E ≃ₐ[K] E)
local notation "H" => (M ≃ₐ[E] M)
local instance : CommGroup G := IsCyclic.commGroup
local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }
local instance : Fintype G := Fintype.ofFinite _
local instance : Fintype H := Fintype.ofFinite _

private theorem isAbelianGalois_of_norm_factor {c : ℕ} [NeZero c]
    (f : IdeleGroup E →* H) (hf : IsFiniteIdelicArtin f) (ψ : H →* A)
    (hinj : Function.Injective ψ) (χ : RayClassGroup (normModulus K c) →* A)
    (hχ : ψ.comp f = (χ.comp (rayClassNorm K E c)).comp (toRayClass (normModulus E c))) :
    IsAbelianGalois K M := by
  letI : FiniteDimensional K M := FiniteDimensional.trans K E M
  letI : NumberField M := NumberField.of_module_finite E M
  let T := normalClosure K M (AlgebraicClosure M)
  letI : FiniteDimensional K T := normalClosure.is_finiteDimensional K M (AlgebraicClosure M)
  letI : NumberField T := NumberField.of_module_finite K T
  letI : Algebra E T := ((algebraMap M T).comp (algebraMap E M)).toAlgebra
  letI : IsScalarTower E M T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K E T := IsScalarTower.to₁₂₄ K E M T
  obtain ⟨m, hm, hp⟩ := hf
  let d := c * m.fin.absNorm
  letI : NeZero d := ⟨mul_ne_zero (NeZero.ne c) (fun h => m.fin_ne_bot
    (Ideal.absNorm_eq_zero_iff.mp h))⟩
  have hc : c ∣ d := dvd_mul_right _ _
  have hd := normModulus_fin_le_of_absNorm_dvd E m (dvd_mul_left m.fin.absNorm c)
  refine isAbelianGalois_of_norm_frobenius K E M T d (χ.comp (rationalRayReduction K hc)) ψ hinj ?_ ?_
  · intro v hv
    exact not_not.mp fun hu => hv (((hm v).mpr hu).trans (Ideal.dvd_iff_le.mpr hd))
  · intro w hw
    let J : idealGroup (normModulus E d) := ⟨idealUnit w.ne_bot, idealUnit_prime_mem_idealGroup _ hw⟩
    have hu : IsUnramifiedPrime E M H w :=
      not_not.mp fun hu => hw (((hm w).mpr hu).trans (Ideal.dvd_iff_le.mpr hd))
    have he := artin_factor_on_norm_refinement hc m hd f ψ χ hp hχ J
    change ψ (artinMap E M H (idealUnit w.ne_bot)) = _ at he
    rwa [artinMap_idealUnit_prime, frobeniusOrOne, if_pos hu] at he

section BaseFactor

variable [FiniteDimensional K M] [IsAbelianGalois K M] [NumberField M]

local notation "Γ" => Gal(M/K)
local instance : CommGroup Γ :=
  { (inferInstance : Group Γ) with mul_comm := IsMulCommutative.is_comm.comm }
local instance : Fintype Γ := Fintype.ofFinite _

private theorem exists_nonzero_common_multiple (a b c d e : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ a ∣ n ∧ b ∣ n ∧ c ∣ n ∧ d ∣ n ∧ e ∣ n :=
  ⟨a * b * c * d * e, mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) he,
    ⟨b * c * d * e, by ac_rfl⟩, ⟨a * c * d * e, by ac_rfl⟩, ⟨a * b * d * e, by ac_rfl⟩,
    ⟨a * b * c * e, by ac_rfl⟩, dvd_mul_left e _⟩

omit [Algebra E M] [IsScalarTower K E M] [FiniteDimensional E M] [IsAbelianGalois E M] in
private theorem exists_common_artin_refinement (q : Modulus K) (m : Modulus E) (c : ℕ)
    [NeZero c] : ∃ (d : ℕ) (hn : NeZero d), letI := hn
    c ∣ d ∧ (normModulus K d).fin ≤ q.fin ∧ (normModulus E d).fin ≤ m.fin ∧
      (∀ v, ¬ v.asIdeal ∣ (normModulus K d).fin → IsUnramifiedPrime K E G v) ∧
      (∀ v, ¬ v.asIdeal ∣ (normModulus K d).fin → IsUnramifiedPrime K M Γ v) ∧
      rayPrincipal (normModulus K d) ≤ (artinMap K E G).ker ∧
      rayPrincipal (normModulus K d) ≤ (artinMap K M Γ).ker := by
  obtain ⟨cE, hcE, hEu, hEr⟩ := exists_rayPrincipal_le_ker_artinMap K E G
  obtain ⟨cM, hcM, hMu, hMr⟩ := exists_rayPrincipal_le_ker_artinMap K M Γ
  letI := hcE
  letI := hcM
  obtain ⟨d, hd, hcd, hmd, hEd, hMd, hqd⟩ :=
    exists_nonzero_common_multiple c m.fin.absNorm cE cM q.fin.absNorm (NeZero.ne c)
      (fun h => m.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)) (NeZero.ne cE) (NeZero.ne cM)
      (fun h => q.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  letI : NeZero d := ⟨hd⟩
  have hE (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ (normModulus K d).fin) :
      IsUnramifiedPrime K E G v :=
    hEu v fun hv' => hv (((dvd_normModulus_fin_iff K cE v).mpr hv').trans
      (Ideal.dvd_iff_le.mpr (normModulus_fin_le_of_dvd K hEd)))
  have hM (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ (normModulus K d).fin) :
      IsUnramifiedPrime K M Γ v :=
    hMu v fun hv' => hv (((dvd_normModulus_fin_iff K cM v).mpr hv').trans
      (Ideal.dvd_iff_le.mpr (normModulus_fin_le_of_dvd K hMd)))
  exact ⟨d, inferInstance, hcd, normModulus_fin_le_of_absNorm_dvd K q hqd,
    normModulus_fin_le_of_absNorm_dvd E m hmd, hE, hM,
    (rayPrincipal_normModulus_le_of_dvd K hEd).trans hEr,
    (rayPrincipal_normModulus_le_of_dvd K hMd).trans hMr⟩

private theorem exists_ideal_factor_at_refinement {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (m : Modulus E) (hmd : (normModulus E d).fin ≤ m.fin)
    (hE : ∀ v, ¬ v.asIdeal ∣ (normModulus K d).fin → IsUnramifiedPrime K E G v)
    (hM : ∀ v, ¬ v.asIdeal ∣ (normModulus K d).fin → IsUnramifiedPrime K M Γ v)
    (hEr : rayPrincipal (normModulus K d) ≤ (artinMap K E G).ker)
    (hMr : rayPrincipal (normModulus K d) ≤ (artinMap K M Γ).ker)
    (f : IdeleGroup E →* H) (ψ : H →* A) (χ : RayClassGroup (normModulus K c) →* A)
    (hp : ∀ y : idelesOneMod m, f y.val = artinMap E M H (toFractionalIdeal y.val))
    (hχ : ψ.comp f = (χ.comp (rayClassNorm K E c)).comp (toRayClass (normModulus E c))) :
    ∃ g : Γ →* A, ∀ I : idealGroup (normModulus K d),
      g (artinMap K M Γ I.val) =
        (χ.comp (rationalRayReduction K hcd)) (rayClass (normModulus K d) I) := by
  let j : H →* Γ := AlgEquiv.restrictScalarsHom K
  have hj (σ : H) (x : M) : j σ • x = σ • x := rfl
  have he (J : idealGroup (normModulus E d)) :
      (χ.comp (rationalRayReduction K hcd)) (rayClassNorm K E d (rayClass (normModulus E d) J)) =
        ψ (artinMap E M H J.val) :=
    (artin_factor_on_norm_refinement hcd m hmd f ψ χ hp hχ J).symm
  exact exists_artin_factor_of_norm_factor K E M G H Γ j hj d hE hM hEr hMr
    (χ.comp (rationalRayReduction K hcd)) ψ he

private theorem exists_base_artin_factor_of_norm_factor {c : ℕ} [NeZero c]
    (f : IdeleGroup E →* H) (hf : IsFiniteIdelicArtin f) (ψ : H →* A)
    (χ : RayClassGroup (normModulus K c) →* A)
    (hχ : ψ.comp f = (χ.comp (rayClassNorm K E c)).comp (toRayClass (normModulus E c))) :
    ∃ (a : IdeleGroup K →* Γ) (g : Γ →* A),
      IsFiniteIdelicArtin a ∧ (∀ u : Kˣ, a (diagonal K u) = 1) ∧
        g.comp a = χ.comp (toRayClass (normModulus K c)) := by
  letI : DiscreteTopology Γ := krullTopology_discreteTopology_of_finiteDimensional K M
  obtain ⟨m, -, hp⟩ := hf
  obtain ⟨q, a, -, -, hd, hq, ha⟩ := exists_finite_idelic_artin K M Γ
  obtain ⟨d, hn, hcd, hqd, hmd, hE, hM, hEr, hMr⟩ :=
    exists_common_artin_refinement (E := E) (M := M) q m c
  letI := hn
  obtain ⟨g, hg⟩ := exists_ideal_factor_at_refinement hcd m hmd hE hM hEr hMr f ψ χ hp hχ
  have hga := rational_ray_factor_of_agreement_on_ideals hcd q hqd a hd ha g χ hg
  exact ⟨a, g, ⟨q, hq, ha⟩, hd, hga⟩

end BaseFactor

theorem exists_faithful_artin_factor_of_cyclic_norm_factor {c : ℕ} [NeZero c]
    (f : IdeleGroup E →* H) (hf : IsFiniteIdelicArtin f) (ψ : H →* A)
    (hinj : Function.Injective ψ) (χ : RayClassGroup (normModulus K c) →* A)
    (hχ : ψ.comp f = (χ.comp (rayClassNorm K E c)).comp (toRayClass (normModulus E c))) :
    letI : FiniteDimensional K M := FiniteDimensional.trans K E M
    ∃ (L : IntermediateField K M) (hL : IsAbelianGalois K L), letI := hL
      ∃ (a : IdeleGroup K →* Gal(L/K)) (g : Gal(L/K) →* A),
        Continuous a ∧ Function.Surjective a ∧ IsFiniteIdelicArtin a ∧
        Function.Injective g ∧ g.comp a = χ.comp (toRayClass (normModulus K c)) := by
  letI : FiniteDimensional K M := FiniteDimensional.trans K E M
  letI : IsAbelianGalois K M := isAbelianGalois_of_norm_factor f hf ψ hinj χ hχ
  letI : NumberField M := NumberField.of_module_finite E M
  obtain ⟨a, g, ha, hd, hg⟩ := exists_base_artin_factor_of_norm_factor f hf ψ χ hχ
  obtain ⟨L, hL, b, u, hb, hbs, hbA, hui, hu⟩ :=
    exists_faithful_artin_factor_of_factor a ha hd g
  exact ⟨L, hL, b, u, hb, hbs, hbA, hui, hu.trans hg⟩

end GlobalTheory.Reciprocity
