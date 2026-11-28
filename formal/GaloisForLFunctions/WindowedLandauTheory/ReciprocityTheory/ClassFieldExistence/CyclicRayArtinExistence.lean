import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclicNormArtinDescent
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeCyclotomicDescentField
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RootCharacterArtinFactor
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayNeighborhoods

/-! Cyclic ray characters have faithful finite idelic Artin factors.
Prime exponent is treated after adjoining the roots of unity. For composite
exponent, pass to the field for the p-th power of the character, where
the norm pullback has prime exponent. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped Cyclotomic IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay GlobalTheory.Kummer

variable {A : Type*} [CommGroup A] [IsCyclic A]

/-- A ray character is a faithful factor of the idelic Artin map of a
finite abelian extension. -/
def HasRayArtinFactor {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
    (χ : RayClassGroup (normModulus K c) →* A) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
    (_ : IsAbelianGalois K L),
    ∃ (f : IdeleGroup K →* Gal(L/K)) (g : Gal(L/K) →* A),
      Continuous f ∧ Function.Surjective f ∧ IsFiniteIdelicArtin f ∧
        Function.Injective g ∧ g.comp f = χ.comp (toRayClass (normModulus K c))

omit [IsCyclic A] in
private theorem hasRayArtinFactor_of_roots
    {K : Type} [Field K] [NumberField K] {p c : ℕ} [NeZero p] [NeZero c]
    [HasEnoughRootsOfUnity K p] (χ : RayClassGroup (normModulus K c) →* A)
    (hχ : ∀ x, χ x ^ p = 1) : HasRayArtinFactor χ := by
  let q := normModulus K c
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace (RayClassGroup q) := ⊥
  letI : DiscreteTopology (RayClassGroup q) := ⟨rfl⟩
  let θ := χ.comp (compactToRayClass q)
  have hθ : Continuous θ :=
    (continuous_of_discreteTopology : Continuous χ).comp (continuous_compactToRayClass q)
  obtain ⟨S, L, hL, f, g, hf, hs, ha, hi, hgf⟩ :=
    exists_artin_factor_of_roots θ hθ (fun x => hχ (compactToRayClass q x))
  exact ⟨L, inferInstance, inferInstance, inferInstance, hL, f, g, hf, hs, ha, hi, hgf⟩

omit [IsCyclic A] in
private theorem hasRayArtinFactor_of_norm_factor
    {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)]
    {c : ℕ} [NeZero c] (χ : RayClassGroup (normModulus K c) →* A)
    (hnorm : HasRayArtinFactor (χ.comp (rayClassNorm K E c))) : HasRayArtinFactor χ := by
  obtain ⟨M, _, _, _, _, f, ψ, -, -, hf, hinj, he⟩ := hnorm
  letI : Algebra K M := ((algebraMap E M).comp (algebraMap K E)).toAlgebra
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨L, hL, a, g, hc, hs, ha, hi, hg⟩ :=
    exists_faithful_artin_factor_of_cyclic_norm_factor f hf ψ hinj χ he
  letI : FiniteDimensional K M := FiniteDimensional.trans K E M
  exact ⟨L, inferInstance, inferInstance, inferInstance, hL, a, g, hc, hs, ha, hi, hg⟩

omit [IsCyclic A] in
private theorem hasRayArtinFactor_of_refinement
    {K : Type} [Field K] [NumberField K] {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (χ : RayClassGroup (normModulus K c) →* A)
    (h : HasRayArtinFactor (χ.comp (rationalRayReduction K hcd))) : HasRayArtinFactor χ := by
  obtain ⟨L, hF, hA, hfin, hGa, f, g, hf, hs, ha, hi, hg⟩ := h
  refine ⟨L, hF, hA, hfin, hGa, f, g, hf, hs, ha, hi, hg.trans ?_⟩
  rw [MonoidHom.comp_assoc, rationalRayReduction_comp_toRayClass]

omit [IsCyclic A] in
private theorem hasRayArtinFactor_of_prime_exponent
    {K : Type} [Field K] [NumberField K] {p c : ℕ} [NeZero c] (hp : p.Prime)
    (χ : RayClassGroup (normModulus K c) →* A) (hχ : ∀ x, χ x ^ p = 1) :
    HasRayArtinFactor χ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let E := CyclotomicField p K
  letI : HasEnoughRootsOfUnity E p := primeCyclotomicField_hasEnoughRootsOfUnity K p hp
  letI : IsCyclic (E ≃ₐ[K] E) := primeCyclotomicField_isCyclic K p hp
  letI : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  letI : IsGalois K E := IsCyclotomicExtension.isGalois {p} K E
  have h : HasRayArtinFactor (χ.comp (rayClassNorm K E c)) :=
    hasRayArtinFactor_of_roots _ (fun x => hχ (rayClassNorm K E c x))
  exact hasRayArtinFactor_of_norm_factor χ h

section PowerFactor

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsAbelianGalois K E]

local notation "G" => Gal(E/K)
local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }
local instance : Fintype G := Fintype.ofFinite _

omit [IsCyclic A] in
private theorem norm_pullback_pow_eq_one {p c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (m : Modulus K) (hm : (normModulus K d).fin ≤ m.fin)
    (f : IdeleGroup K →* G) (ψ : G →* A) (χ : RayClassGroup (normModulus K c) →* A)
    (hp : ∀ y : idelesOneMod m, f y.val = artinMap K E G (toFractionalIdeal y.val))
    (hψ : ψ.comp f = ((powMonoidHom p : A →* A).comp χ).comp (toRayClass (normModulus K c)))
    (x : RayClassGroup (normModulus E d)) :
    ((χ.comp (rationalRayReduction K hcd)).comp (rayClassNorm K E d)) x ^ p = 1 := by
  obtain ⟨J, rfl⟩ := QuotientGroup.mk'_surjective _ x
  let I := coprimeIdealNorm K E d J
  have h := artin_factor_on_ray_refinement (normModulus K d) m (normModulus K c)
    hm (normModulus_fin_le_of_dvd K hcd) (Set.subset_univ _) (by rfl)
    f ψ ((powMonoidHom p : A →* A).comp χ) hp hψ I
  have hn : artinMap K E G I.val = 1 := artinMap_idealNormHom K E G J.val
  exact h.symm.trans ((congrArg ψ hn).trans (map_one ψ))

private theorem hasRayArtinFactor_of_power_factor {p c : ℕ} [NeZero c] (hp : p.Prime)
    (χ : RayClassGroup (normModulus K c) →* A)
    (f : IdeleGroup K →* G) (ψ : G →* A) (hf : IsFiniteIdelicArtin f)
    (hi : Function.Injective ψ)
    (hψ : ψ.comp f = ((powMonoidHom p : A →* A).comp χ).comp (toRayClass (normModulus K c))) :
    HasRayArtinFactor χ := by
  letI : IsCyclic G := isCyclic_of_injective ψ hi
  obtain ⟨m, -, hm⟩ := hf
  let d := c * m.fin.absNorm
  letI : NeZero d := ⟨mul_ne_zero (NeZero.ne c)
    (fun h => m.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))⟩
  have hcd : c ∣ d := dvd_mul_right _ _
  have hdm : (normModulus K d).fin ≤ m.fin :=
    normModulus_fin_le_of_absNorm_dvd K m (dvd_mul_left m.fin.absNorm c)
  let χd := χ.comp (rationalRayReduction K hcd)
  let θ := χd.comp (rayClassNorm K E d)
  have hθ := norm_pullback_pow_eq_one (p := p) hcd m hdm f ψ χ hm hψ
  have h := hasRayArtinFactor_of_prime_exponent hp θ hθ
  exact hasRayArtinFactor_of_refinement hcd χ (hasRayArtinFactor_of_norm_factor χd h)

end PowerFactor

private theorem hasRayArtinFactor_of_power
    {K : Type} [Field K] [NumberField K] {p c : ℕ} [NeZero c] (hp : p.Prime)
    (χ : RayClassGroup (normModulus K c) →* A)
    (hpow : HasRayArtinFactor ((powMonoidHom p : A →* A).comp χ)) :
    HasRayArtinFactor χ := by
  obtain ⟨E, _, _, _, _, f, ψ, -, -, hf, hi, hg⟩ := hpow
  letI : NumberField E := NumberField.of_module_finite K E
  exact hasRayArtinFactor_of_power_factor hp χ f ψ hf hi hg

theorem hasRayArtinFactor_of_exponent
    {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
    (n : ℕ) (hn : 0 < n) (χ : RayClassGroup (normModulus K c) →* A)
    (hχ : ∀ x, χ x ^ n = 1) : HasRayArtinFactor χ := by
  induction n using Nat.strong_induction_on generalizing χ with
  | h n ih =>
    by_cases h : n = 1
    · apply hasRayArtinFactor_of_prime_exponent Nat.prime_two
      intro x
      have hx : χ x = 1 := by simpa only [h, pow_one] using hχ x
      rw [hx, one_pow]
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h
      apply hasRayArtinFactor_of_power hp χ
      apply ih (n / p) (Nat.div_lt_self hn hp.one_lt) (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
      intro x
      change (χ x ^ p) ^ (n / p) = 1
      rw [← pow_mul, Nat.mul_div_cancel' hpn]
      exact hχ x

end GlobalTheory.Reciprocity
