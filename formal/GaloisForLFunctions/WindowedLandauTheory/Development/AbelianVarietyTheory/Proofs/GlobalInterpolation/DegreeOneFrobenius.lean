import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteDegreeOneFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! To prescribe a Frobenius element, pass to the fixed field of its cyclic
subgroup and choose a prime in its Artin ray class. Prime norm makes the
Frobenius restrict to the base field without a residue-degree power. -/

noncomputable section

open scoped Classical NumberField nonZeroDivisors Pointwise
open NumberField IsDedekindDomain FractionalIdeal
open GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DegreeOneFrobenius

private theorem isPlaceOver_under {F Z Ω : Type} [Field F] [Field Z] [Field Ω]
    [NumberField F] [NumberField Z] [Algebra F Z] [Algebra Z Ω] [Algebra F Ω] [IsScalarTower F Z Ω]
    {w : HeightOneSpectrum (𝓞 Z)} {B : ValuationSubring Ω} (hB : IsPlaceOver B w) :
    IsPlaceOver B (w.under (𝓞 F)) := by
  intro x
  have h := hB (algebraMap (𝓞 F) (𝓞 Z) x)
  change B.valuation (algebraMap Z Ω (algebraMap F Z (x : F))) < 1 ↔
    x ∈ (w.under (𝓞 F)).asIdeal at h
  simpa only [← IsScalarTower.algebraMap_apply F Z Ω] using h

private theorem isFrob_under_of_prime_norm {F Z Ω : Type} [Field F] [Field Z] [Field Ω]
    [NumberField F] [NumberField Z] [Algebra F Z] [Algebra Z Ω] [Algebra F Ω] [IsScalarTower F Z Ω]
    {w : HeightOneSpectrum (𝓞 Z)} {B : ValuationSubring Ω} {σ : G Z Ω}
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hσ : IsFrob B (normV w) σ) :
    (Ideal.absNorm (w.under (𝓞 F)).asIdeal).Prime ∧ IsFrob B (normV (w.under (𝓞 F))) (σ.restrictScalars F) := by
  let v := w.under (𝓞 F)
  letI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  have h1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
  rw [h1, pow_one] at h
  refine ⟨h ▸ hp, ?_⟩
  have e : normV v = normV w := h
  rw [e]
  exact ⟨hσ.1, hσ.2⟩

private theorem isAlgClosure_of_tower {F Z Ω : Type} [Field F] [Field Z] [Field Ω]
    [Algebra F Z] [Algebra Z Ω] [Algebra F Ω] [IsScalarTower F Z Ω] [IsAlgClosure F Ω] :
    IsAlgClosure Z Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) Z⟩

/-- A finite Galois extension realizes every Frobenius element at a prime
of rational-prime norm away from any finite set of places. -/
theorem exists_frobenius_in_coset (F Ω : Type) [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L]
    (g : G F Ω) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ T ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ L.fixingSubgroup := by
  let γ := g.restrictNormal L
  let C := Subgroup.zpowers γ
  let Z := IntermediateField.fixedField C
  let γ₀ : C := ⟨γ, Subgroup.mem_zpowers _⟩
  letI : NumberField L := NumberField.of_module_finite F L
  letI : NumberField Z := NumberField.of_module_finite F Z
  letI : Fintype C := Fintype.ofFinite C
  letI : CommGroup C := IsCyclic.commGroup
  letI : IsGaloisGroup C Z L := IsGaloisGroup.subgroup (L ≃ₐ[F] L) F L C
  letI algebraZΩ : Algebra Z Ω := ((algebraMap L Ω).comp (algebraMap Z L)).toAlgebra
  letI towerZLΩ : IsScalarTower Z L Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI towerFZΩ : IsScalarTower F Z Ω := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IsScalarTower.algebraMap_apply F L Ω x).trans
      (congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply F Z L x)))
  letI closureZΩ := @isAlgClosure_of_tower F Z Ω inferInstance inferInstance inferInstance
    inferInstance algebraZΩ inferInstance towerFZΩ ‹IsAlgClosure F Ω›
  have hgen (u : C) : u ∈ Subgroup.zpowers γ₀ := by
    obtain ⟨n, hn⟩ := u.2
    exact ⟨n, Subtype.ext hn⟩
  obtain ⟨w, hw, hp, hur, hg⟩ := exists_cyclic_prime Z L C γ₀ hgen _ (finite_under_preimage hT)
  let Q := primeAbove Z L w
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q
  let V : HeightOneSpectrum (𝓞 L) := ⟨Q, (primeAbove_isMaximal Z L w).isPrime, hQ0⟩
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω V
  have he : V.under (𝓞 Z) = w := HeightOneSpectrum.ext (Q.over_def w.asIdeal).symm
  have hBw : IsPlaceOver (F := Z) B w := by
    rw [← he]
    exact @isPlaceOver_under Z L Ω inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance algebraZΩ towerZLΩ V B hB
  obtain ⟨s, hs⟩ := @exists_isFrob Z Ω inferInstance inferInstance inferInstance
    algebraZΩ closureZΩ B w hBw
  let σ := @AlgEquiv.restrictScalars F Z Ω Ω inferInstance inferInstance inferInstance inferInstance
    inferInstance algebraZΩ algebraZΩ inferInstance inferInstance towerFZΩ towerFZΩ s
  let δ := σ.restrictNormal L
  have hδ (x : L) : algebraMap L Ω (δ x) = σ (algebraMap L Ω x) :=
    AlgEquiv.restrictNormal_commutes σ L x
  have hmem : δ ∈ C := by
    rw [← IntermediateField.fixingSubgroup_fixedField C, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply (algebraMap L Ω).injective
    have h := s.commutes (⟨x, hx⟩ : Z)
    change σ (algebraMap L Ω x) = algebraMap L Ω x at h
    exact (hδ x).trans h
  let δ₀ : C := ⟨δ, hmem⟩
  letI : SMulCommClass C (𝓞 Z) (𝓞 L) := ⟨fun u a x => RingOfIntegers.ext (by
    change u.val (algebraMap Z L (a : Z) * (x : L)) = algebraMap Z L (a : Z) * u.val (x : L)
    have ha : u.val (algebraMap Z L (a : Z)) = algebraMap Z L (a : Z) :=
      (IntermediateField.mem_fixedField_iff C ((a : Z) : L)).mp (a : Z).2 u u.2
    rw [map_mul, ha])⟩
  have hFrob : IsArithFrobAt (𝓞 Z) δ₀ Q := by
    intro x
    change δ₀ • x - x ^ Nat.card (𝓞 Z ⧸ Q.under (𝓞 Z)) ∈ Q
    rw [show Q.under (𝓞 Z) = w.asIdeal from (Q.over_def w.asIdeal).symm]
    apply (hB _).mp
    have hx : algebraMap L Ω (x : L) ∈ B :=
      mem_of_isIntegral_int B (IsIntegral.map (Algebra.ofId L Ω) x.isIntegral_coe)
    have h := hs.2 _ ((B.valuation_le_one_iff _).mpr hx)
    change B.valuation (algebraMap L Ω (δ (x : L) - (x : L) ^ normV w)) < 1
    rwa [map_sub, map_pow, hδ]
  have heq : δ₀ = γ₀ := by
    have h0 := hFrob.mul_inv_mem_inertia (isArithFrobAt_frobeniusElement Z L C w)
    have hI : Q.inertia C = ⊥ := hur Q inferInstance inferInstance
    change δ₀ * (frobeniusElement Z L C w)⁻¹ ∈ Q.inertia C at h0
    rw [hI, Subgroup.mem_bot] at h0
    exact (mul_inv_eq_one.mp h0).trans hg
  obtain ⟨hpv, hsv⟩ := @isFrob_under_of_prime_norm F Z Ω inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance algebraZΩ inferInstance towerFZΩ w B s hp hs
  have hBv := @isPlaceOver_under F Z Ω inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance algebraZΩ inferInstance towerFZΩ w B hBw
  refine ⟨w.under (𝓞 F), hw, hpv, B, hBv, σ, hsv, ?_⟩
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  exact congrArg Subtype.val heq

end GlobalTheory.DegreeOneFrobenius
