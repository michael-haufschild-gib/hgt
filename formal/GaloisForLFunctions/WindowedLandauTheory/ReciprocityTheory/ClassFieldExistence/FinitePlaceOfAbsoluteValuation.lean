import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsoluteInertiaRestriction
import GaloisForLFunctions.HTGeometry.ValuationSubringInertiaDictionary
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! An absolute valuation determines a finite prime at each number-field
stage. Absolute inertia restricts onto inertia at the selected prime,
and absolute arithmetic Frobenius restricts to arithmetic Frobenius. -/

noncomputable section

open NumberField IsDedekindDomain WindowedLandauTheory.ConjugateSelfDual
open ReciprocityTheory.Gal GaloisForLFunctions.HTGeometry.ValuationInertia
open scoped Pointwise

namespace GlobalTheory.Reciprocity

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
  (A : ValuationSubring Ω)

private theorem integer_mem_absoluteValuation (x : 𝓞 L) : algebraMap (𝓞 L) Ω x ∈ A := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L Ω]
  exact mem_of_isIntegral_int A (IsIntegral.map (Algebra.ofId L Ω) x.isIntegral_coe)

private def absoluteValuationCentre : Ideal (𝓞 L) :=
  centerPrime A (integer_mem_absoluteValuation A)

private theorem mem_absoluteValuationCentre (x : 𝓞 L) :
    x ∈ absoluteValuationCentre (L := L) A ↔ A.valuation (algebraMap (𝓞 L) Ω x) < 1 :=
  A.valuation_lt_one_iff ⟨_, integer_mem_absoluteValuation A x⟩

variable {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

include h in
private theorem absoluteValuationCentre_liesOver :
    (absoluteValuationCentre (L := L) A).LiesOver v.asIdeal := by
  constructor
  symm
  apply Ideal.ext
  intro x
  change algebraMap (𝓞 K) (𝓞 L) x ∈ absoluteValuationCentre A ↔ x ∈ v.asIdeal
  rw [mem_absoluteValuationCentre, IsScalarTower.algebraMap_apply (𝓞 L) L Ω]
  change A.valuation (algebraMap L Ω (algebraMap K L (x : K))) < 1 ↔ x ∈ v.asIdeal
  rw [← IsScalarTower.algebraMap_apply K L Ω]
  exact h x

def finitePlaceAtAbsoluteValuation : HeightOneSpectrum (𝓞 L) :=
  let P := absoluteValuationCentre (L := L) A
  letI : P.LiesOver v.asIdeal := absoluteValuationCentre_liesOver A h
  ⟨P, centerPrime_isPrime A (integer_mem_absoluteValuation A),
    Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩

theorem finitePlaceAtAbsoluteValuation_liesOver :
    (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.LiesOver v.asIdeal :=
  absoluteValuationCentre_liesOver A h

private theorem mem_finitePlaceAtAbsoluteValuation (x : 𝓞 L) :
    x ∈ (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal ↔
      A.valuation (algebraMap L Ω (x : L)) < 1 := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 L) L Ω]
  exact mem_absoluteValuationCentre A x

theorem finitePlaceAtAbsoluteValuation_isPlaceOver :
    IsPlaceOver A (finitePlaceAtAbsoluteValuation (L := L) A h) :=
  fun x => (mem_finitePlaceAtAbsoluteValuation (L := L) A h x).symm

variable [IsAlgClosure K Ω] [IsGalois K L]

theorem restrictNormalHom_mem_stabilizer_of_mem_Dec {σ : Gal(Ω/K)} (hσ : σ ∈ Dec (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈
      MulAction.stabilizer Gal(L/K) (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal := by
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  let r : Gal(Ω/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  change r σ ∈ MulAction.stabilizer Gal(L/K) w.asIdeal
  apply MulAction.mem_stabilizer_iff.mpr
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change (r σ)⁻¹ • x ∈ w.asIdeal ↔ x ∈ w.asIdeal
  rw [← map_inv r]
  rw [mem_finitePlaceAtAbsoluteValuation, mem_finitePlaceAtAbsoluteValuation]
  change A.valuation (algebraMap L Ω (r σ⁻¹ (x : L))) < 1 ↔
    A.valuation (algebraMap L Ω (x : L)) < 1
  have hr := AlgEquiv.restrictNormal_commutes σ⁻¹ L (x : L)
  change algebraMap L Ω (r σ⁻¹ (x : L)) = σ⁻¹ (algebraMap L Ω (x : L)) at hr
  rw [hr]
  exact valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ) _

theorem restrictNormalHom_mem_inertia_of_mem_Ine {σ : Gal(Ω/K)} (hσ : σ ∈ Ine (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.inertia Gal(L/K) := by
  intro x
  apply (mem_finitePlaceAtAbsoluteValuation (L := L) A h _).mpr
  change A.valuation (algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ) (x : L) - (x : L))) < 1
  have hr := AlgEquiv.restrictNormal_commutes σ L (x : L)
  change algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ) (x : L)) =
    σ (algebraMap L Ω (x : L)) at hr
  rw [map_sub, hr]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (by
    rw [← IsScalarTower.algebraMap_apply (𝓞 L) L Ω]
    exact integer_mem_absoluteValuation A x))

theorem exists_Ine_restrictNormalHom_eq (τ : Gal(L/K))
    (hτ : τ ∈ (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal.inertia Gal(L/K)) :
    ∃ σ : Ine (F := K) A, AlgEquiv.restrictNormalHom L σ.val = τ := by
  obtain ⟨σ, hσ, he⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ (fun x => by
    rw [← map_sub]
    exact (mem_finitePlaceAtAbsoluteValuation (L := L) A h _).mp (hτ x))
  refine ⟨⟨σ, hσ⟩, AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_⟩
  exact (AlgEquiv.restrictNormal_commutes σ L x).trans (he x)

theorem restrictNormalHom_isArithFrobAt {σ : Gal(Ω/K)} (hσ : IsFrob A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal := by
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  intro x
  change (AlgEquiv.restrictNormalHom L σ) • x - x ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈ w.asIdeal
  rw [← Ideal.over_def w.asIdeal v.asIdeal]
  apply (mem_finitePlaceAtAbsoluteValuation (L := L) A h _).mpr
  change A.valuation (algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ) (x : L) - (x : L) ^ normV v)) < 1
  have hr := AlgEquiv.restrictNormal_commutes σ L (x : L)
  change algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ) (x : L)) =
    σ (algebraMap L Ω (x : L)) at hr
  rw [map_sub, map_pow, hr]
  apply hσ.2
  apply (A.valuation_le_one_iff _).mpr
  rw [← IsScalarTower.algebraMap_apply (𝓞 L) L Ω]
  exact integer_mem_absoluteValuation A x

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.restrictNormalHom_mem_stabilizer_of_mem_Dec
#print axioms GlobalTheory.Reciprocity.restrictNormalHom_mem_inertia_of_mem_Ine
#print axioms GlobalTheory.Reciprocity.exists_Ine_restrictNormalHom_eq
#print axioms GlobalTheory.Reciprocity.restrictNormalHom_isArithFrobAt
