import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilGroupAtFinitePlace
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PrimitiveElement

/-! Restricting scalars along a finite extension embeds its Weil group
into the base Weil group and multiplies Weil degree by the residue degree. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Filter
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Topology

namespace GlobalTheory.Reciprocity

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  (hv : IsPlaceOver A v) (hw : IsPlaceOver A w)

private theorem normV_eq_pow_inertiaDeg [w.asIdeal.LiesOver v.asIdeal] :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  letI := v.isMaximal
  letI := w.isMaximal
  exact (Ideal.cardQuot_pow_inertiaDeg v.asIdeal w.asIdeal).symm

private theorem mem_Dec_restrictScalars {σ : Gal(Ω/L)} (hσ : σ ∈ Dec (F := L) A) :
    σ.restrictScalars K ∈ Dec (F := K) A :=
  mem_Dec.mpr (mem_Dec.mp hσ)

def inertiaRestrictScalars :
    Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).comp (Ine (F := L) A).subtype).codRestrict _
    fun σ => ⟨mem_Dec_restrictScalars σ.2.1, σ.2.2⟩

variable [w.asIdeal.LiesOver v.asIdeal]

private theorem actsAs_restrictScalars {σ : Gal(Ω/L)} {a b : ℕ}
    (hσ : ActsAs A (normV w) σ a b) :
    ActsAs A (normV v) (σ.restrictScalars K)
      (w.asIdeal.inertiaDeg (𝓞 K) * a) (w.asIdeal.inertiaDeg (𝓞 K) * b) := by
  refine ⟨mem_Dec_restrictScalars hσ.1, fun x hx => ?_⟩
  have h := hσ.2 x hx
  rwa [normV_eq_pow_inertiaDeg (v := v) (w := w), ← pow_mul, ← pow_mul] at h

def weilRestrictScalars : Weil hw →* Weil hv :=
  ((AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K)).comp (Weil hw).subtype).codRestrict _
    fun σ => by
      obtain ⟨a, b, hab⟩ := σ.2
      exact ⟨_, _, actsAs_restrictScalars hab⟩

@[simp] theorem weilRestrictScalars_ineIncl (σ : Ine (F := L) A) :
    weilRestrictScalars hv hw (ineIncl hw σ) = ineIncl hv (inertiaRestrictScalars σ) := rfl

theorem deg_weilRestrictScalars [IsAlgClosure K Ω] [IsAlgClosure L Ω] (σ : Weil hw) :
    deg (h := hv) (weilRestrictScalars hv hw σ) =
      (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) * deg (h := hw) σ := by
  obtain ⟨a, b, hab⟩ := σ.2
  have hu := actsAs_restrictScalars (v := v) hab
  rw [deg_eq (h := hv) (σ := weilRestrictScalars hv hw σ) hu, deg_eq (h := hw) (σ := σ) hab]
  push_cast
  exact (mul_sub _ _ _).symm

theorem continuous_absolute_restrictScalars [Algebra.IsIntegral K Ω] :
    Continuous ((AlgEquiv.restrictScalarsHom K : Gal(Ω/L) →* Gal(Ω/K))) := by
  apply continuous_of_continuousAt_one
  refine continuousAt_def.mpr fun U hU => ?_
  rw [map_one] at hU
  obtain ⟨B, hB, hBU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
  letI : FiniteDimensional K B := hB
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K B
  have hBgen : IntermediateField.adjoin K ({(x : Ω)} : Set Ω) = B := by
    exact (IntermediateField.lift_adjoin_simple (F := K) B x).symm.trans
      (by rw [hx, IntermediateField.lift_top])
  let F := IntermediateField.adjoin L ({(x : Ω)} : Set Ω)
  letI : FiniteDimensional L F := IntermediateField.adjoin.finiteDimensional
    ((Algebra.IsIntegral.isIntegral (R := K) (x : Ω)).tower_top (A := L))
  have hBF : B ≤ F.restrictScalars K := by
    rw [← hBgen, IntermediateField.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self L _)
  refine (krullTopology_mem_nhds_one_iff L Ω _).mpr ⟨F, inferInstance, fun σ hσ => ?_⟩
  apply hBU
  exact (B.mem_fixingSubgroup_iff _).mpr fun y hy =>
    (F.mem_fixingSubgroup_iff _).mp hσ y (hBF hy)

theorem continuous_inertiaRestrictScalars [Algebra.IsIntegral K Ω] :
    Continuous (inertiaRestrictScalars (K := K) (L := L) (A := A)) :=
  (continuous_absolute_restrictScalars.comp continuous_subtype_val).subtype_mk _

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.weilRestrictScalars
#print axioms GlobalTheory.Reciprocity.deg_weilRestrictScalars
#print axioms GlobalTheory.Reciprocity.continuous_inertiaRestrictScalars
