import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup
import GaloisForLFunctions.RHTower.Artin.TheArtinMapOnIdealsKillsNorms
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

/-! Below a prime in a finite Galois extension, the prime of the
decomposition field has degree and ramification index one. The prime
of the inertia field is unramified. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open scoped IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

include K in
/-- The restriction of a prime to an intermediate field lies over the base prime. -/
theorem liesOver_under_intermediateField (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (E : IntermediateField K L) [NumberField E] :
    (w.under (𝓞 E)).asIdeal.LiesOver v.asIdeal := by
  constructor
  change v.asIdeal = (w.asIdeal.under (𝓞 E)).under (𝓞 K)
  rw [Ideal.under_under]
  exact Ideal.LiesOver.over (p := v.asIdeal) (P := w.asIdeal)

theorem split_at_decomposition_fixedField (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    let E := fixedField (MulAction.stabilizer Gal(L/K) w.asIdeal)
    letI := NumberField.of_module_finite K E
    let u := w.under (𝓞 E)
    u.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ u.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  let E := fixedField (MulAction.stabilizer Gal(L/K) w.asIdeal)
  letI : NumberField E := NumberField.of_module_finite K E
  let u := w.under (𝓞 E)
  letI : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  letI := w.isMaximal
  letI := u.isMaximal
  letI : IsDecompositionField K L w.asIdeal E :=
    inferInstanceAs (IsDecompositionField K L w.asIdeal (FixedPoints.intermediateField
      (F := K) (MulAction.stabilizer Gal(L/K) w.asIdeal) : IntermediateField K L))
  exact ⟨IsDecompositionField.ramificationIdx_eq (𝓞 K) K L w.asIdeal E (𝓞 E) u.asIdeal v.ne_bot,
    IsDecompositionField.inertiaDeg_eq (𝓞 K) K L w.asIdeal E (𝓞 E) u.asIdeal v.ne_bot⟩

private theorem finite_residue_of_heightOne {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Finite v.asIdeal.ResidueField := by
  letI := v.isMaximal
  letI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_surjective _ v.asIdeal.bijective_algebraMap_quotient_residueField.surjective

theorem unramified_at_inertia_fixedField (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    let E := fixedField (w.asIdeal.inertia Gal(L/K))
    letI := NumberField.of_module_finite K E
    (w.under (𝓞 E)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let I := w.asIdeal.inertia Gal(L/K)
  let E := fixedField I
  letI : NumberField E := NumberField.of_module_finite K E
  let u := w.under (𝓞 E)
  letI : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  letI := v.isMaximal
  letI := w.isMaximal
  letI := u.isMaximal
  letI : Finite v.asIdeal.ResidueField := finite_residue_of_heightOne v
  letI : Finite u.asIdeal.ResidueField := finite_residue_of_heightOne u
  letI : IsGaloisGroup I E L := IsGaloisGroup.subgroup Gal(L/K) K L I
  letI : IsGaloisGroup I (𝓞 E) (𝓞 L) := .of_isFractionRing I _ _ E L
  have hI : w.asIdeal.inertia I = ⊤ := top_unique fun σ _ => σ.2
  have h₁ := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal
  have h₂ := Ideal.card_inertia_eq_ramificationIdxIn (G := I) u.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)] at h₁
  rw [hI, Subgroup.card_top, Ideal.ramificationIdxIn_eq_ramificationIdx u.asIdeal w.asIdeal I] at h₂
  have h : w.asIdeal.ramificationIdx (𝓞 E) = w.asIdeal.ramificationIdx (𝓞 K) := h₂.symm.trans h₁
  have ht := Ideal.ramificationIdx_tower (R := 𝓞 K) u.asIdeal w.asIdeal
  rwa [h, right_eq_mul₀ (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'] at ht

omit [IsGalois K L]

variable [IsAbelianGalois K L]

local instance : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype Gal(L/K) := Fintype.ofFinite _

theorem isUnramifiedPrime_of_ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : w.asIdeal.ramificationIdx (𝓞 K) = 1) : IsUnramifiedPrime K L Gal(L/K) v := by
  letI := v.isMaximal
  letI := w.isMaximal
  letI : Finite v.asIdeal.ResidueField := finite_residue_of_heightOne v
  intro P hP hPV
  letI := hP
  letI := hPV
  apply Subgroup.eq_bot_of_card_eq
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal P,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K), hw]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.split_at_decomposition_fixedField
#print axioms GlobalTheory.Reciprocity.unramified_at_inertia_fixedField
#print axioms GlobalTheory.Reciprocity.isUnramifiedPrime_of_ramificationIdx_eq_one
