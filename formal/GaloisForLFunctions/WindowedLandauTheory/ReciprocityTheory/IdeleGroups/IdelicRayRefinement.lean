import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayClass
import GaloisForLFunctions.RHTower.Artin.EveryRayClassCharacterIsInducedFromAPrimitiveCharacterOfItsConductor

/-! Refining the modulus enlarges the local congruence depths and
commutes with the native ray class reduction. -/

noncomputable section

open NumberField IsDedekindDomain WithZero UniqueFactorizationMonoid
open GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity.IdeleRay

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem idelesOneMod_le_of_refinement {m q : Modulus K} (hfin : q.fin ≤ m.fin)
    (hinf : m.inf ⊆ q.inf) : idelesOneMod q ≤ idelesOneMod m := by
  intro x hx
  obtain ⟨hf, hi⟩ := (mem_idelesOneMod q).mp hx
  refine (mem_idelesOneMod m).mpr ⟨fun v hv => ?_, fun w hw => hi w (hinf hw)⟩
  have hq : m.fin ∣ q.fin := Ideal.dvd_iff_le.mpr hfin
  have h := mem_unitsLevel.mp (hf v (hv.trans hq))
  have hm : FiniteMultiplicity v.asIdeal q.fin :=
    finiteMultiplicity_of_emultiplicity_eq_natCast
      (emultiplicity_eq_count_normalizedFactors v.prime.irreducible q.fin_ne_bot)
  have hdepth : exponent m v ≤ exponent q v :=
    hm.le_multiplicity_of_pow_dvd ((asIdeal_pow_exponent_dvd m v).trans hq)
  refine mem_unitsLevel.mpr ⟨h.1, h.2.trans ?_⟩
  rw [exp_le_exp]
  exact neg_le_neg (by exact_mod_cast hdepth)

theorem rayClassReduction_comp_toRayClass (q : Modulus K) {J : Ideal (𝓞 K)} (hJ : q.fin ≤ J) :
    (rayClassReduction q hJ).comp (toRayClass q) =
      toRayClass (divisorModulus q J hJ) := by
  let m := divisorModulus q J hJ
  have hle : idelesOneMod q ≤ idelesOneMod m := idelesOneMod_le_of_refinement hJ (by rfl)
  apply MonoidHom.ext
  intro x
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod q x
  let y : idelesOneMod q := ⟨diagonal K a * x, ha⟩
  let z : idelesOneMod m := ⟨y.val, hle y.2⟩
  have hy := toRayClass_normalized q a⁻¹ y
  have hz := toRayClass_normalized m a⁻¹ z
  change toRayClass q (diagonal K a⁻¹ * (diagonal K a * x)) = _ at hy
  change toRayClass m (diagonal K a⁻¹ * (diagonal K a * x)) = _ at hz
  rw [map_inv, inv_mul_cancel_left] at hy hz
  rw [MonoidHom.comp_apply, hy, rayClassReduction_rayClass, hz]
  rfl

end GlobalTheory.Reciprocity.IdeleRay
