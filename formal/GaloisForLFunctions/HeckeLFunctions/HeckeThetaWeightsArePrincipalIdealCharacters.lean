import GaloisForLFunctions.HeckeLFunctions.HeckeIdealThetaIsUnitPeriodic
import GaloisForLFunctions.HeckeLFunctions.ConePointsOfARayClassAreLatticeCosets
import GaloisForLFunctions.HeckeLFunctions.NonzeroIdealElementsAreGlobalUnitOrbits

/-!
# Theta weights recover principal-ideal Hecke characters

Finite residue weights and real parity signs reproduce the Hecke value of
any nonzero principal integral ideal. At noncoprime elements both sides
vanish. The selected inverse-class generators therefore contribute exactly
the product of the class ideal and base ideal character values.

Separating each real embedding into its sign and positive place magnitude
also identifies the arithmetic monomial used in the archimedean integral.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

omit [NumberField K] in
/-- A nonzero real embedding is its arithmetic sign times its place absolute value. -/
theorem real_embedding_eq_sign_mul_place (α : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    embedding_of_isReal w.2 (α : K) = ((signAt K α w : ℤ) : ℝ) * w.1 (α : K) := by
  have he : embedding_of_isReal w.2 (α : K) ≠ 0 := by simp
  have hn := norm_embedding_of_isReal w.2 (α : K)
  rw [Real.norm_eq_abs] at hn
  change embedding_of_isReal w.2 (α : K) =
    ((if 0 < embedding_of_isReal w.2 (α : K) then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) * w.1 (α : K)
  rcases he.lt_or_gt with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    rw [← hn, abs_of_neg hneg]
    ring
  · rw [if_pos hpos]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [← hn, abs_of_pos hpos]

/-- The actual real monomial splits into its sign character and positive place magnitudes. -/
theorem heckeRealMonomial_eq_sign_mul_placeProduct (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (α : Kˣ) :
    heckeRealMonomial 𝔪 ψ (HTGeometry.numberFieldMixedPlaceScale y (mixedEmbedding K (α : K))) =
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 α) : ℂ) *
        ∏ w : 𝔪.inf, ((Real.exp (-y w.1.1) * w.1.1 (α : K) : ℝ) : ℂ) ^ heckeParity 𝔪 ψ w := by
  rw [infiniteSignCharacter_eq_prod, ← Finset.prod_mul_distrib]
  unfold heckeRealMonomial
  apply Finset.prod_congr rfl
  intro w _
  change ((Real.exp (-y w.1.1) * embedding_of_isReal w.1.2 (α : K) : ℝ) : ℂ) ^ _ = _
  rw [real_embedding_eq_sign_mul_place α w.1, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_intCast, mul_pow, mul_pow]
  change _ = ((signAt K α w.1 : ℤ) : ℂ) ^ _ * _
  rw [Complex.ofReal_mul, mul_pow]
  ring

/-- Finite theta weight and the actual sign character recover the principal-ideal Hecke value. -/
theorem integralHeckeWeight_mul_infiniteSign_eq_heckeValue (ψ : HeckeCharacter 𝔪)
    (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a ≠ 0) :
    integralHeckeWeight 𝔪 ψ a *
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) =
        heckeValue 𝔪 ψ (Ideal.span {a}) := by
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (by rw [h, map_zero])
  have hspan : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 K)) := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha0
  by_cases hu : IsUnit (Ideal.Quotient.mk 𝔪.fin a)
  · have hp := not_mem_of_isUnit_mk 𝔪 hu
    let α : primeToUnits 𝔪 := ⟨Units.mk0 _ ha, mk0_mem_primeToUnits 𝔪 ha hp⟩
    have hgroup : idealUnit hspan ∈ idealGroup 𝔪 := by
      rw [idealUnit_span_eq ha hspan]
      exact (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mpr α.2
    have hred : reduce 𝔪 α = unitMod 𝔪 hp :=
      congrArg (fun p : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ) => p.1)
        (rayHom_algebraMap 𝔪 ha hp)
    have hw : integralHeckeWeight 𝔪 ψ a =
        (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 α) : ℂ) := by
      rw [hred]
      change finiteHeckeWeight 𝔪 ψ (Ideal.Quotient.mk 𝔪.fin a) = _
      rw [← coe_unitMod 𝔪 hp]
      exact finiteHeckeWeight_unit 𝔪 ψ _
    have hchar := congrArg (fun z : ℂˣ => (z : ℂ)) (character_rayClassOfElt_eq 𝔪 ψ α)
    simp only [Units.val_mul] at hchar
    rw [hw, ← hchar, heckeValue_of_mem 𝔪 ψ hspan hgroup]
    apply congrArg (fun c : RayClassGroup 𝔪 => (ψ c : ℂ))
    apply congrArg (rayClass 𝔪)
    exact Subtype.ext (idealUnit_span_eq ha hspan).symm
  · rw [integralHeckeWeight_eq_zero 𝔪 ψ a hu, zero_mul]
    symm
    apply heckeValue_of_not_mem
    rintro ⟨hI, hgroup⟩
    rw [idealUnit_span_eq ha hI] at hgroup
    have hp := (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mp hgroup
    apply hu
    apply isUnit_mk_of_forall_not_mem 𝔪
    intro v hv hav
    have he := hp v hv
    rw [Units.val_mk0, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at he
    have hl := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr hav
    rw [he] at hl
    exact lt_irrefl _ hl

/-- The arithmetic coefficient is the finite weight times the proved real parity signs. -/
theorem integralHeckeWeight_mul_parities_eq_heckeValue (ψ : HeckeCharacter 𝔪)
    (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a ≠ 0) :
    integralHeckeWeight 𝔪 ψ a *
      ∏ w : 𝔪.inf, ((signAtInf 𝔪 (Units.mk0 _ ha) w : ℤ) : ℂ) ^ heckeParity 𝔪 ψ w =
        heckeValue 𝔪 ψ (Ideal.span {a}) := by
  rw [← infiniteSignCharacter_eq_prod]
  exact integralHeckeWeight_mul_infiniteSign_eq_heckeValue 𝔪 ψ a ha

/-- The selected nonzero class generator remains nonzero in the number field. -/
theorem inverseClassGenerator_ne_zero_in_field (b : (Ideal (𝓞 K))⁰)
    (I : inverseClassIntegralIdeals b) :
    algebraMap (𝓞 K) K (inverseClassGenerator b I) ≠ 0 := by
  intro h
  exact (inverseClassGenerator_mem_ne_zero b I).2 (Subtype.ext h)

/-- The chosen class generator has precisely the product of the two ideal-character values. -/
theorem inverseClassGenerator_heckeCoefficient (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (I : inverseClassIntegralIdeals b) :
    integralHeckeWeight 𝔪 ψ (inverseClassGenerator b I) *
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪
        (Units.mk0 _ (inverseClassGenerator_ne_zero_in_field b I))) : ℂ) =
        heckeValue 𝔪 ψ (I : Ideal (𝓞 K)) * heckeValue 𝔪 ψ (b : Ideal (𝓞 K)) := by
  rw [integralHeckeWeight_mul_infiniteSign_eq_heckeValue, span_inverseClassGenerator,
    heckeValue_mul]

end GaloisForLFunctions.HeckeLFunctions
