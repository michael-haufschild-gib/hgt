import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassModule

/-!
# Canonical module splitting of finite-stage idele classes

For a finite set `S` of rational finite places, the semilocal source states
that the idele-class group is (noncanonically) a product of the kernel of its
module with the positive reals.  The distinguished real place removes that
ambiguity: a positive real number defines an idele whose finite coordinates
are all one.  This gives a continuous multiplicative section of the module.

This file proves the resulting algebraic and topological product

`C_S ≃ ker(|·|_S) × ℝ₊ˣ`

unconditionally.  Compactness of the module-one factor, its Haar
disintegration, and the induced invariant-`L²` equivalence are separate
downstream theorems.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open scoped NNReal

/-- The idele-class module with codomain restricted to positive nonzero
real numbers, represented as units of `ℝ≥0`. -/
def fieldOneFiniteStageIdeleClassUnitModule
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S →* ℝ≥0ˣ :=
  (fieldOneFiniteStageIdeleClassModule S).toHomUnits

/-- Positive-real section at the idele level: use the positive real number
at the archimedean coordinate and one at every finite coordinate. -/
def fieldOneFiniteStagePositiveRealIdeleSection
    (S : Finset (HeightOneSpectrum ℤ)) :
    ℝ≥0ˣ →* FieldOneFiniteStageIdele S where
  toFun r :=
    (Units.map NNReal.toRealHom.toMonoidHom r, fun _ => 1)
  map_one' := by
    apply Prod.ext
    · simp
    · funext v
      simp
  map_mul' r s := by
    apply Prod.ext
    · simp
    · funext v
      simp

/-- Positive-real section of the finite-stage idele-class module. -/
def fieldOneFiniteStagePositiveRealClassSection
    (S : Finset (HeightOneSpectrum ℤ)) :
    ℝ≥0ˣ →* FieldOneFiniteStageIdeleClassGroup S :=
  (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S)).comp
    (fieldOneFiniteStagePositiveRealIdeleSection S)

/-- The positive-real class section is a right inverse of the unit-valued
idele-class module. -/
@[simp]
theorem fieldOneFiniteStageIdeleClassUnitModule_section
    (S : Finset (HeightOneSpectrum ℤ)) (r : ℝ≥0ˣ) :
    fieldOneFiniteStageIdeleClassUnitModule S
        (fieldOneFiniteStagePositiveRealClassSection S r) = r := by
  apply Units.ext
  change
    ‖((Units.map NNReal.toRealHom.toMonoidHom r : ℝˣ) : ℝ)‖₊ *
        ∏ _v : ↥S,
          ‖((1 : (_v.1.adicCompletion ℚ)ˣ) :
            _v.1.adicCompletion ℚ)‖₊ =
      (r : ℝ≥0)
  simp

/-- The finite-stage idele module is continuous. -/
theorem fieldOneFiniteStageModule_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageModule S) := by
  apply Continuous.mul
  · exact continuous_nnnorm.comp
      (Units.continuous_val.comp continuous_fst)
  · exact continuous_finsetProd _ fun v _ =>
      continuous_nnnorm.comp
        (Units.continuous_val.comp
          ((continuous_apply v).comp continuous_snd))

/-- The descended finite-stage idele-class module is continuous. -/
theorem fieldOneFiniteStageIdeleClassModule_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleClassModule S) := by
  rw [(QuotientGroup.isQuotientMap_mk
    (fieldOneFiniteStageSUnitImage S)).continuous_iff]
  change Continuous (fieldOneFiniteStageModule S)
  exact fieldOneFiniteStageModule_continuous S

/-- The unit-valued idele-class module is continuous. -/
theorem fieldOneFiniteStageIdeleClassUnitModule_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleClassUnitModule S) := by
  apply Continuous.of_coeHom_comp
  change Continuous (fieldOneFiniteStageIdeleClassModule S)
  exact fieldOneFiniteStageIdeleClassModule_continuous S

/-- The positive-real idele section is continuous. -/
theorem fieldOneFiniteStagePositiveRealIdeleSection_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStagePositiveRealIdeleSection S) := by
  apply Continuous.prodMk
  · exact Continuous.units_map _ NNReal.continuous_coe
  · exact continuous_pi fun _ => continuous_const

/-- The positive-real class section is continuous. -/
theorem fieldOneFiniteStagePositiveRealClassSection_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStagePositiveRealClassSection S) := by
  exact continuous_quotient_mk'.comp
    (fieldOneFiniteStagePositiveRealIdeleSection_continuous S)

/-- Finite-stage idele classes commute.  This is stated explicitly because
the quotient-group API only exposes the inherited `Group` structure here. -/
theorem fieldOneFiniteStageIdeleClassGroup_comm
    (S : Finset (HeightOneSpectrum ℤ))
    (c d : FieldOneFiniteStageIdeleClassGroup S) :
    c * d = d * c := by
  refine Quotient.inductionOn₂' c d ?_
  intro u w
  change QuotientGroup.mk (u * w) = QuotientGroup.mk (w * u)
  rw [mul_comm]

/-- Module-one finite-stage idele classes. -/
abbrev FieldOneFiniteStageModuleOneClass
    (S : Finset (HeightOneSpectrum ℤ)) :=
  (fieldOneFiniteStageIdeleClassUnitModule S).ker

/-- Canonical multiplicative splitting of the finite-stage idele-class
group into its module-one factor and the positive reals. -/
def fieldOneFiniteStageIdeleClassSplitMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S ≃*
      FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ where
  toFun c :=
    (⟨c *
        (fieldOneFiniteStagePositiveRealClassSection S
          (fieldOneFiniteStageIdeleClassUnitModule S c))⁻¹, by
      rw [MonoidHom.mem_ker]
      simp [fieldOneFiniteStageIdeleClassUnitModule_section]⟩,
      fieldOneFiniteStageIdeleClassUnitModule S c)
  invFun z :=
    z.1.1 * fieldOneFiniteStagePositiveRealClassSection S z.2
  left_inv c := by
    simp
  right_inv z := by
    have hk :
        fieldOneFiniteStageIdeleClassUnitModule S z.1.1 = 1 :=
      z.1.2
    apply Prod.ext
    · apply Subtype.ext
      simp [hk, fieldOneFiniteStageIdeleClassUnitModule_section]
    · change
        fieldOneFiniteStageIdeleClassUnitModule S
            (z.1.1 * fieldOneFiniteStagePositiveRealClassSection S z.2) =
          z.2
      rw [map_mul, hk,
        fieldOneFiniteStageIdeleClassUnitModule_section, one_mul]
  map_mul' c d := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      simp only [map_mul]
      rw [mul_inv_rev]
      let a := (fieldOneFiniteStagePositiveRealClassSection S
        (fieldOneFiniteStageIdeleClassUnitModule S c))⁻¹
      let b := (fieldOneFiniteStagePositiveRealClassSection S
        (fieldOneFiniteStageIdeleClassUnitModule S d))⁻¹
      change (c * d) * (b * a) = (c * a) * (d * b)
      rw [mul_assoc c d]
      rw [show b * a = a * b from
        fieldOneFiniteStageIdeleClassGroup_comm S b a]
      rw [show d * (a * b) = a * (d * b) by
        rw [← mul_assoc, fieldOneFiniteStageIdeleClassGroup_comm S d a,
          mul_assoc]]
      rw [← mul_assoc]
    · simp

/-- Canonical topological splitting
`C_S ≃ ker(|·|_S) × ℝ₊ˣ`. -/
def fieldOneFiniteStageIdeleClassSplitHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S ≃ₜ
      FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ where
  toEquiv := fieldOneFiniteStageIdeleClassSplitMulEquiv S
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        (continuous_id.mul
          ((fieldOneFiniteStagePositiveRealClassSection_continuous S).comp
            (fieldOneFiniteStageIdeleClassUnitModule_continuous S)).inv) _
    · exact fieldOneFiniteStageIdeleClassUnitModule_continuous S
  continuous_invFun := by
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((fieldOneFiniteStagePositiveRealClassSection_continuous S).comp
        continuous_snd)

end

end GaloisForLFunctions.RHTower
