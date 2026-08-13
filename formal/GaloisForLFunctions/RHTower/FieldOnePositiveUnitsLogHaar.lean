import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassHaarSplitting
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Logarithmic Haar coordinates on positive units

Connes--Marcolli Proposition 2.30 uses the factor `ℝ₊ˣ` with multiplicative Haar
measure.  This file proves, without a normalization convention hidden in notation,
that the canonical Haar measure on `ℝ≥0ˣ` is a strictly positive finite scalar
multiple of the pushforward of Lebesgue measure by the exponential map.

The intermediate `Multiplicative ℝ` construction is needed because `exp` is a
group homomorphism from addition to multiplication, whereas Haar transport in
mathlib is stated between groups carrying the same operation syntax.
-/

open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Set TopologicalSpace

noncomputable instance fieldOneMultiplicativeRealMeasurableSpace :
    MeasurableSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasurableSpace ℝ)

noncomputable instance fieldOneMultiplicativeRealBorelSpace :
    BorelSpace (Multiplicative ℝ) :=
  inferInstanceAs (BorelSpace ℝ)

/-- Identity homeomorphism, with the target carrying multiplication induced by addition. -/
def fieldOneMultiplicativeRealHomeomorph : ℝ ≃ₜ Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd x
  invFun x := Multiplicative.toAdd x
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- Lebesgue measure on the multiplicative presentation of the additive real line. -/
def fieldOneMultiplicativeRealHaarMeasure : Measure (Multiplicative ℝ) :=
  Measure.map fieldOneMultiplicativeRealHomeomorph (volume : Measure ℝ)

instance fieldOneMultiplicativeRealHaar_isHaar :
    IsHaarMeasure fieldOneMultiplicativeRealHaarMeasure where
  lt_top_of_isCompact K hK := by
    rw [fieldOneMultiplicativeRealHaarMeasure,
      Measure.map_apply fieldOneMultiplicativeRealHomeomorph.measurable hK.measurableSet]
    have hpre : IsCompact (fieldOneMultiplicativeRealHomeomorph ⁻¹' K) := by
      simpa only [Homeomorph.image_symm] using
        hK.image fieldOneMultiplicativeRealHomeomorph.symm.continuous
    exact hpre.measure_lt_top
  open_pos U hU hUne := by
    rw [fieldOneMultiplicativeRealHaarMeasure,
      Measure.map_apply fieldOneMultiplicativeRealHomeomorph.measurable hU.measurableSet]
    exact (hU.preimage fieldOneMultiplicativeRealHomeomorph.continuous).measure_ne_zero volume
      (hUne.preimage fieldOneMultiplicativeRealHomeomorph.surjective)
  toIsMulLeftInvariant := by
    constructor
    intro g
    rw [fieldOneMultiplicativeRealHaarMeasure,
      Measure.map_map (measurable_const_mul g) fieldOneMultiplicativeRealHomeomorph.measurable]
    calc
      Measure.map ((g * ·) ∘ fieldOneMultiplicativeRealHomeomorph) volume =
          Measure.map fieldOneMultiplicativeRealHomeomorph
            (Measure.map (Multiplicative.toAdd g + ·) volume) := by
        rw [Measure.map_map fieldOneMultiplicativeRealHomeomorph.measurable
          (measurable_const_add (Multiplicative.toAdd g))]
        congr 1
      _ = Measure.map fieldOneMultiplicativeRealHomeomorph volume := by
        rw [map_add_left_eq_self]

/-- Exponential coordinates as a homeomorphism `ℝ ≃ ℝ≥0ˣ`. -/
def fieldOnePositiveUnitsExpHomeomorph : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm

/-- Exponential coordinates as a topological group isomorphism. -/
def fieldOnePositiveUnitsLogContinuousMulEquiv : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ where
  toFun t := fieldOnePositiveUnitsExpHomeomorph (Multiplicative.toAdd t)
  invFun u := Multiplicative.ofAdd (fieldOnePositiveUnitsExpHomeomorph.symm u)
  left_inv t := by simp
  right_inv u := by simp
  map_mul' x y := by
    apply Units.ext
    apply NNReal.eq
    change Real.exp (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      Real.exp (Multiplicative.toAdd x) * Real.exp (Multiplicative.toAdd y)
    exact Real.exp_add _ _
  continuous_toFun := fieldOnePositiveUnitsExpHomeomorph.continuous.comp continuous_id
  continuous_invFun := fieldOnePositiveUnitsExpHomeomorph.symm.continuous.comp continuous_id

/-- Multiplicative Haar measure in exact logarithmic coordinates. -/
def fieldOnePositiveUnitsLogHaarMeasure : Measure ℝ≥0ˣ :=
  Measure.map fieldOnePositiveUnitsExpHomeomorph (volume : Measure ℝ)

private theorem fieldOnePositiveUnitsLogHaarMeasure_eq_groupMap :
    fieldOnePositiveUnitsLogHaarMeasure =
      Measure.map fieldOnePositiveUnitsLogContinuousMulEquiv
        fieldOneMultiplicativeRealHaarMeasure := by
  rw [fieldOnePositiveUnitsLogHaarMeasure, fieldOneMultiplicativeRealHaarMeasure,
    show (fieldOnePositiveUnitsLogContinuousMulEquiv : Multiplicative ℝ → ℝ≥0ˣ) =
      fieldOnePositiveUnitsLogContinuousMulEquiv.toHomeomorph from rfl]
  rw [Measure.map_map fieldOnePositiveUnitsLogContinuousMulEquiv.continuous.measurable
    fieldOneMultiplicativeRealHomeomorph.measurable]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun _ => rfl

instance fieldOnePositiveUnitsLogHaar_isHaar :
    IsHaarMeasure fieldOnePositiveUnitsLogHaarMeasure := by
  rw [fieldOnePositiveUnitsLogHaarMeasure_eq_groupMap]
  exact fieldOnePositiveUnitsLogContinuousMulEquiv.isHaarMeasure_map
    fieldOneMultiplicativeRealHaarMeasure

/-- `exp` is measure preserving from Lebesgue measure to logarithmic Haar measure. -/
theorem fieldOnePositiveUnitsExp_measurePreserving :
    MeasurePreserving fieldOnePositiveUnitsExpHomeomorph
      (volume : Measure ℝ) fieldOnePositiveUnitsLogHaarMeasure :=
  fieldOnePositiveUnitsExpHomeomorph.measurable.measurePreserving _

/-- Canonical positive-unit Haar is a finite scalar multiple of logarithmic Haar. -/
theorem fieldOnePositiveUnitsHaar_eq_smul_logHaar :
    fieldOnePositiveUnitsHaarMeasure =
      haarScalarFactor fieldOnePositiveUnitsHaarMeasure fieldOnePositiveUnitsLogHaarMeasure •
        fieldOnePositiveUnitsLogHaarMeasure :=
  isMulLeftInvariant_eq_smul _ _

/-- Logarithmic Haar is a finite scalar multiple of canonical positive-unit Haar. -/
theorem fieldOnePositiveUnitsLogHaar_eq_smul_haar :
    fieldOnePositiveUnitsLogHaarMeasure =
      haarScalarFactor fieldOnePositiveUnitsLogHaarMeasure fieldOnePositiveUnitsHaarMeasure •
        fieldOnePositiveUnitsHaarMeasure :=
  isMulLeftInvariant_eq_smul _ _

theorem fieldOnePositiveUnitsHaar_logScalar_pos :
    0 < haarScalarFactor fieldOnePositiveUnitsHaarMeasure fieldOnePositiveUnitsLogHaarMeasure :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem fieldOnePositiveUnitsLogHaar_haarScalar_pos :
    0 < haarScalarFactor fieldOnePositiveUnitsLogHaarMeasure fieldOnePositiveUnitsHaarMeasure :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Membership in `Lᵖ` is independent of the two exact Haar normalizations. -/
theorem memLp_fieldOnePositiveUnitsHaar_iff_logHaar
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ≥0∞} {f : ℝ≥0ˣ → E} :
    MemLp f p fieldOnePositiveUnitsHaarMeasure ↔
      MemLp f p fieldOnePositiveUnitsLogHaarMeasure := by
  constructor
  · intro hf
    rw [fieldOnePositiveUnitsLogHaar_eq_smul_haar]
    exact hf.smul_measure (by simp)
  · intro hf
    rw [fieldOnePositiveUnitsHaar_eq_smul_logHaar]
    exact hf.smul_measure (by simp)

end

end GaloisForLFunctions.RHTower
