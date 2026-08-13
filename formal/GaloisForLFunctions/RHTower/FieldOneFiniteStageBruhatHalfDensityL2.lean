import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatLogGrowth
import GaloisForLFunctions.RHTower.FieldOnePositiveUnitsLogHaar
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Connes--Marcolli half-density lands in `L²`

For the literal finite-stage Bruhat--Schwartz space, define

`E(f)(x) = |x|^(1/2) * Σ(f)(x)`.

The sharp logarithmic growth and uniform rapid decay proved in Lemma 2.29
give an integrable square majorant in logarithmic module coordinates.  This
file proves measurability, `L²` landing, and linearity on the actual split
idele-class carrier.  Dense range, the remaining assertion of Proposition
2.30, is proved downstream.
-/

open scoped NNReal ENNReal TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set TopologicalSpace

/-- Canonical norm-one representative of a module-one idele class. -/
def fieldOneFiniteStageAngularTorusRepresentative
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageNormOneTorus S :=
  (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm k

theorem fieldOneFiniteStageAngularTorusRepresentative_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageAngularTorusRepresentative S) :=
  (fieldOneFiniteStageNormOneTorusContinuousMulEquiv S).symm.continuous

private theorem fieldOneFiniteStageAngularTorusRepresentative_value_continuous
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S) :
    Continuous (fun k : FieldOneFiniteStageModuleOneClass S =>
      (((fieldOneFiniteStageAngularTorusRepresentative S k v).1 :
        (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)) := by
  exact Units.continuous_val.comp <|
    continuous_subtype_val.comp <|
      (continuous_apply v).comp
        (fieldOneFiniteStageAngularTorusRepresentative_continuous S)

/-- Periodization in the exact compact-times-logarithmic fundamental domain. -/
def fieldOneFiniteStageBruhatLogPeriodization
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ) : ℂ :=
  fieldOneFiniteStageBruhatPeriodization S x
    (fieldOneFiniteStageBruhatLogRayIdele S
      (fun v => (fieldOneFiniteStageAngularTorusRepresentative S z.1 v).1) z.2)

private theorem fieldOneFiniteStageBruhatOrbit_log_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (q : fieldOneSUnitSubgroup S) :
    Continuous (fun z : FieldOneFiniteStageModuleOneClass S × ℝ =>
      fieldOneFiniteStageBruhatOrbit S x
        (fieldOneFiniteStageBruhatLogRayIdele S
          (fun v => (fieldOneFiniteStageAngularTorusRepresentative S z.1 v).1) z.2) q) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simpa [fieldOneFiniteStageBruhatOrbit] using
        (continuous_const : Continuous
          (fun _ : FieldOneFiniteStageModuleOneClass S × ℝ => (0 : ℂ)))
  | tmul f phi =>
      simp only [fieldOneFiniteStageBruhatOrbit_tmul,
        fieldOneFiniteStageBruhatPureTensorOrbit,
        fieldOneFiniteStageBruhatLogRayIdele]
      apply Continuous.mul
      · exact f.continuous.comp (by fun_prop)
      · apply phi.1.continuous.comp
        exact continuous_pi fun v => continuous_const.mul <|
          (fieldOneFiniteStageAngularTorusRepresentative_value_continuous S v).comp
            continuous_fst
  | add x y hx hy =>
      convert hx.add hy using 1 <;>
        funext z <;> simp [fieldOneFiniteStageBruhatOrbit, map_add]

theorem fieldOneFiniteStageBruhatLogPeriodization_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatLogPeriodization S x) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  apply Measurable.tsum
  intro q
  exact (fieldOneFiniteStageBruhatOrbit_log_continuous S x q).measurable

/-- Absolute orbit periodization.  Unlike the norm of `Σ(f)`, this retains
the termwise information needed for Tonelli in Connes--Marcolli Lemma 2.32. -/
def fieldOneFiniteStageBruhatLogAbsolutePeriodization
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ) : ℝ :=
  ∑' q : fieldOneSUnitSubgroup S,
    ‖fieldOneFiniteStageBruhatOrbit S x
      (fieldOneFiniteStageBruhatLogRayIdele S
        (fun v => (fieldOneFiniteStageAngularTorusRepresentative S z.1 v).1) z.2) q‖

theorem fieldOneFiniteStageBruhatLogAbsolutePeriodization_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatLogAbsolutePeriodization S x) := by
  letI : Countable ℚˣ := Units.val_injective.countable
  letI : Countable (fieldOneSUnitSubgroup S) := Subtype.countable
  apply Measurable.tsum
  intro q
  exact (fieldOneFiniteStageBruhatOrbit_log_continuous S x q).norm.measurable

/-- Source half-density in logarithmic module coordinates. -/
def fieldOneFiniteStageBruhatLogHalfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ) : ℂ :=
  (Real.exp (z.2 / 2) : ℂ) * fieldOneFiniteStageBruhatLogPeriodization S x z

/-- Absolute half-density: `|x|^(1/2)` times the sum of the absolute values
of all orbit terms. -/
def fieldOneFiniteStageBruhatLogAbsoluteHalfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ) : ℝ :=
  Real.exp (z.2 / 2) *
    fieldOneFiniteStageBruhatLogAbsolutePeriodization S x z

theorem fieldOneFiniteStageBruhatLogHalfDensity_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatLogHalfDensity S x) := by
  exact (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_snd.div_const 2))).mul
    (fieldOneFiniteStageBruhatLogPeriodization_measurable S x)

theorem fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_measurable
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Measurable (fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x) := by
  exact (Real.measurable_exp.comp (measurable_snd.div_const 2)).mul
    (fieldOneFiniteStageBruhatLogAbsolutePeriodization_measurable S x)

/-- Product of probability Haar on the angular factor and Lebesgue measure on log-module. -/
def fieldOneFiniteStageSplitLogHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageModuleOneClass S × ℝ) :=
  (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod (volume : Measure ℝ)

private theorem integrableOn_abs_pow_mul_exp_Iic (n : ℕ) :
    IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp t) (Iic 0) := by
  have hglobal := HTGeometry.integrable_abs_pow_mul_exp_neg_abs n
    (by norm_num : (0 : ℝ) < 1)
  apply hglobal.integrableOn.congr_fun (fun t ht => ?_) measurableSet_Iic
  rw [abs_of_nonpos ht]
  congr 2
  ring_nf

private theorem integrableOn_exp_mul_neg_add_pow_Iic (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp t * (-t + 2) ^ n) (Iic 0) := by
  have hterm (i : ℕ) :
      IntegrableOn
        (fun t : ℝ => ((Nat.choose n i : ℝ) * 2 ^ (n - i)) *
          (|t| ^ i * Real.exp t)) (Iic 0) :=
    (integrableOn_abs_pow_mul_exp_Iic i).const_mul _
  have hsum : IntegrableOn
      (fun t : ℝ => ∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i : ℝ) * 2 ^ (n - i)) *
          (|t| ^ i * Real.exp t)) (Iic 0) := by
    change Integrable _ (volume.restrict (Iic 0))
    exact integrable_finsetSum _ fun i _ => hterm i
  apply hsum.congr_fun (fun t ht => ?_) measurableSet_Iic
  rw [abs_of_nonpos ht]
  rw [show (-t + 2) ^ n =
      ∑ i ∈ Finset.range (n + 1),
        (-t) ^ i * 2 ^ (n - i) * (Nat.choose n i : ℝ) by
    exact add_pow (-t) 2 n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def fieldOneFiniteStageBruhatHalfDensitySquareMajorant
    (S : Finset (HeightOneSpectrum ℤ)) (C D : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then
    C ^ 2 * (Real.exp t * (-t + 2) ^ (2 * Fintype.card ↥S))
  else
    D ^ 2 * Real.exp (-t)

private theorem fieldOneFiniteStageBruhatHalfDensitySquareMajorant_integrable
    (S : Finset (HeightOneSpectrum ℤ)) (C D : ℝ) :
    Integrable (fieldOneFiniteStageBruhatHalfDensitySquareMajorant S C D) := by
  let f : ℝ → ℝ := fun t =>
    C ^ 2 * (Real.exp t * (-t + 2) ^ (2 * Fintype.card ↥S))
  let g : ℝ → ℝ := fun t => D ^ 2 * Real.exp (-t)
  have hf : IntegrableOn f (Iic 0) :=
    (integrableOn_exp_mul_neg_add_pow_Iic (2 * Fintype.card ↥S)).const_mul _
  have hg : IntegrableOn g (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hpiece := Integrable.piecewise measurableSet_Iic hf (by
    simpa only [compl_Iic] using hg)
  apply hpiece.congr
  exact Filter.Eventually.of_forall fun t => by
    simp [fieldOneFiniteStageBruhatHalfDensitySquareMajorant, f, g,
      Set.piecewise, mem_Iic]

private theorem fieldOneFiniteStageBruhatLogHalfDensity_sq_le_majorant
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ z : FieldOneFiniteStageModuleOneClass S × ℝ,
        ‖fieldOneFiniteStageBruhatLogHalfDensity S x z‖ ^ 2 ≤
          fieldOneFiniteStageBruhatHalfDensitySquareMajorant S C D z.2 := by
  obtain ⟨C, hC, hsmall⟩ :=
    fieldOneFiniteStageBruhatTensor_uniform_logGrowth S x
  obtain ⟨D, hD, hlarge⟩ :=
    fieldOneFiniteStageBruhatTensor_uniform_rapidDecay S x 1
  refine ⟨C, D, hC, hD, fun z => ?_⟩
  let k := fieldOneFiniteStageAngularTorusRepresentative S z.1
  let P := fieldOneFiniteStageBruhatLogPeriodization S x z
  have hhalf :
      ‖fieldOneFiniteStageBruhatLogHalfDensity S x z‖ ^ 2 =
        Real.exp z.2 * ‖P‖ ^ 2 := by
    have hnormexp : ‖(Real.exp (z.2 / 2) : ℂ)‖ = Real.exp (z.2 / 2) := by
      exact (Complex.norm_real _).trans
        (Real.norm_of_nonneg (Real.exp_pos _).le)
    rw [fieldOneFiniteStageBruhatLogHalfDensity, norm_mul, hnormexp, mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hhalf]
  by_cases ht : z.2 ≤ 0
  · rw [fieldOneFiniteStageBruhatHalfDensitySquareMajorant, if_pos ht]
    have hP : ‖P‖ ≤ C * (-z.2 + 2) ^ Fintype.card ↥S :=
      hsmall k z.2 ht
    have hbase : 0 ≤ -z.2 + 2 := by linarith
    have hsq : ‖P‖ ^ 2 ≤ (C * (-z.2 + 2) ^ Fintype.card ↥S) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg P) hP 2
    calc
      Real.exp z.2 * ‖P‖ ^ 2 ≤
          Real.exp z.2 * (C * (-z.2 + 2) ^ Fintype.card ↥S) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = C ^ 2 *
          (Real.exp z.2 * (-z.2 + 2) ^ (2 * Fintype.card ↥S)) := by
        rw [mul_pow, ← pow_mul]
        ring
  · rw [fieldOneFiniteStageBruhatHalfDensitySquareMajorant, if_neg ht]
    have ht0 : 0 ≤ z.2 := le_of_lt (lt_of_not_ge ht)
    have hP : ‖P‖ ≤ D * Real.exp z.2 ^ (-(1 : ℝ)) :=
      hlarge k z.2 ht0
    have hsq : ‖P‖ ^ 2 ≤ (D * Real.exp z.2 ^ (-(1 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg P) hP 2
    calc
      Real.exp z.2 * ‖P‖ ^ 2 ≤
          Real.exp z.2 * (D * Real.exp z.2 ^ (-(1 : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = D ^ 2 * Real.exp (-z.2) := by
        rw [Real.rpow_neg_one, ← Real.exp_neg, mul_pow]
        have hexp : Real.exp z.2 * Real.exp (-z.2) = 1 := by
          rw [← Real.exp_add]
          simp
        calc
          Real.exp z.2 * (D ^ 2 * Real.exp (-z.2) ^ 2) =
              D ^ 2 * Real.exp (-z.2) *
                (Real.exp z.2 * Real.exp (-z.2)) := by ring
          _ = D ^ 2 * Real.exp (-z.2) := by rw [hexp, mul_one]

/-- The logarithmic Connes--Marcolli half-density is square-integrable. -/
theorem fieldOneFiniteStageBruhatLogHalfDensity_memLp
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatLogHalfDensity S x) 2
      (fieldOneFiniteStageSplitLogHaarMeasure S) := by
  rw [memLp_two_iff_integrable_sq_norm
    (fieldOneFiniteStageBruhatLogHalfDensity_measurable S x).aestronglyMeasurable]
  obtain ⟨C, D, hC, hD, hbound⟩ :=
    fieldOneFiniteStageBruhatLogHalfDensity_sq_le_majorant S x
  have hmajor :=
    (fieldOneFiniteStageBruhatHalfDensitySquareMajorant_integrable S C D).comp_snd
      (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
  apply hmajor.mono'
  · exact ((fieldOneFiniteStageBruhatLogHalfDensity_measurable S x).norm.pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound z

private theorem fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_sq_le_majorant
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ z : FieldOneFiniteStageModuleOneClass S × ℝ,
        ‖fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x z‖ ^ 2 ≤
          fieldOneFiniteStageBruhatHalfDensitySquareMajorant S C D z.2 := by
  obtain ⟨C, hC, hsmall⟩ :=
    fieldOneFiniteStageBruhatTensor_norm_tsum_uniform_logGrowth S x
  obtain ⟨D, hD, hlarge⟩ :=
    fieldOneFiniteStageBruhatTensor_norm_tsum_uniform_rapidDecay S x 1
  refine ⟨C, D, hC, hD, fun z => ?_⟩
  let k := fieldOneFiniteStageAngularTorusRepresentative S z.1
  let P := fieldOneFiniteStageBruhatLogAbsolutePeriodization S x z
  have hP0 : 0 ≤ P := by
    exact tsum_nonneg fun _ => norm_nonneg _
  have hhalf :
      ‖fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x z‖ ^ 2 =
        Real.exp z.2 * P ^ 2 := by
    rw [fieldOneFiniteStageBruhatLogAbsoluteHalfDensity, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hP0), mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hhalf]
  by_cases ht : z.2 ≤ 0
  · rw [fieldOneFiniteStageBruhatHalfDensitySquareMajorant, if_pos ht]
    have hP : P ≤ C * (-z.2 + 2) ^ Fintype.card ↥S :=
      hsmall k z.2 ht
    have hsq : P ^ 2 ≤ (C * (-z.2 + 2) ^ Fintype.card ↥S) ^ 2 :=
      pow_le_pow_left₀ hP0 hP 2
    calc
      Real.exp z.2 * P ^ 2 ≤
          Real.exp z.2 * (C * (-z.2 + 2) ^ Fintype.card ↥S) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = C ^ 2 *
          (Real.exp z.2 * (-z.2 + 2) ^ (2 * Fintype.card ↥S)) := by
        rw [mul_pow, ← pow_mul]
        ring
  · rw [fieldOneFiniteStageBruhatHalfDensitySquareMajorant, if_neg ht]
    have ht0 : 0 ≤ z.2 := le_of_lt (lt_of_not_ge ht)
    have hP : P ≤ D * Real.exp z.2 ^ (-(1 : ℝ)) :=
      hlarge k z.2 ht0
    have hsq : P ^ 2 ≤ (D * Real.exp z.2 ^ (-(1 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hP0 hP 2
    calc
      Real.exp z.2 * P ^ 2 ≤
          Real.exp z.2 * (D * Real.exp z.2 ^ (-(1 : ℝ))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = D ^ 2 * Real.exp (-z.2) := by
        rw [Real.rpow_neg_one, ← Real.exp_neg, mul_pow]
        have hexp : Real.exp z.2 * Real.exp (-z.2) = 1 := by
          rw [← Real.exp_add]
          simp
        calc
          Real.exp z.2 * (D ^ 2 * Real.exp (-z.2) ^ 2) =
              D ^ 2 * Real.exp (-z.2) *
                (Real.exp z.2 * Real.exp (-z.2)) := by ring
          _ = D ^ 2 * Real.exp (-z.2) := by rw [hexp, mul_one]

/-- The termwise-absolute logarithmic half-density is square-integrable. -/
theorem fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_memLp
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x) 2
      (fieldOneFiniteStageSplitLogHaarMeasure S) := by
  rw [memLp_two_iff_integrable_sq_norm
    (fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_measurable S x).aestronglyMeasurable]
  obtain ⟨C, D, hC, hD, hbound⟩ :=
    fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_sq_le_majorant S x
  have hmajor :=
    (fieldOneFiniteStageBruhatHalfDensitySquareMajorant_integrable S C D).comp_snd
      (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
  apply hmajor.mono'
  · exact ((fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_measurable S x).norm.pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound z

/-- Half-density on the split class carrier, defined by exact logarithmic pullback. -/
def fieldOneFiniteStageBruhatSplitHalfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) : ℂ :=
  fieldOneFiniteStageBruhatLogHalfDensity S x
    (z.1, fieldOnePositiveUnitsExpHomeomorph.symm z.2)

/-- Termwise-absolute half-density on the split idele-class carrier. -/
def fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) : ℝ :=
  fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x
    (z.1, fieldOnePositiveUnitsExpHomeomorph.symm z.2)

private theorem fieldOneFiniteStageSplitExpSymm_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving
      (Prod.map id fieldOnePositiveUnitsExpHomeomorph.symm)
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure)
      (fieldOneFiniteStageSplitLogHaarMeasure S) := by
  have hexp := fieldOnePositiveUnitsExp_measurePreserving
  change MeasurePreserving fieldOnePositiveUnitsExpHomeomorph.toMeasurableEquiv
    (volume : Measure ℝ) fieldOnePositiveUnitsLogHaarMeasure at hexp
  exact (MeasurePreserving.id
    (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)).prod
      hexp.symm

/-- The split half-density is in `L²` for canonical idele-class Haar measure. -/
theorem fieldOneFiniteStageBruhatSplitHalfDensity_memLp
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatSplitHalfDensity S x) 2
      (fieldOneFiniteStageSplitProductHaarMeasure S) := by
  have hlog := (fieldOneFiniteStageBruhatLogHalfDensity_memLp S x).comp_measurePreserving
    (fieldOneFiniteStageSplitExpSymm_measurePreserving S)
  have hlog' :
      MemLp (fieldOneFiniteStageBruhatSplitHalfDensity S x) 2
        ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
          fieldOnePositiveUnitsLogHaarMeasure) := by
    change MemLp (fun z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ =>
      fieldOneFiniteStageBruhatLogHalfDensity S x
        (z.1, fieldOnePositiveUnitsExpHomeomorph.symm z.2)) 2
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure) at hlog
    exact hlog
  rw [fieldOneFiniteStageSplitProductHaarMeasure,
    fieldOnePositiveUnitsHaar_eq_smul_logHaar, Measure.prod_smul_right]
  exact hlog'.smul_measure (by simp)

/-- The termwise-absolute split half-density belongs to the literal quotient
`L²`; this is the analytic input required for absolute correlation summability. -/
theorem fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity_memLp
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    MemLp (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity S x) 2
      (fieldOneFiniteStageSplitProductHaarMeasure S) := by
  have hlog :=
    (fieldOneFiniteStageBruhatLogAbsoluteHalfDensity_memLp S x).comp_measurePreserving
      (fieldOneFiniteStageSplitExpSymm_measurePreserving S)
  have hlog' :
      MemLp (fieldOneFiniteStageBruhatSplitAbsoluteHalfDensity S x) 2
        ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
          fieldOnePositiveUnitsLogHaarMeasure) := by
    change MemLp (fun z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ =>
      fieldOneFiniteStageBruhatLogAbsoluteHalfDensity S x
        (z.1, fieldOnePositiveUnitsExpHomeomorph.symm z.2)) 2
      ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
        fieldOnePositiveUnitsLogHaarMeasure) at hlog
    exact hlog
  rw [fieldOneFiniteStageSplitProductHaarMeasure,
    fieldOnePositiveUnitsHaar_eq_smul_logHaar, Measure.prod_smul_right]
  exact hlog'.smul_measure (by simp)

/-- The `L²` vector underlying Connes--Marcolli's map `E`. -/
def fieldOneFiniteStageBruhatHalfDensityL2
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    FieldOneFiniteStageSplitProductL2 S :=
  (fieldOneFiniteStageBruhatSplitHalfDensity_memLp S x).toLp
    (fieldOneFiniteStageBruhatSplitHalfDensity S x)

theorem fieldOneFiniteStageBruhatHalfDensityL2_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatHalfDensityL2 S x =ᵐ[
      fieldOneFiniteStageSplitProductHaarMeasure S]
        fieldOneFiniteStageBruhatSplitHalfDensity S x :=
  (fieldOneFiniteStageBruhatSplitHalfDensity_memLp S x).coeFn_toLp

theorem fieldOneFiniteStageBruhatPeriodization_smul
    (S : Finset (HeightOneSpectrum ℤ)) (c : ℂ)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatPeriodization S (c • x) u =
      c * fieldOneFiniteStageBruhatPeriodization S x u := by
  rw [fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization]
  have hsummable := summable_norm_iff.mp
    (fieldOneFiniteStageBruhatOrbit_summable S x u)
  calc
    (∑' q, fieldOneFiniteStageBruhatOrbit S (c • x) u q) =
        ∑' q, c • fieldOneFiniteStageBruhatOrbit S x u q := by
      apply tsum_congr
      intro q
      simp [fieldOneFiniteStageBruhatOrbit]
    _ = c • ∑' q, fieldOneFiniteStageBruhatOrbit S x u q :=
      hsummable.tsum_const_smul c
    _ = c * ∑' q, fieldOneFiniteStageBruhatOrbit S x u q := by rfl

theorem fieldOneFiniteStageBruhatSplitHalfDensity_add
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSplitHalfDensity S (x + y) =
      fieldOneFiniteStageBruhatSplitHalfDensity S x +
        fieldOneFiniteStageBruhatSplitHalfDensity S y := by
  funext z
  simp only [fieldOneFiniteStageBruhatSplitHalfDensity,
    fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization_add, Pi.add_apply]
  ring

theorem fieldOneFiniteStageBruhatSplitHalfDensity_smul
    (S : Finset (HeightOneSpectrum ℤ)) (c : ℂ)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSplitHalfDensity S (c • x) =
      c • fieldOneFiniteStageBruhatSplitHalfDensity S x := by
  funext z
  simp only [fieldOneFiniteStageBruhatSplitHalfDensity,
    fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization,
    fieldOneFiniteStageBruhatPeriodization_smul, Pi.smul_apply]
  ring

/-- Connes--Marcolli's half-density map `E` as a genuine linear map into `L²`. -/
def fieldOneFiniteStageBruhatHalfDensityLinearMap
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageSplitProductL2 S where
  toFun := fieldOneFiniteStageBruhatHalfDensityL2 S
  map_add' x y := by
    apply Lp.ext
    filter_upwards [
      fieldOneFiniteStageBruhatHalfDensityL2_ae S (x + y),
      fieldOneFiniteStageBruhatHalfDensityL2_ae S x,
      fieldOneFiniteStageBruhatHalfDensityL2_ae S y,
      Lp.coeFn_add (fieldOneFiniteStageBruhatHalfDensityL2 S x)
        (fieldOneFiniteStageBruhatHalfDensityL2 S y)] with z hxy hx hy hadd
    have hadd' :
        ((fieldOneFiniteStageBruhatHalfDensityL2 S x +
          fieldOneFiniteStageBruhatHalfDensityL2 S y) :
          FieldOneFiniteStageSplitProductL2 S) z =
          fieldOneFiniteStageBruhatHalfDensityL2 S x z +
            fieldOneFiniteStageBruhatHalfDensityL2 S y z := by
      simpa using hadd
    calc
      fieldOneFiniteStageBruhatHalfDensityL2 S (x + y) z =
          fieldOneFiniteStageBruhatSplitHalfDensity S (x + y) z := hxy
      _ = fieldOneFiniteStageBruhatSplitHalfDensity S x z +
          fieldOneFiniteStageBruhatSplitHalfDensity S y z :=
        congrFun (fieldOneFiniteStageBruhatSplitHalfDensity_add S x y) z
      _ = fieldOneFiniteStageBruhatHalfDensityL2 S x z +
          fieldOneFiniteStageBruhatHalfDensityL2 S y z := by rw [← hx, ← hy]
      _ = (fieldOneFiniteStageBruhatHalfDensityL2 S x +
          fieldOneFiniteStageBruhatHalfDensityL2 S y) z := hadd'.symm
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [
      fieldOneFiniteStageBruhatHalfDensityL2_ae S (c • x),
      fieldOneFiniteStageBruhatHalfDensityL2_ae S x,
      Lp.coeFn_smul c (fieldOneFiniteStageBruhatHalfDensityL2 S x)] with z hcx hx hsmul
    have hsmul' :
        (c • fieldOneFiniteStageBruhatHalfDensityL2 S x :
          FieldOneFiniteStageSplitProductL2 S) z =
          c • fieldOneFiniteStageBruhatHalfDensityL2 S x z := by
      simpa using hsmul
    calc
      fieldOneFiniteStageBruhatHalfDensityL2 S (c • x) z =
          fieldOneFiniteStageBruhatSplitHalfDensity S (c • x) z := hcx
      _ = c • fieldOneFiniteStageBruhatSplitHalfDensity S x z :=
        congrFun (fieldOneFiniteStageBruhatSplitHalfDensity_smul S c x) z
      _ = c • fieldOneFiniteStageBruhatHalfDensityL2 S x z := by rw [← hx]
      _ = (c • fieldOneFiniteStageBruhatHalfDensityL2 S x) z := hsmul'.symm

end

end GaloisForLFunctions.RHTower
