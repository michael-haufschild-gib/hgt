import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The value of relative entropy between countable laws

On a countable measurable space with measurable singletons, a law with everywhere positive atoms
dominates every other law, its Radon--Nikodym derivative is the pointwise mass ratio, and the
Kullback--Leibler divergence is the absolutely convergent atom series
`∑ Q{a} log (Q{a}/P{a})`.  This is the exact-value companion to the finiteness test
`discretePMF_klDiv_ne_top`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory Real
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

omit [MeasurableSingletonClass α] [Countable α] in
/-- A law whose atoms are all positive dominates every law on the same countable space. -/
theorem absolutelyContinuous_of_forall_singleton_ne_zero {P Q : Measure α}
    (hP0 : ∀ a, P {a} ≠ 0) : Q ≪ P := by
  refine Measure.AbsolutelyContinuous.mk fun S _ hS => ?_
  have hempty : S = ∅ := by
    by_contra hne
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hle : P {a} ≤ 0 := by
      calc P {a} ≤ P S := measure_mono (Set.singleton_subset_iff.mpr ha)
        _ = 0 := hS
    exact hP0 a (nonpos_iff_eq_zero.mp hle)
  simp [hempty]

/-- The pointwise atom ratio is a density of one countable law against a positive-atom law. -/
theorem withDensity_singleton_ratio {P Q : Measure α} [IsFiniteMeasure P]
    (hP0 : ∀ a, P {a} ≠ 0) :
    P.withDensity (fun a => Q {a} / P {a}) = Q := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [withDensity_apply _ (MeasurableSet.singleton a), lintegral_singleton]
  exact ENNReal.div_mul_cancel (hP0 a) (measure_ne_top P {a})

/-- The Radon--Nikodym derivative of countable laws is the pointwise atom ratio. -/
theorem rnDeriv_eq_singleton_ratio {P Q : Measure α} [IsFiniteMeasure P]
    (hP0 : ∀ a, P {a} ≠ 0) :
    Q.rnDeriv P =ᵐ[P] fun a => Q {a} / P {a} := by
  nth_rewrite 1 [← withDensity_singleton_ratio (P := P) (Q := Q) hP0]
  exact Measure.rnDeriv_withDensity P Measurable.of_discrete

/-- The log-likelihood ratio of countable laws is the pointwise log atom ratio. -/
theorem llr_eq_log_singleton_ratio {P Q : Measure α} [IsFiniteMeasure P]
    (hP0 : ∀ a, P {a} ≠ 0) :
    llr Q P =ᵐ[Q] fun a => Real.log ((Q {a}).toReal / (P {a}).toReal) := by
  have hac : Q ≪ P := absolutelyContinuous_of_forall_singleton_ne_zero hP0
  filter_upwards [hac.ae_le (rnDeriv_eq_singleton_ratio (P := P) (Q := Q) hP0)] with a ha
  rw [llr, ha, ENNReal.toReal_div]

/-- Absolute summability of the atom-weighted values is integrability on a countable law. -/
theorem integrable_of_summable_singleton_weighted {Q : Measure α} [IsFiniteMeasure Q] (f : α → ℝ)
    (hsum : Summable fun a => (Q {a}).toReal * |f a|) : Integrable f Q := by
  refine ⟨StronglyMeasurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_countable']
  have hterm : (fun a => ‖f a‖ₑ * Q {a}) = fun a => ENNReal.ofReal ((Q {a}).toReal * |f a|) := by
    funext a
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_toReal (measure_ne_top Q {a}),
      ← ENNReal.ofReal_mul (abs_nonneg (f a)), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    ring_nf
  rw [hterm]
  exact hsum.tsum_ofReal_lt_top

/-- **Finiteness of countable relative entropy** from an absolutely summable log-ratio series. -/
theorem klDiv_ne_top_of_summable_log_singleton_ratio {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hP0 : ∀ a, P {a} ≠ 0)
    (hsum : Summable fun a =>
      (Q {a}).toReal * |Real.log ((Q {a}).toReal / (P {a}).toReal)|) :
    klDiv Q P ≠ ⊤ := by
  refine klDiv_ne_top (absolutelyContinuous_of_forall_singleton_ne_zero hP0) ?_
  exact (integrable_of_summable_singleton_weighted _ hsum).congr
    (llr_eq_log_singleton_ratio hP0).symm

/-- **Exact value of countable relative entropy.**  Against a positive-atom baseline the
Kullback--Leibler divergence is the absolutely convergent atom series. -/
theorem toReal_klDiv_of_countable {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hP0 : ∀ a, P {a} ≠ 0)
    (hsum : Summable fun a =>
      (Q {a}).toReal * |Real.log ((Q {a}).toReal / (P {a}).toReal)|) :
    (klDiv Q P).toReal
      = ∑' a, (Q {a}).toReal * Real.log ((Q {a}).toReal / (P {a}).toReal) := by
  have hac : Q ≪ P := absolutelyContinuous_of_forall_singleton_ne_zero hP0
  have hint : Integrable (fun a => Real.log ((Q {a}).toReal / (P {a}).toReal)) Q :=
    integrable_of_summable_singleton_weighted _ hsum
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_congr_ae (llr_eq_log_singleton_ratio hP0),
    integral_countable hint]
  simp [Measure.real, smul_eq_mul]

end GaloisForLFunctions.HTGeometry
