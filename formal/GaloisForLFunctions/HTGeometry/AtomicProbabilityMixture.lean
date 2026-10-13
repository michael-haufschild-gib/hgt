import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure

/-! # Atomic mixtures and uniform control of every event probability -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open MeasureTheory
open scoped BigOperators ENNReal

variable {α β : Type*} [Fintype α] [MeasurableSpace β]

theorem atomicProbability_mixture (P Q : Law α) (φ : α → β)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((mixture P Q t h0 h1).atomicProbability φ : Measure β) =
      ENNReal.ofReal t • (P.atomicProbability φ : Measure β) +
      ENNReal.ofReal (1 - t) • (Q.atomicProbability φ : Measure β) := by
  classical
  have hcoef (i : α) : ENNReal.ofReal (mixture P Q t h0 h1 i) =
      ENNReal.ofReal t * ENNReal.ofReal (P i) +
      ENNReal.ofReal (1 - t) * ENNReal.ofReal (Q i) := by
    rw [mixture_apply,
      ENNReal.ofReal_add (mul_nonneg h0 (P.nonneg i))
        (mul_nonneg (sub_nonneg.mpr h1) (Q.nonneg i)),
      ENNReal.ofReal_mul h0, ENNReal.ofReal_mul (sub_nonneg.mpr h1)]
  change (∑ i, ENNReal.ofReal (mixture P Q t h0 h1 i) • Measure.dirac (φ i)) =
    ENNReal.ofReal t • (∑ i, ENNReal.ofReal (P i) • Measure.dirac (φ i)) +
    ENNReal.ofReal (1 - t) • (∑ i, ENNReal.ofReal (Q i) • Measure.dirac (φ i))
  simp_rw [hcoef, add_smul, mul_smul]
  simp only [Finset.sum_add_distrib, Finset.smul_sum]

theorem atomicProbability_mixture_event_difference (P Q : Law α) (φ : α → β)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (s : Set β) :
    |(((mixture P Q t h0 h1).atomicProbability φ : Measure β) s).toReal -
        ((Q.atomicProbability φ : Measure β) s).toReal| =
      t * |((P.atomicProbability φ : Measure β) s).toReal -
        ((Q.atomicProbability φ : Measure β) s).toReal| := by
  rw [atomicProbability_mixture]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h1)]
  rw [show t * ((P.atomicProbability φ : Measure β) s).toReal +
      (1 - t) * ((Q.atomicProbability φ : Measure β) s).toReal -
      ((Q.atomicProbability φ : Measure β) s).toReal =
      t * (((P.atomicProbability φ : Measure β) s).toReal -
        ((Q.atomicProbability φ : Measure β) s).toReal) by ring,
    abs_mul, abs_of_nonneg h0]

theorem atomicProbability_mixture_event_le (P Q : Law α) (φ : α → β)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (s : Set β) :
    |(((mixture P Q t h0 h1).atomicProbability φ : Measure β) s).toReal -
        ((Q.atomicProbability φ : Measure β) s).toReal| ≤ t := by
  rw [atomicProbability_mixture_event_difference]
  have hP : ((P.atomicProbability φ : Measure β) s).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (MeasureTheory.prob_le_one (μ := (P.atomicProbability φ : Measure β)) (s := s))
  have hQ : ((Q.atomicProbability φ : Measure β) s).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (MeasureTheory.prob_le_one (μ := (Q.atomicProbability φ : Measure β)) (s := s))
  have hP0 : 0 ≤ ((P.atomicProbability φ : Measure β) s).toReal := ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ ((Q.atomicProbability φ : Measure β) s).toReal := ENNReal.toReal_nonneg
  have hdiff : |((P.atomicProbability φ : Measure β) s).toReal -
      ((Q.atomicProbability φ : Measure β) s).toReal| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiff h0

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
