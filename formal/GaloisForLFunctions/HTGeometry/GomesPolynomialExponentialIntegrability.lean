import GaloisForLFunctions.HTGeometry.GomesPolynomialExponentialTails

/-!
# Finite mass for every polynomial exponential density

The scalar tensor-density experiment now has a complete finite-sector criterion:
positive even polynomial degree and negative leading coefficient. Reflection supplies
the second tail, and continuity supplies local integrability. The result does not assume
coercivity, integrability, or an asymptotic envelope.
-/

noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Reflection turns the left tail into the right tail of the reflected polynomial. -/
theorem gomesPolynomialExponential_reflection_integrability (P : ℝ[X]) :
    IntegrableAtFilter (dilatonWeight (P.comp (-X))) atTop ↔
      IntegrableAtFilter (dilatonWeight P) atBot := by
  rw [integrableAtFilter_atTop_iff, integrableAtFilter_atBot_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have hb : IntegrableOn (dilatonWeight (P.comp (-X))) (Ici (-(-a))) := by
      simpa only [neg_neg] using ha
    change IntegrableOn (fun x : ℝ => Real.exp (P.eval x)) (Iic (-a))
    simpa only [dilatonWeight, eval_comp, eval_neg, eval_X, neg_neg] using hb.comp_neg_Iic
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have hb : IntegrableOn (dilatonWeight P) (Iic (-(-a))) := by
      simpa only [neg_neg] using ha
    change IntegrableOn (fun x : ℝ => Real.exp ((P.comp (-X)).eval x)) (Ici (-a))
    simpa only [dilatonWeight, eval_comp, eval_neg, eval_X] using hb.comp_neg_Ici

/-- On a polynomial tail, integrability is precisely divergence of the log-density to minus infinity. -/
theorem gomesPolynomialExponential_tail_decay_iff (P : ℝ[X]) :
    IntegrableAtFilter (dilatonWeight P) atTop ↔ Tendsto (fun x : ℝ => P.eval x) atTop atBot := by
  rw [gomesPolynomialExponential_integrable_atTop_iff,
    P.tendsto_atBot_iff_leadingCoeff_nonpos]
  constructor
  · rintro ⟨hd, hl⟩
    exact ⟨natDegree_pos_iff_degree_pos.mp hd, hl.le⟩
  · rintro ⟨hd, hl⟩
    exact ⟨natDegree_pos_iff_degree_pos.mpr hd,
      lt_of_le_of_ne hl (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hd))⟩

/-- Complete full-line integrability classification for every real polynomial profile. -/
theorem gomesPolynomialExponential_integrable_iff (P : ℝ[X]) :
    Integrable (dilatonWeight P) ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ P.leadingCoeff < 0 := by
  have hc : LocallyIntegrable (dilatonWeight P) := (gomesDilatonWeight_continuous P).locallyIntegrable
  rw [integrable_iff_integrableAtFilter_atBot_atTop, and_iff_left hc,
    ← gomesPolynomialExponential_reflection_integrability,
    gomesPolynomialExponential_integrable_atTop_iff,
    gomesPolynomialExponential_integrable_atTop_iff]
  have hd : (P.comp (-X : ℝ[X])).natDegree = P.natDegree := by simp only [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hl : (P.comp (-X : ℝ[X])).leadingCoeff = P.leadingCoeff * (-1) ^ P.natDegree := by
    rw [leadingCoeff_comp (by simp)]
    simp only [leadingCoeff_neg, leadingCoeff_X]
  rw [hd, hl]
  constructor
  · rintro ⟨⟨hp, hleft⟩, ⟨_, hright⟩⟩
    refine ⟨hp, ?_, hright⟩
    rcases Nat.even_or_odd P.natDegree with he | ho
    · exact he
    · rw [ho.neg_one_pow, mul_neg_one] at hleft
      linarith
  · rintro ⟨hp, he, hn⟩
    rw [he.neg_one_pow, mul_one]
    exact ⟨⟨hp, hn⟩, ⟨hp, hn⟩⟩

/-- An equivalent criterion records decay at both real infinities. -/
theorem gomesPolynomialExponential_integrable_decay_iff (P : ℝ[X]) :
    Integrable (dilatonWeight P) ↔
      Tendsto (fun x : ℝ => P.eval x) atTop atBot ∧
      Tendsto (fun x : ℝ => P.eval x) atBot atBot := by
  have hc : LocallyIntegrable (dilatonWeight P) := (gomesDilatonWeight_continuous P).locallyIntegrable
  rw [integrable_iff_integrableAtFilter_atBot_atTop, and_iff_left hc,
    ← gomesPolynomialExponential_reflection_integrability,
    gomesPolynomialExponential_tail_decay_iff, gomesPolynomialExponential_tail_decay_iff]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨hr, ?_⟩
    simpa only [Function.comp_def, eval_comp, eval_neg, eval_X, neg_neg] using
      hl.comp tendsto_neg_atBot_atTop
  · rintro ⟨hr, hl⟩
    refine ⟨?_, hr⟩
    simpa only [Function.comp_def, eval_comp, eval_neg, eval_X] using
      hl.comp tendsto_neg_atTop_atBot

/-- Raw polynomial density has finite mass exactly when its real density is integrable. -/
theorem gomesDilatonMeasure_finite_iff_integrable (P : ℝ[X]) :
    IsFiniteMeasure (gomesDilatonMeasure P) ↔ Integrable (dilatonWeight P) := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) (gomesDilatonMeasure P) ↔
      Integrable (dilatonWeight P) := by
    change Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.withDensity (fun x => ENNReal.ofReal (dilatonWeight P x))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul'
      (gomesDilatonWeight_continuous P).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [dilatonWeight, ENNReal.toReal_ofReal (Real.exp_pos (P.eval _)).le,
      smul_eq_mul, mul_one]
    rfl
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).symm.trans h

/-- Exact finite-measure criterion, with all degrees and all coefficients covered. -/
theorem gomesDilatonMeasure_finite_polynomial_iff (P : ℝ[X]) :
    IsFiniteMeasure (gomesDilatonMeasure P) ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ P.leadingCoeff < 0 := by
  rw [gomesDilatonMeasure_finite_iff_integrable, gomesPolynomialExponential_integrable_iff]

/-- Exact failure region of total-mass finiteness. -/
theorem gomesDilatonMeasure_infinite_polynomial_iff (P : ℝ[X]) :
    gomesDilatonMeasure P Set.univ = ∞ ↔
      ¬ (0 < P.natDegree ∧ Even P.natDegree ∧ P.leadingCoeff < 0) := by
  rw [← not_isFiniteMeasure_iff, gomesDilatonMeasure_finite_polynomial_iff]

/-- The same coefficient criterion decides whether normalization produces a probability law. -/
theorem gomesDilatonMassNormalized_polynomial_probability_iff (P : ℝ[X]) :
    IsProbabilityMeasure (gomesDilatonMassNormalized P) ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ P.leadingCoeff < 0 := by
  rw [gomesDilatonMassNormalized_probability_iff, gomesDilatonMeasure_finite_polynomial_iff]

end GaloisForLFunctions.HTGeometry
