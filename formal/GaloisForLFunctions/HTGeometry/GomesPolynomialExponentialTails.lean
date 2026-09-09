import GaloisForLFunctions.HTGeometry.GomesDilatonNormalizationTensor
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact half-line integrability of polynomial exponential densities

Infrastructure for the finite scalar tensor sector suggested by arXiv:2509.25276v7
section 5.2. This extends the existing Gaussian and quartic families to every real
polynomial. No decay, integrability, or leading-term premise is supplied: the complete
right-tail classification is proved. Comparison uses symbolic polynomial asymptotics.
-/

noncomputable section
open Polynomial MeasureTheory Filter Asymptotics Set
open scoped Topology NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- A positive constant exponential cannot be integrated on any right-hand tail. -/
theorem gomesConstantExponential_not_integrable_atTop (c : ℝ) :
    ¬ IntegrableAtFilter (fun _ : ℝ => Real.exp c) atTop := by
  intro h
  obtain ⟨a, ha⟩ := integrableAtFilter_atTop_iff.mp h
  have hf : IsFiniteMeasure (volume.restrict (Ici a) : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (Real.exp_ne_zero c)).mp ha
  have hn := isFiniteMeasure_restrict.mp hf
  exact hn Real.volume_Ici

/-- Negative leading term gives an explicit eventual linear exponential envelope. -/
theorem gomesPolynomialExponential_linear_envelope_iff (P : ℝ[X]) :
    (∃ c : ℝ, c < 0 ∧ ∀ᶠ x : ℝ in atTop, P.eval x ≤ c * x) ↔
      0 < P.natDegree ∧ P.leadingCoeff < 0 := by
  constructor
  · rintro ⟨c, hc, hb⟩
    have ht : Tendsto (fun x : ℝ => P.eval x) atTop atBot :=
      tendsto_atBot_mono' atTop hb (tendsto_id.const_mul_atTop_of_neg hc)
    obtain ⟨hd, hl⟩ := P.tendsto_atBot_iff_leadingCoeff_nonpos.mp ht
    refine ⟨natDegree_pos_iff_degree_pos.mpr hd, ?_⟩
    exact lt_of_le_of_ne hl (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hd))
  · rintro ⟨hd, hl⟩
    have hp : P ≠ 0 := leadingCoeff_ne_zero.mp hl.ne
    have he : P.degree = (X ^ P.natDegree : ℝ[X]).degree := by
      rw [degree_eq_natDegree hp, degree_X_pow]
    have ht : Tendsto (fun x : ℝ => P.eval x / x ^ P.natDegree) atTop (𝓝 P.leadingCoeff) := by
      simpa only [eval_pow, eval_X, leadingCoeff_X_pow, div_one] using
        P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X ^ P.natDegree) he
    refine ⟨P.leadingCoeff / 2, by linarith, ?_⟩
    filter_upwards [ht.eventually_lt_const (show P.leadingCoeff < P.leadingCoeff / 2 by linarith),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hpow : x ≤ x ^ P.natDegree := le_self_pow₀ hx1 (Nat.ne_of_gt hd)
    have hh : P.eval x < P.leadingCoeff / 2 * x ^ P.natDegree :=
      (div_lt_iff₀ (pow_pos hx0 _)).mp hx
    exact hh.le.trans (mul_le_mul_of_nonpos_left hpow (by linarith))

/-- Complete right-tail integrability classification, including constant and growing profiles. -/
theorem gomesPolynomialExponential_integrable_atTop_iff (P : ℝ[X]) :
    IntegrableAtFilter (dilatonWeight P) atTop ↔ 0 < P.natDegree ∧ P.leadingCoeff < 0 := by
  constructor
  · intro hi
    have obstruction : (∃ c : ℝ, ∀ᶠ x : ℝ in atTop, c ≤ P.eval x) → False := by
      rintro ⟨c, hc⟩
      have ho : (fun _ : ℝ => Real.exp c) =O[atTop] dilatonWeight P := by
        apply IsBigO.of_bound 1
        filter_upwards [hc] with x hx
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos c), dilatonWeight,
          abs_of_pos (Real.exp_pos (P.eval x)), one_mul] using Real.exp_le_exp.mpr hx
      exact gomesConstantExponential_not_integrable_atTop c
        (ho.integrableAtFilter (continuous_const.stronglyMeasurableAtFilter volume atTop) hi)
    have hd : 0 < P.natDegree := by
      by_contra hn
      have hz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hn
      have hp := eq_C_of_natDegree_eq_zero hz
      apply obstruction
      exact ⟨P.coeff 0, Filter.Eventually.of_forall fun x => by
        have hx := congrArg (fun q : ℝ[X] => q.eval x) hp
        simp only [eval_C] at hx
        exact hx.ge⟩
    refine ⟨hd, ?_⟩
    by_contra hn
    have hl : 0 ≤ P.leadingCoeff := le_of_not_gt hn
    apply obstruction
    exact ⟨0, (P.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp hd) hl).eventually_ge_atTop 0⟩
  · intro h
    obtain ⟨c, hc, he⟩ := (gomesPolynomialExponential_linear_envelope_iff P).mpr h
    have ho : dilatonWeight P =O[atTop] (fun x : ℝ => Real.exp (c * x)) := by
      apply IsBigO.of_bound 1
      filter_upwards [he] with x hx
      simpa only [dilatonWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (P.eval x)),
        abs_of_pos (Real.exp_pos (c * x)), one_mul] using Real.exp_le_exp.mpr hx
    have hg : IntegrableAtFilter (fun x : ℝ => Real.exp (c * x)) atTop :=
      integrableAtFilter_atTop_iff.mpr ⟨0,
        Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi hc 0)⟩
    exact ho.integrableAtFilter ((gomesDilatonWeight_continuous P).stronglyMeasurableAtFilter volume atTop) hg

end GaloisForLFunctions.HTGeometry
