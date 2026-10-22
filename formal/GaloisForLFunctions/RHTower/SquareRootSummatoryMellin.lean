import GaloisForLFunctions.RHTower.Suzuki.SuzukiMellinConvolution
import GaloisForLFunctions.RHTower.StepProfileMellinLSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Mellin transport of square-root summatory primitives

Multiplicative convolution with the unit ray integrates the weighted summatory
profile. The result is its literal truncated integral and has the absolutely
convergent Mellin transform `L(b,s-1/2)/(2*s*(s-1/2))` under a summatory bound.
No numerical premise or source-cone assertion is used.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower

/-- The positive-ray integration kernel, with unit cutoff. -/
def mellinRayOne : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun _ => 1)

lemma hasMellin_mellinRayOne {s : ℂ} (hs : 0 < s.re) :
    HasMellin mellinRayOne (-s) (1 / s) := by
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro x hx
    change (1 : ℝ) < x at hx
    exact (lt_trans zero_lt_one hx : (0 : ℝ) < x)
  simp_rw [HasMellin, mellin, MellinConvergent, mellinRayOne, ← indicator_smul,
    IntegrableOn, integrable_indicator_iff measurableSet_Ioi, smul_eq_mul,
    integral_indicator measurableSet_Ioi, mul_one,
    Measure.restrict_restrict_of_subset hsubset]
  simp only [IntegrableOn, Measure.restrict_restrict_of_subset hsubset]
  have hex : (-s - 1).re < -1 := by simp only [sub_re, neg_re, one_re]; linarith
  refine ⟨integrableOn_Ioi_cpow_of_lt hex zero_lt_one, ?_⟩
  rw [integral_Ioi_cpow_of_lt hex zero_lt_one, ofReal_one, one_cpow, sub_add_cancel]
  ring

/-- The weighted summatory profile whose multiplicative integration gives the
literal square-root Abel mean. -/
def squareRootSummatoryProfile (b : ℕ → ℂ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x =>
    (x : ℂ) ^ (1 / 2 : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n) / 2)

lemma measurable_squareRootSummatoryProfile (b : ℕ → ℂ) :
    Measurable (squareRootSummatoryProfile b) := by
  apply Measurable.indicator _ measurableSet_Ioi
  have hsum : Measurable (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n) :=
    (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, b n)).comp
      Nat.measurable_floor
  fun_prop

lemma hasMellin_squareRootSummatoryProfile {b : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, b n‖ ≤ C * (N : ℝ) ^ θ)
    {s : ℂ} (hs : 1 / 2 < s.re) (hθs : θ < s.re - 1 / 2)
    (hsum : LSeriesSummable b (s - 1 / 2)) :
    HasMellin (squareRootSummatoryProfile b) (-s)
      (LSeries b (s - 1 / 2) / (2 * (s - 1 / 2))) := by
  have hw : 0 < (s - 1 / 2).re := by
    simp only [sub_re]; norm_num; linarith
  have hθw : θ < (s - 1 / 2).re := by simpa using hθs
  have hi := integrableOn_complexPartialSum hC hb hw hθw
  have hm := mellin_complexPartialSum_eq_LSeries hC hb hw hθw hsum
  have he (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (x : ℂ) ^ (-s - 1) *
        ((x : ℂ) ^ (1 / 2 : ℂ) * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n) / 2) =
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n) * (x : ℂ) ^ (-(s - 1 / 2) - 1)) / 2 := by
    change (1 : ℝ) < x at hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith : x ≠ 0)
    rw [show -(s - 1 / 2) - 1 = (-s - 1) + 1 / 2 by ring, cpow_add _ _ hx0]
    ring
  have hsubset : Ioi (1 : ℝ) ⊆ Ioi 0 := by
    intro x hx
    change (1 : ℝ) < x at hx
    exact (lt_trans zero_lt_one hx : (0 : ℝ) < x)
  simp_rw [HasMellin, mellin, MellinConvergent, squareRootSummatoryProfile,
    ← indicator_smul, IntegrableOn, integrable_indicator_iff measurableSet_Ioi,
    smul_eq_mul, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset hsubset]
  simp only [IntegrableOn, Measure.restrict_restrict_of_subset hsubset]
  constructor
  · exact (hi.div_const 2).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (he x hx).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi he, integral_div]
    have hw0 : s - 1 / 2 ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have heq := (eq_div_iff hw0).mpr (show
      (∫ x in Ioi (1 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, b n) *
        (x : ℂ) ^ (-(s - 1 / 2) - 1)) * (s - 1 / 2) = _ by
          simpa only [mul_comm] using hm)
    rw [heq, div_div]
    congr 1
    ring

/-- The continuous square-root Abel interpolation as a Mellin convolution. -/
def squareRootSummatoryPrimitive (b : ℕ → ℂ) : ℝ → ℂ :=
  positiveMellinConvolution (squareRootSummatoryProfile b) mellinRayOne

lemma hasMellin_squareRootSummatoryPrimitive {b : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, ‖∑ n ∈ Finset.Icc 1 N, b n‖ ≤ C * (N : ℝ) ^ θ)
    {s : ℂ} (hs : 1 / 2 < s.re) (hθs : θ < s.re - 1 / 2)
    (hsum : LSeriesSummable b (s - 1 / 2)) :
    HasMellin (squareRootSummatoryPrimitive b) (-s)
      (LSeries b (s - 1 / 2) / (2 * s * (s - 1 / 2))) := by
  have hf := hasMellin_squareRootSummatoryProfile hC hb hs hθs hsum
  have hg := hasMellin_mellinRayOne (show 0 < s.re by linarith)
  have h := hasMellin_positiveMellinConvolution (g := mellinRayOne) (measurable_squareRootSummatoryProfile b)
    (measurable_const.indicator measurableSet_Ioi) hf.1 hg.1
  rw [hf.2, hg.2] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [div_mul_div_comm, mul_one]
  congr 1
  ring

end RHTower

namespace RHTower

/-- The convolution is exactly the truncated weighted integral, for every real
cutoff, including cutoffs below one. -/
lemma squareRootSummatoryPrimitive_eq_integral (b : ℕ → ℂ) (x : ℝ) :
    squareRootSummatoryPrimitive b x =
      ∫ t in Ioo (1 : ℝ) x,
        ((t : ℂ) ^ (1 / 2 : ℂ) / (2 * t)) * ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, b n := by
  rw [squareRootSummatoryPrimitive, positiveMellinConvolution,
    ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 1 < t
  · have ht0 : 0 < t := by linarith
    by_cases htx : t < x
    · have hdiv : 1 < x / t := (one_lt_div ht0).mpr htx
      simp only [squareRootSummatoryProfile, mellinRayOne, indicator_apply,
        mem_Ioi, mem_Ioo, ht, ht0, htx, hdiv, and_self, if_true]
      ring
    · have hdiv : ¬1 < x / t := by rw [one_lt_div ht0]; exact htx
      simp [squareRootSummatoryProfile, mellinRayOne, indicator_apply, ht, ht0, htx, hdiv]
  · simp [squareRootSummatoryProfile, mellinRayOne, indicator_apply, ht]

end RHTower
