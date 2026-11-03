import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime
import GaloisForLFunctions.ArithmeticCriticalityTheory.CapacityRatioApertureCriticality
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# The Markov part of Weil's form dies before the first prime

Weil's form splits as `W = M + ½⟨c, ·⟩² − ½⟨s, ·⟩²` (RHTower `weil_eq_markovForm_add_pole`), with the
Markov part `M(g) = Γ‖g‖² + ∫_0^∞ ω(x)‖g − g(· + x)‖² dx − 2Σ_n w_n c_g(log n)`,
`Γ = −(γ + π/2 + log 8π)`. `M` is a translation-invariant jump form with nonnegative rates.

**Theorem** (`exists_markovEnergy_neg_of_support_le`). There is a nonnegative `C²` test supported
in `[0, e^{−3/4}]` with `M(g) ≤ −‖g‖²/40`. Since `e^{−3/4} < 1/2 < log 2`, the Markov part is
indefinite on every window of length `e^{−3/4}`, before any prime acts and inside half of the unit
window.

Proof: a smooth plateau of width `w = e^{−3/4}` has self-energy
`(log(1/w) + 2c_∞ + β/‖φ‖²)‖g‖² + O(w)‖g‖²` with `2c_∞ = 2log 2 + π/2` and shape term `β/‖φ‖² → 1`
(SSHA). The `π/2` of the archimedean Robin constant cancels the `π/2` of `Γ`, leaving
`−γ − log 2 − log π + 3/4 + 1 + e^{−1/4}/2 + o(1) < 0`.

Every prime enters `M` with the sign `−2w_n c_g(log n) ≤ 0` on nonnegative tests, so translates and
longer windows stay negative (`exists_markovEnergy_neg_of_support_Icc`).
-/

open MeasureTheory Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open RHTower RHTower.WeilMarkovPole SpacingScaleHarmonicAnalysis

/-- The width of the Markov-negative plateau, `e^{−3/4}`. -/
def markovDeathWidth : ℝ := Real.exp (-(3 / 4))

theorem markovDeathWidth_pos : 0 < markovDeathWidth := Real.exp_pos _

theorem markovDeathWidth_lt_half : markovDeathWidth < 1 / 2 := by
  unfold markovDeathWidth
  have h := Real.add_one_le_exp (3 / 4 : ℝ)
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

theorem markovDeathWidth_lt_log_two : markovDeathWidth < Real.log 2 := by
  linarith [markovDeathWidth_lt_half, Real.log_two_gt_d9]

/-- The Lévy energy as a Bochner integral equals the lintegral form used by `markovForm`. -/
theorem levyJump_eq_levyEnergy {g : ℝ → ℝ} (hg : Continuous g) : levyJump g = levyEnergy g := by
  unfold levyJump levyEnergy
  have hc : Continuous fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2 := by fun_prop
  have hm : StronglyMeasurable fun x : ℝ => ∫ u, (g u - g (u + x)) ^ 2 :=
    hc.stronglyMeasurable.integral_prod_right'
  rw [integral_eq_lintegral_of_nonneg_ae]
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
      mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _)
  · exact (measurable_archLevyDensity.mul hm.measurable).aestronglyMeasurable

/-- At level one the Markov form is `Γ‖g‖² + J(g)`: no prime acts. -/
theorem markovForm_one (g : ℝ → ℝ) :
    markovForm 1 g = EF.gammaBracket 0 * (∫ u, g u ^ 2) + levyJump g := by
  have h : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
  simp [markovForm, creationPotential, primeJump, h]

/-- The constant of the plateau estimate is negative. -/
theorem markovDeath_constant_neg :
    EF.gammaBracket 0 + (3 / 4 + (2 * Real.log 2 + π / 2) + (1 + 1 / 100)) +
      Real.exp (1 / 2) / 2 * markovDeathWidth ≤ -(1 / 40) := by
  rw [ArchimedeanAnomaly.gammaBracket_zero_eq]
  have h8 : Real.log (8 * π) = 3 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_gt_d9
  have hlπ : 1 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hew : Real.exp (1 / 2) * markovDeathWidth ≤ 4 / 5 := by
    unfold markovDeathWidth
    rw [← Real.exp_add, show (1 / 2 : ℝ) + -(3 / 4) = -(1 / 4) by norm_num, Real.exp_neg]
    have h := Real.add_one_le_exp (1 / 4 : ℝ)
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  rw [h8]
  nlinarith

/-- **The Markov part dies before the first prime.** Some nonnegative `C²` test supported in
`[0, e^{−3/4}]` has `M(g) ≤ −‖g‖²/40 < 0`; the bound holds for the Markov energy of the Weil
functional and for the level-one Markov form. -/
theorem exists_markovEnergy_neg_of_support_le :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ (∀ u, u ∉ Icc 0 markovDeathWidth → g u = 0) ∧
      (∀ u, 0 ≤ g u) ∧ 0 < ∫ u, g u ^ 2 ∧
      markovForm 1 g ≤ -(1 / 40) * ∫ u, g u ^ 2 ∧
      markovEnergy (fun u => (g u : ℂ)) ≤ -(1 / 40) * ∫ u, g u ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_lipschitz_smoothTransition
  obtain ⟨η, hη0, hη4, hβ⟩ := exists_plateau_bumpRobin_le (ε := 1 / 100) (by norm_num)
  set w := markovDeathWidth with hw
  have hw0 : 0 < w := markovDeathWidth_pos
  have hw1 : w ≤ 1 := by linarith [markovDeathWidth_lt_half]
  set φ := plateau η with hφ
  set g := atomDilate φ w with hg
  have hφc : ContDiff ℝ 2 φ := contDiff_plateau η
  have hφsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0 := fun u hu => plateau_eq_zero hη0 hu
  have hφ0 : 0 < ∫ u, φ u ^ 2 :=
    lt_of_lt_of_le (by linarith) (integral_plateau_sq_ge hη0 (by linarith))
  have hgc : ContDiff ℝ 2 g := hφc.comp (contDiff_id.div_const w)
  have hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0 := by
    intro u hu
    refine hφsupp (u / w) fun h => hu ⟨?_, ?_⟩
    · have := h.1; rw [le_div_iff₀ hw0] at this; linarith
    · have := h.2; rw [div_le_iff₀ hw0] at this; linarith
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := 0) (b := w)) fun u hu => hgsupp u hu
  have hM : ∫ u, g u ^ 2 = w * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw0
  have hM0 : 0 < ∫ u, g u ^ 2 := by rw [hM]; positivity
  -- the self-energy of the plateau atom
  have hE := abs_levyEnergy_atomDilate_sub_le hφc hφsupp hφ0 hw0 hw1 (abs_plateau_sub_le hC hη0)
  have hlog : Real.log (1 / w) = 3 / 4 := by
    rw [hw, markovDeathWidth, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hR : profileRobin φ ≤ 2 * Real.log 2 + π / 2 + (1 + 1 / 100) := by
    unfold profileRobin
    rw [archRobinConstant_eq]
    linarith
  have hlevy : levyEnergy g ≤
      (3 / 4 + (2 * Real.log 2 + π / 2) + (1 + 1 / 100) + Real.exp (1 / 2) / 2 * w) *
        ∫ u, g u ^ 2 := by
    have h1 := (abs_le.mp hE).2
    rw [hlog] at h1
    nlinarith [mul_le_mul_of_nonneg_right hR hM0.le]
  -- assemble the Markov form at level one
  have hform : markovForm 1 g ≤ -(1 / 40) * ∫ u, g u ^ 2 := by
    rw [markovForm_one, levyJump_eq_levyEnergy hgc.continuous]
    have hk := markovDeath_constant_neg
    rw [← hw] at hk
    nlinarith [mul_le_mul_of_nonneg_right hk hM0.le]
  have hN : ∀ n : ℕ, 1 < n → ∀ u, g u * g (u + Real.log n) = 0 := by
    intro n hn u
    by_cases hu : u ∈ Icc 0 w
    · have hlog2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have : u + Real.log n ∉ Icc 0 w := fun h => by
        linarith [h.2, hu.1, markovDeathWidth_lt_log_two]
      rw [hgsupp _ this, mul_zero]
    · rw [hgsupp u hu, zero_mul]
  have hbridge := ArithmeticCriticalityTheory.markovForm_eq_markovEnergy hgc hgcs hN
  exact ⟨g, hgc, hgsupp, fun u => plateau_nonneg _, hM0, hform, hbridge ▸ hform⟩

end GaloisForLFunctions.SignedWindowCriticality

end
