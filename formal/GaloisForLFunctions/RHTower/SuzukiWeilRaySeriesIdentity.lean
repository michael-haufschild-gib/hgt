import GaloisForLFunctions.RHTower.SuzukiWeilRaySeriesHolomorphy
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert

/-!
# Identity theorem for the ray series of the transform

Step 3b(i) of the route to Suzuki's Lemma 3.2.  `‖.‖_0 = 0` only gives information on the *real*
axis; this file upgrades it to the whole divisor complement.

The ray series is holomorphic on the open set `{XiC != 0}`
(`differentiableAt_suzukiPHatRaySum`), that set is preconnected (the corpus's
`isPreconnected_XiC_ne_zero`, from countability of the divisor), and the reals accumulate at the
admissible point `0` (`XiC 0 != 0`).  So vanishing at every admissible real point is already an
`eventually-frequently` hypothesis at `0`, and
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` closes it.

What remains for Lemma 3.2 is the fiber residue: splitting the tsum at
`{q | xiSpectralPoint q = gamma}` — finite, since it is a `Fin (multiplicity)` slice of the sigma
type — and reading off `sum over the fiber of b_q = 0`, then feeding `F(gamma) = 0` into
`suzuki_lemma_two_one`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## From the real axis to the whole divisor complement -/

/-- **Identity theorem for the ray series.**  Vanishing at every admissible *real* point forces
vanishing at every point off the Xi divisor. -/
theorem suzukiPHatRaySum_eq_zero_off_divisor {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0)
    (hvanish : ∀ x : ℝ, XiC ((x : ℝ) : ℂ) ≠ 0 →
      (∑' q : XiZeroCopy, suzukiPHatRayTerm φ ((x : ℝ) : ℂ) q) = 0)
    {w : ℂ} (hw : XiC w ≠ 0) :
    (∑' q : XiZeroCopy, suzukiPHatRayTerm φ w q) = 0 := by
  set R : ℂ → ℂ := fun z => ∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q with hR
  have hdiff : DifferentiableOn ℂ R {z : ℂ | XiC z ≠ 0} := fun z hz =>
    (differentiableAt_suzukiPHatRaySum hφ hsupp hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ R {z : ℂ | XiC z ≠ 0} := hdiff.analyticOnNhd isOpen_XiC_ne_zero
  have hz₀ : XiC (0 : ℂ) ≠ 0 := XiC_zero_ne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_XiC_ne_zero 0 hz₀
  set u : ℕ → ℂ := fun n => (((r / ((n : ℝ) + 2)) : ℝ) : ℂ) with hu
  have hupos : ∀ n : ℕ, (0 : ℝ) < r / ((n : ℝ) + 2) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    positivity
  have hune : ∀ n : ℕ, u n ≠ 0 := by
    intro n
    simp only [hu, ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (hupos n)
  have hulim : Tendsto u atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    rw [Complex.ofReal_zero] at this
    exact this
  have hulimW : Tendsto u atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hulim
      (Filter.Eventually.of_forall fun n => hune n)
  have hzero : ∀ n : ℕ, R (u n) = 0 := by
    intro n
    have hlt : ‖u n‖ < r := by
      simp only [hu, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hupos n)]
      have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      calc r / ((n : ℝ) + 2) ≤ r / 2 := by
            refine div_le_div_of_nonneg_left hr.le (by norm_num) h2
        _ < r := by linarith
    have hmem : u n ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hlt
    have hXi : XiC (u n) ≠ 0 := hball hmem
    have := hvanish (r / ((n : ℝ) + 2)) (by simpa only [hu] using hXi)
    simpa only [hu, hR] using this
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = 0 :=
    hulimW.frequently (Filter.Frequently.of_forall hzero)
  have heq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_XiC_ne_zero hz₀ hfreq
  exact heq hw

end
end RHTower

