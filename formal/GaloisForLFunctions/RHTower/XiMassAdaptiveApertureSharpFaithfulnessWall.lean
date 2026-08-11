import GaloisForLFunctions.RHTower.XiMassAdaptiveApertureFaithfulnessWall
import GaloisForLFunctions.RHTower.XiMassObliqueComovingPrimeExponential

/-!
# Sharp source/receiver wall for adaptive Xi mass apertures

The conserved mass charge says that an off-line divisor boost is governed by time divided by the
raised spectral height.  The previous one-sided wall showed that boost divergence forces
`n / a(n) -> infinity`.  The universal upper height law closes the converse: the raised height is
at most the aperture plus the fixed original height.  Thus every off-line copy is faithful on
exactly the same schedules, namely those with divergent time-to-aperture ratio.

This makes the adaptive phase diagram sharp.  Every unconditional oblique source absorber requires
an eventually positive linear aperture velocity, while every faithful receiver schedule excludes
every such velocity.  Kinematic mass extinction and off-line detection therefore occupy disjoint
asymptotic chambers.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- The raised Xi mass height is bounded above by aperture plus original Poisson height. -/
theorem xiMassFamily_height_le_aperture_add_original
    {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    ((xiMassFamily ha).pt q).re ≤ a + (xiPoissonPoint q).re := by
  have h := xiPoissonAbstract.csqrtRe_massArg_le_add ha q
  simpa only [xiMassFamily_pt_eq_mass_pt, xiPoissonAbstract_pt,
    HTGeometry.AbstractSpectralFamily.mass_pt,
    HTGeometry.csqrt_re, add_comm] using h

/-- Divergent time-to-aperture ratio forces divergent time-to-raised-height ratio.  The reverse
inequality was already immediate from the lower aperture bound; this is the missing sharp half. -/
theorem xiMassFamily_apertureRatio_tendsto_implies_heightRatio_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop atTop) :
    Tendsto
      (fun n : ℕ => (n : ℝ) / ((xiMassFamily (ha n)).pt q).re)
      atTop atTop := by
  let R : ℝ := (xiPoissonPoint q).re
  let C : ℝ := 1 + 2 * R
  have hR : 0 < R := by
    dsimp only [R]
    linarith [three_lt_xiPoissonPoint_re q]
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hscaled : Tendsto (fun n : ℕ => ((n : ℝ) / a n) / C) atTop atTop :=
    hratio.atTop_div_const hC
  refine tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_) hscaled
  have haPos : 0 < a n := by linarith [ha n]
  have hheightPos : 0 < ((xiMassFamily (ha n)).pt q).re :=
    (xiMassFamily (ha n)).re_pos q
  have hheight : ((xiMassFamily (ha n)).pt q).re ≤ C * a n := by
    calc
      ((xiMassFamily (ha n)).pt q).re ≤ a n + R := by
        simpa only [R, add_comm] using
          xiMassFamily_height_le_aperture_add_original (ha n) q
      _ ≤ C * a n := by
        dsimp only [C]
        nlinarith [ha n]
  calc
    ((n : ℝ) / a n) / C = (n : ℝ) / (C * a n) := by
      field_simp [haPos.ne', hC.ne']
    _ ≤ (n : ℝ) / ((xiMassFamily (ha n)).pt q).re :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg n) hheightPos hheight

/-- **Sharp adaptive faithfulness law.**  At every off-line Xi divisor copy, boost divergence is
equivalent to divergent time-to-aperture ratio. -/
theorem xiMassFamily_boost_tendsto_iff_apertureRatio_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hq : (xiPoissonPoint q).im ≠ 0) :
    Tendsto
        (fun n : ℕ => (n : ℝ) * |((xiMassFamily (ha n)).pt q).im|)
        atTop atTop ↔
      Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop atTop := by
  constructor
  · exact xiMassFamily_boost_tendsto_implies_apertureRatio_tendsto a ha q hq
  · intro hratio
    apply (xiMassFamily_boost_tendsto_iff_heightRatio_tendsto a ha q hq).2
    exact xiMassFamily_apertureRatio_tendsto_implies_heightRatio_tendsto
      a ha q hratio

/-- Every faithful off-line schedule eventually violates each proposed positive linear aperture
lower bound. -/
theorem xiMassFamily_faithfulSchedule_not_eventually_linear
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hq : (xiPoissonPoint q).im ≠ 0)
    (hfaithful : Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop atTop)
    {v : ℝ} (hv : 0 < v) :
    ¬ ∀ᶠ n : ℕ in atTop, v * (n : ℝ) ≤ a n := by
  intro hlinear
  have hboost :=
    (xiMassFamily_boost_tendsto_iff_apertureRatio_tendsto a ha q hq).2 hfaithful
  exact (xiMassFamily_linearSchedule_boost_not_tendsto_atTop
    a ha hv hlinear q) hboost

/-- **Source/receiver chamber separation.**  Any schedule entering an unconditional oblique
source-absorber chamber (`4 * sigma * v > 1`) is incapable of faithful off-line boost detection. -/
theorem xiMassFamily_obliqueAbsorberSchedule_not_faithful
    (a : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (q : XiZeroCopy)
    (hq : (xiPoissonPoint q).im ≠ 0)
    {sigma v : ℝ} (hv : 0 < v) (_hphase : 1 < 4 * sigma * v)
    (habsorber : ∀ᶠ n : ℕ in atTop, v * (n : ℝ) ≤ a n) :
    ¬ Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop atTop := by
  intro hfaithful
  exact xiMassFamily_faithfulSchedule_not_eventually_linear
    a ha q hq hfaithful hv habsorber

end

end RHTower
