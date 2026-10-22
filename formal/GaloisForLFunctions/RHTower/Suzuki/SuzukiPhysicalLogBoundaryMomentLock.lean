import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Suzuki physical-log boundary moment lock

The physical logarithmic chart has measure `dr / r`.  A continuous profile with finite weighted
square mass must therefore vanish at the boundary.  Applied to an exact low/high-frequency
splitting of a Dirichlet profile, this forces the low-frequency boundary moment to vanish before
the high-frequency part can enter the physical logarithmic carrier.
-/

open scoped MeasureTheory Topology Interval

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- Continuous finite physical-log mass forces the boundary value to vanish.  This is the
load-bearing analytic implication behind the `dr` versus `dr / r` obstruction. -/
theorem physicalLogIntegrable_continuousAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContinuousAt f 0) {ε : ℝ} (hε : ε ≠ 0)
    (hint : IntervalIntegrable (fun r : ℝ => ‖f r‖ ^ 2 / r) volume 0 ε) :
    f 0 = 0 := by
  by_contra h0
  have hnorm : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hevent : ∀ᶠ r in 𝓝[≠] (0 : ℝ), ‖f 0‖ / 2 ≤ ‖f r‖ := by
    have ht : Tendsto (fun r => ‖f r‖) (𝓝[≠] (0 : ℝ)) (𝓝 ‖f 0‖) :=
      (hf.norm.tendsto.mono_left inf_le_left)
    have hlt : ‖f 0‖ / 2 < ‖f 0‖ := by linarith
    exact ht.eventually (eventually_ge_nhds hlt)
  have hbig :
      (fun r : ℝ => r⁻¹) =O[𝓝[≠] (0 : ℝ)] (fun r : ℝ => ‖f r‖ ^ 2 / r) := by
    rw [isBigO_iff]
    refine ⟨4 / ‖f 0‖ ^ 2, ?_⟩
    filter_upwards [hevent, self_mem_nhdsWithin] with r hr hne
    have habs : 0 < |r| := abs_pos.mpr hne
    have hn0 : ‖f 0‖ ≠ 0 := ne_of_gt hnorm
    have hcoeff : 1 ≤ 4 / ‖f 0‖ ^ 2 * ‖f r‖ ^ 2 := by
      field_simp
      nlinarith [sq_nonneg ‖f r‖]
    rw [Real.norm_eq_abs, abs_inv, norm_div, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (norm_nonneg (f r)), Real.norm_eq_abs]
    simpa [one_div, div_eq_mul_inv, mul_assoc] using
      (div_le_div_iff_of_pos_right habs).mpr hcoeff
  exact (not_intervalIntegrable_of_sub_inv_isBigO_punctured
    (a := 0) (b := ε) (c := 0) (by simpa only [sub_zero] using hbig) hε.symm (by simp)) hint

/-- Exact low/high boundary lock.  If a Dirichlet profile is split into low and high frequency
parts and the continuous high part has finite physical-log mass, then its low-frequency boundary
moment must vanish. -/
theorem lowFrequencyBoundaryMoment_eq_zero_of_physicalLogIntegrable_high
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (full low high : ℝ → E)
    (hsplit : ∀ r, full r = low r + high r)
    (hfull : full 0 = 0) (hhigh : ContinuousAt high 0)
    {ε : ℝ} (hε : ε ≠ 0)
    (hint : IntervalIntegrable (fun r : ℝ => ‖high r‖ ^ 2 / r) volume 0 ε) :
    low 0 = 0 := by
  have hh0 := physicalLogIntegrable_continuousAt_zero high hhigh hε hint
  have hs0 := hsplit 0
  rw [hfull, hh0, add_zero] at hs0
  exact hs0.symm

/-- Contrapositive source-facing form: a nonzero low-frequency boundary moment makes the
high-frequency profile inadmissible for the physical logarithmic carrier. -/
theorem not_physicalLogIntegrable_high_of_lowFrequencyBoundaryMoment_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (full low high : ℝ → E)
    (hsplit : ∀ r, full r = low r + high r)
    (hfull : full 0 = 0) (hhigh : ContinuousAt high 0)
    {ε : ℝ} (hε : ε ≠ 0) (hlow : low 0 ≠ 0) :
    ¬IntervalIntegrable (fun r : ℝ => ‖high r‖ ^ 2 / r) volume 0 ε := by
  intro hint
  exact hlow <|
    lowFrequencyBoundaryMoment_eq_zero_of_physicalLogIntegrable_high
      full low high hsplit hfull hhigh hε hint

/-- Renormalize the high-frequency profile by the single low-frequency boundary constant. -/
def boundaryMatchedHigh
    {E : Type*} [AddCommGroup E]
    (low high : ℝ → E) : ℝ → E :=
  fun r => high r + low 0

/-- Exact counterterm identity: matched high frequency equals the full profile minus the
boundary-vanishing low-frequency remainder. -/
theorem boundaryMatchedHigh_eq_full_sub_lowRemainder
    {E : Type*} [AddCommGroup E]
    (full low high : ℝ → E)
    (hsplit : ∀ r, full r = low r + high r) (r : ℝ) :
    boundaryMatchedHigh low high r = full r - (low r - low 0) := by
  simp only [boundaryMatchedHigh, hsplit]
  abel

/-- The boundary counterterm restores the exact Dirichlet value of the full profile. -/
theorem boundaryMatchedHigh_zero
    {E : Type*} [AddCommGroup E]
    (full low high : ℝ → E)
    (hsplit : ∀ r, full r = low r + high r)
    (hfull : full 0 = 0) :
    boundaryMatchedHigh low high 0 = 0 := by
  rw [boundaryMatchedHigh_eq_full_sub_lowRemainder full low high hsplit, hfull, sub_self, sub_zero]

/-- A Lipschitz low-frequency profile loses its boundary constant at physical rate `exp (-L)`
after the nonlinear boundary-log change of variables. -/
theorem lipschitz_boundaryLogRemainder_le
    {E : Type*} [PseudoMetricSpace E]
    {K : NNReal} (g : ℝ → E) (hg : LipschitzWith K g)
    (a L : ℝ) :
    dist (g (a - Real.exp (-L))) (g a) ≤ K * Real.exp (-L) := by
  calc
    dist (g (a - Real.exp (-L))) (g a) ≤
        K * dist (a - Real.exp (-L)) a := hg.dist_le_mul _ _
    _ = K * Real.exp (-L) := by
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos (Real.exp_pos _)]

/-- Changing the low-frequency cutoff changes the matched high profile only by the difference of
two boundary-vanishing low-frequency remainders. -/
theorem boundaryMatchedHigh_sub_boundaryMatchedHigh
    {E : Type*} [AddCommGroup E]
    (full low₁ high₁ low₂ high₂ : ℝ → E)
    (hsplit₁ : ∀ r, full r = low₁ r + high₁ r)
    (hsplit₂ : ∀ r, full r = low₂ r + high₂ r)
    (r : ℝ) :
    boundaryMatchedHigh low₁ high₁ r - boundaryMatchedHigh low₂ high₂ r =
      (low₂ r - low₂ 0) - (low₁ r - low₁ 0) := by
  rw [boundaryMatchedHigh_eq_full_sub_lowRemainder full low₁ high₁ hsplit₁,
    boundaryMatchedHigh_eq_full_sub_lowRemainder full low₂ high₂ hsplit₂]
  abel

end GaloisForLFunctions.RHTower
