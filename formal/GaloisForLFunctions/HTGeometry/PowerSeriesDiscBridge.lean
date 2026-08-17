import Mathlib

/-!
# Scalar power series on a disc

Two conversions between a holomorphic function on a disc and a bounded coefficient sequence.

* a sequence with `‖c n‖ r ^ n` bounded sums to a function holomorphic on the ball of radius `r`;
* a function holomorphic on a closed ball of radius `R` is the sum of such a series, with the bound
  available for every `r < R`.

Together they say that "holomorphic on a disc" is *equivalent* to a countable list of numbers with
geometric bounds, which is what makes continuation to a disc an arithmetically explicit condition
rather than an existential over a function space.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The sum of a scalar power series. -/
def seriesSum (c : ℕ → ℂ) (w : ℂ) : ℂ := ∑' n : ℕ, c n * w ^ n

theorem seriesSum_eq_ofScalarsSum (c : ℕ → ℂ) :
    seriesSum c = (FormalMultilinearSeries.ofScalars ℂ c).sum := by
  funext w
  rw [seriesSum, ← FormalMultilinearSeries.ofScalarsSum]
  rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  exact tsum_congr fun n => by rw [smul_eq_mul]

/-- **A geometrically bounded coefficient sequence sums to a holomorphic function on the disc.** -/
theorem analyticOnNhd_seriesSum {c : ℕ → ℂ} {B r : ℝ} (hr : 0 < r)
    (hc : ∀ n : ℕ, ‖c n‖ * r ^ n ≤ B) :
    AnalyticOnNhd ℂ (seriesSum c) (Metric.ball 0 r) := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hnorm : ∀ n : ℕ, ‖p n‖ = ‖c n‖ := fun n => FormalMultilinearSeries.ofScalars_norm ℂ c n
  have hrad : (r.toNNReal : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound B ?_
    intro n
    rw [hnorm n]
    have : ((r.toNNReal : ℝ)) = r := Real.coe_toNNReal r hr.le
    simpa [this] using hc n
  have hpos : 0 < p.radius := lt_of_lt_of_le (by
    simpa [ENNReal.coe_pos, Real.toNNReal_pos] using hr) hrad
  have hball := p.hasFPowerSeriesOnBall hpos
  have hana : AnalyticOnNhd ℂ p.sum (Metric.eball 0 p.radius) := hball.analyticOnNhd
  rw [seriesSum_eq_ofScalarsSum c, ← hp]
  intro w hw
  refine hana w ?_
  have hlt : (‖w‖₊ : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ hrad
    have hw' : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    simpa [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal r hr.le] using hw'
  exact mem_eball_zero_iff.mpr hlt

/-- The coefficient of a scalar power series is bounded by the norm of its term. -/
theorem norm_coeff_le_norm (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    ‖p.coeff n‖ ≤ ‖p n‖ := by
  have h := (p n).le_opNorm (fun _ : Fin n => (1 : ℂ))
  simp only [norm_one, Finset.prod_const_one, mul_one] at h
  exact h

/-- **A function holomorphic on a closed disc is the sum of a geometrically bounded series.** -/
theorem exists_seriesSum_of_differentiableOn {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ R))
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    ∃ (c : ℕ → ℂ) (B : ℝ), (∀ n : ℕ, ‖c n‖ * r ^ n ≤ B) ∧
      ∀ w : ℂ, ‖w‖ < R → f (z₀ + w) = seriesSum c w := by
  have hRnn : ((R.toNNReal : ℝ)) = R := Real.coe_toNNReal R hR.le
  have hfball : DifferentiableOn ℂ f (Metric.closedBall z₀ (R.toNNReal : ℝ)) := by
    rwa [hRnn]
  have hpos : 0 < R.toNNReal := by simpa [Real.toNNReal_pos] using hR
  have hball := hfball.hasFPowerSeriesOnBall hpos
  set p := cauchyPowerSeries f z₀ (R.toNNReal : ℝ) with hp
  refine ⟨fun n => p.coeff n, ?_, ?_, ?_⟩
  · exact Classical.choose (p.norm_mul_pow_le_of_lt_radius (r := r.toNNReal) (by
      refine lt_of_lt_of_le ?_ hball.r_le
      have : ((r.toNNReal : ℝ)) < (R.toNNReal : ℝ) := by
        rw [Real.coe_toNNReal r hr0.le, hRnn]; exact hrR
      exact_mod_cast this))
  · intro n
    have hspec := Classical.choose_spec (p.norm_mul_pow_le_of_lt_radius (r := r.toNNReal) (by
      refine lt_of_lt_of_le ?_ hball.r_le
      have : ((r.toNNReal : ℝ)) < (R.toNNReal : ℝ) := by
        rw [Real.coe_toNNReal r hr0.le, hRnn]; exact hrR
      exact_mod_cast this))
    have hbn := hspec.2 n
    have hcr : ((r.toNNReal : ℝ)) = r := Real.coe_toNNReal r hr0.le
    calc ‖p.coeff n‖ * r ^ n ≤ ‖p n‖ * r ^ n := by
          refine mul_le_mul_of_nonneg_right (norm_coeff_le_norm p n) (by positivity)
      _ ≤ _ := by simpa [hcr] using hbn
  · intro w hw
    have hmem : w ∈ Metric.eball (0 : ℂ) ((R.toNNReal : ENNReal)) := by
      refine mem_eball_zero_iff.mpr ?_
      have hlt : ‖w‖ < (R.toNNReal : ℝ) := by rwa [hRnn]
      exact_mod_cast hlt
    have hsum := hball.hasSum (y := w) hmem
    have hterm : ∀ n : ℕ, (p n fun _ => w) = p.coeff n * w ^ n := by
      intro n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
      ring
    rw [seriesSum]
    refine (HasSum.tsum_eq ?_).symm
    simpa [hterm] using hsum

end GaloisForLFunctions.HTGeometry

end
