import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Constructions

/-!
# Radius of convergence versus genuine singularity

A scalar power series centred at `z₀` whose sum represents a function `f` on the
ball of radius `R` cannot have radius larger than `R` unless `f` continues
analytically past that ball: the sum of the series *is* the continuation.

This is the second half of the Hadamard argument for the radius of a
shift-lattice expansion.  The first half — that the radius is at least the
distance to the nearest singularity — is convergence; this half is the
contrapositive of analytic continuation, and it is what turns a lower bound on
the growth functional into an exact value.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- The sum function of a scalar power series, recentred at `z₀`. -/
noncomputable def shiftSumFun (c : ℕ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ c).sum (z - z₀)

theorem shiftSumFun_eq_tsum (c : ℕ → ℂ) (z₀ z : ℂ) :
    shiftSumFun c z₀ z = ∑' k : ℕ, c k * (z - z₀) ^ k := by
  rw [shiftSumFun, FormalMultilinearSeries.sum]
  refine tsum_congr fun k => ?_
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- The recentred sum function is analytic on every ball inside the radius. -/
theorem analyticOnNhd_shiftSumFun {c : ℕ → ℂ} (z₀ : ℂ) {R : ℝ} (hR : 0 < R)
    (hrad : ENNReal.ofReal R ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    AnalyticOnNhd ℂ (shiftSumFun c z₀) (Metric.ball z₀ R) := by
  have hRpos : (0 : ℝ≥0∞) < ENNReal.ofReal R := by
    simpa using hR
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    lt_of_lt_of_le hRpos hrad
  have hball :=
    ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall hpos).analyticOnNhd
  intro z hz
  have hlt : ‖z - z₀‖ < R := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    exact hz
  have hsub : (z - z₀) ∈ Metric.eball (0 : ℂ)
      (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _) |>.mpr hlt
  have h1 : AnalyticAt ℂ (FormalMultilinearSeries.ofScalars ℂ c).sum (z - z₀) :=
    hball _ hsub
  have h2 : AnalyticAt ℂ (fun w : ℂ => w - z₀) z :=
    analyticAt_id.sub analyticAt_const
  have hcomp := AnalyticAt.comp (𝕜 := ℂ)
    (g := (FormalMultilinearSeries.ofScalars ℂ c).sum)
    (f := fun w : ℂ => w - z₀) (x := z) h1 h2
  show AnalyticAt ℂ
    (fun w : ℂ => (FormalMultilinearSeries.ofScalars ℂ c).sum (w - z₀)) z
  exact hcomp

/-- **Radius versus continuation.**  A radius larger than `R` produces an
analytic continuation of the represented function to the larger ball. -/
theorem exists_analytic_extension_of_lt_radius {c : ℕ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    (hsum : ∀ ζ : ℂ, ‖ζ‖ < R → HasSum (fun k : ℕ => c k * ζ ^ k) (f (z₀ + ζ)))
    (hrad : ENNReal.ofReal R' ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball z₀ R')
      ∧ ∀ z ∈ Metric.ball z₀ R, g z = f z := by
  refine ⟨shiftSumFun c z₀,
    analyticOnNhd_shiftSumFun z₀ (hR.trans hRR') hrad, fun z hz => ?_⟩
  rw [shiftSumFun_eq_tsum]
  have hlt : ‖z - z₀‖ < R := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    exact hz
  rw [(hsum (z - z₀) hlt).tsum_eq]
  congr 1
  ring

/-- **A genuine singularity caps the radius.**  If the represented function
admits no analytic extension to any larger ball, the radius is at most `R`. -/
theorem radius_le_of_no_analytic_extension {c : ℕ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    {R : ℝ} (hR : 0 < R)
    (hsum : ∀ ζ : ℂ, ‖ζ‖ < R → HasSum (fun k : ℕ => c k * ζ ^ k) (f (z₀ + ζ)))
    (hsing : ∀ R' : ℝ, R < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball z₀ R')
        ∧ ∀ z ∈ Metric.ball z₀ R, g z = f z) :
    (FormalMultilinearSeries.ofScalars ℂ c).radius ≤ ENNReal.ofReal R := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hcon
  have httop : t ≠ ⊤ := ne_top_of_lt ht2
  have hRlt : R < t.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal hR.le httop).mp ht1
    exact this
  have hle : ENNReal.ofReal t.toReal
      ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [ENNReal.ofReal_toReal httop]
    exact ht2.le
  exact hsing t.toReal hRlt
    (exists_analytic_extension_of_lt_radius hR hRlt hsum hle)

/-- **The growth functional at a genuine singularity.**  The Cauchy--Hadamard
growth functional is at least the reciprocal of the distance to the
singularity. -/
theorem le_hadamardLimsup_of_no_analytic_extension {c : ℕ → ℂ} {f : ℂ → ℂ}
    {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hsum : ∀ ζ : ℂ, ‖ζ‖ < R → HasSum (fun k : ℕ => c k * ζ ^ k) (f (z₀ + ζ)))
    (hsing : ∀ R' : ℝ, R < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball z₀ R')
        ∧ ∀ z ∈ Metric.ball z₀ R, g z = f z) :
    ENNReal.ofReal (1 / R) ≤ hadamardLimsup c := by
  have hrad := radius_le_of_no_analytic_extension hR hsum hsing
  rw [radius_ofScalars_eq_inv_hadamardLimsup] at hrad
  have h := ENNReal.inv_le_iff_inv_le.mp hrad
  rwa [← ENNReal.ofReal_inv_of_pos hR, ← one_div] at h

/-- **Unboundedness is a genuine singularity.**  A function unbounded on the ball
admits no analytic extension to any larger ball: such an extension would be
continuous on the compact closed ball and hence bounded there. -/
theorem no_analytic_extension_of_unbounded {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hunb : ∀ M : ℝ, ∃ z ∈ Metric.ball z₀ R, M < ‖f z‖) :
    ∀ R' : ℝ, R < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball z₀ R')
        ∧ ∀ z ∈ Metric.ball z₀ R, g z = f z := by
  rintro R' hRR' ⟨g, hg, hgf⟩
  have hsub : Metric.closedBall z₀ R ⊆ Metric.ball z₀ R' :=
    Metric.closedBall_subset_ball hRR'
  have hcont : ContinuousOn g (Metric.closedBall z₀ R) :=
    (hg.mono hsub).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ R).exists_bound_of_continuousOn hcont
  obtain ⟨z, hz, hzM⟩ := hunb M
  have hzc : z ∈ Metric.closedBall z₀ R := Metric.ball_subset_closedBall hz
  have : ‖f z‖ ≤ M := by
    rw [← hgf z hz]
    exact hM z hzc
  linarith

/-- **An unbounded function caps the radius.**  Combining the two previous
results: if the represented function is unbounded on the ball of radius `R`, the
expansion has radius at most `R`. -/
theorem radius_le_of_unbounded {c : ℕ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hsum : ∀ ζ : ℂ, ‖ζ‖ < R → HasSum (fun k : ℕ => c k * ζ ^ k) (f (z₀ + ζ)))
    (hunb : ∀ M : ℝ, ∃ z ∈ Metric.ball z₀ R, M < ‖f z‖) :
    (FormalMultilinearSeries.ofScalars ℂ c).radius ≤ ENNReal.ofReal R :=
  radius_le_of_no_analytic_extension hR hsum (no_analytic_extension_of_unbounded hunb)

end GaloisForLFunctions.HTGeometry
