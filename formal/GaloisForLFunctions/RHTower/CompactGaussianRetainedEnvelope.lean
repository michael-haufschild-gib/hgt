import GaloisForLFunctions.RHTower.CompactDiscFirstMeanEnvelope
import GaloisForLFunctions.RHTower.CompactGaussianRetainedFirstMean

open Complex Filter Topology Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- The boundary envelope of the exact normalized retained arithmetic carrier. -/
def compactGaussianRetainedDiscEnvelope (c : ℂ) (r R : ℝ) (N L : ℕ)
    (S : Finset ℕ) (ω : Omega) : ℝ≥0∞ :=
  compactDiscFirstMeanEnvelope (fun η s => compactGaussianRetainedCarrier s N L S η) c r R ω

theorem measurable_compactGaussianRetainedDiscEnvelope (c : ℂ) (r R : ℝ) {N : ℕ}
    (hN : 0 < N) (L : ℕ) (S : Finset ℕ) :
    Measurable (compactGaussianRetainedDiscEnvelope c r R N L S) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  change Measurable (compactDiscFirstMeanEnvelope
    (fun η s => compactGaussianRetainedCarrier s N L S η) c r R)
  exact measurable_compactDiscFirstMeanEnvelope
    (fun η s => compactGaussianRetainedCarrier s N L S η)
    (measurable_compactGaussianRetainedCarrier_joint hNR L S) c r R

/-- Every point on the compact disc shares this one envelope. -/
theorem norm_le_compactGaussianRetainedDiscEnvelope (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {N : ℕ} (hN : 0 < N) (L : ℕ) (S : Finset ℕ)
    (ω : Omega) {s : ℂ} (hs : s ∈ closedBall c r) :
    ENNReal.ofReal (‖compactGaussianRetainedCarrier s N L S ω‖) ≤
      compactGaussianRetainedDiscEnvelope c r R N L S ω :=
  norm_le_compactDiscFirstMeanEnvelope _
    (fun η => differentiable_compactGaussianRetainedCarrier (by exact_mod_cast hN) L S η)
    c hr hrR ω hs

/-- The whole-disc envelope has vanishing original first mean, uniformly in
all retained prime sets and all independent polynomial cutoffs. -/
theorem eventually_lintegral_compactGaussianRetainedDiscEnvelope_le
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ,
      (∫⁻ ω, compactGaussianRetainedDiscEnvelope c r R N L S ω ∂steinhausMeasure) ≤
        ENNReal.ofReal δ := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  let η : ℝ := δ * (R - r) / R
  have hη : 0 < η := div_pos (mul_pos hδ hgap) hR
  filter_upwards [eventually_integral_norm_compactGaussianRetainedCarrier_band_le
    (a := c.re - R) (b := c.re + R) hc0 (by linarith) hc1 hη,
    eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro L S
  let F : Omega → ℂ → ℂ := fun ω s => compactGaussianRetainedCarrier s N L S ω
  have hFm : Measurable (fun q : Omega × ℂ => F q.1 q.2) :=
    measurable_compactGaussianRetainedCarrier_joint (by exact_mod_cast hN) L S
  have hpoint (θ : ℝ) : (∫⁻ ω, ENNReal.ofReal (‖F ω (circleMap c R θ)‖) ∂steinhausMeasure) ≤
      ENNReal.ofReal η := by
    have hs : circleMap c R θ ∈ closedBall c R := circleMap_mem_closedBall c hR.le θ
    have hre0 : |(circleMap c R θ).re - c.re| ≤ dist (circleMap c R θ) c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (circleMap c R θ - c)
    have hre := hre0.trans hs
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_compactGaussianRetainedCarrier _ N L S)
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hmean _ (by linarith [(abs_le.mp hre).1])
      (by linarith [(abs_le.mp hre).2]) L S)
  refine (lintegral_compactDiscFirstMeanEnvelope_le steinhausMeasure F hFm c r R η hpoint).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (R / (R - r)) * (2 * Real.pi)⁻¹),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((R / (R - r)) * (2 * Real.pi)⁻¹) * η)]
  congr 1
  dsimp only [η]
  field_simp [hR.ne', hgap.ne', Real.pi_ne_zero]

/-- The compact envelope uses only the retained coordinates. -/
theorem compactGaussianRetainedDiscEnvelope_congr_retained (c : ℂ) (r R : ℝ)
    (N L : ℕ) (S : Finset ℕ) {ω ξ : Omega} (h : ∀ p ∈ S, ω p = ξ p) :
    compactGaussianRetainedDiscEnvelope c r R N L S ω =
      compactGaussianRetainedDiscEnvelope c r R N L S ξ := by
  have heq (s : ℂ) : compactGaussianRetainedCarrier s N L S ω =
      compactGaussianRetainedCarrier s N L S ξ := by
    unfold compactGaussianRetainedCarrier
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply X_congr_of_eqOn_primeFactors
    intro p hp
    exact h p ((Sieve.mem_smoothUpTo.mp hn).2 hp)
  simp only [compactGaussianRetainedDiscEnvelope, compactDiscFirstMeanEnvelope, heq]

end RHTower
