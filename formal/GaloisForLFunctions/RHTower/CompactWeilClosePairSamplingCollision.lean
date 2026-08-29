import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Compact-Weil close-pair sampling collision

Two nearby point-evaluation reporters split exactly into an average channel and a difference
channel. At collision the difference channel disappears. If the reported profile is
differentiable, its difference energy is quadratically small in the separation, with normalized
limit equal to derivative energy.

This is a source-independent obstruction for compact-Weil and zero-sampling arguments: an
unrenormalized scalar sampling form loses one independent close-pair channel at order two. It
cannot obtain separation-uniform multiplicity resolution from point values alone. The split and
collision laws are unconditional. The quadratic law records its mathematically necessary
`HasDerivAt` premise explicitly; a downstream compact-Weil application must construct that
profile and discharge differentiability internally.
-/

open Filter Topology

noncomputable section

namespace RHTower

variable {F : Type*} [NormedAddCommGroup F]

/-- Sum of the two point-evaluation energies at separation `h`. -/
def compactWeilClosePairSamplingEnergy (f : ℝ → F) (x h : ℝ) : ℝ :=
  ‖f x‖ ^ 2 + ‖f (x + h)‖ ^ 2

/-- Energy of the antisymmetric channel of a point-evaluation pair. -/
def compactWeilClosePairDifferenceEnergy (f : ℝ → F) (x h : ℝ) : ℝ :=
  ‖f (x + h) - f x‖ ^ 2

/-- Two point evaluations split exactly into average and difference channels. -/
theorem compactWeilClosePair_samplingEnergy_split [InnerProductSpace ℝ F]
    (f : ℝ → F) (x h : ℝ) :
    compactWeilClosePairSamplingEnergy f x h =
      (1 / 2 : ℝ) * ‖f x + f (x + h)‖ ^ 2 +
        (1 / 2 : ℝ) * compactWeilClosePairDifferenceEnergy f x h := by
  have hp := parallelogram_law_with_norm ℝ (f x) (f (x + h))
  have hnorm : ‖f x - f (x + h)‖ = ‖f (x + h) - f x‖ := by
    rw [← norm_neg, neg_sub]
  rw [hnorm] at hp
  unfold compactWeilClosePairSamplingEnergy compactWeilClosePairDifferenceEnergy
  nlinarith

/-- At exact collision, two scalar point reporters become one reporter with doubled weight. -/
@[simp] theorem compactWeilClosePair_samplingEnergy_collision (f : ℝ → F) (x : ℝ) :
    compactWeilClosePairSamplingEnergy f x 0 = 2 * ‖f x‖ ^ 2 := by
  unfold compactWeilClosePairSamplingEnergy
  simp only [add_zero]
  ring

/-- At exact collision the antisymmetric reporter channel vanishes identically. -/
@[simp] theorem compactWeilClosePair_differenceEnergy_collision (f : ℝ → F) (x : ℝ) :
    compactWeilClosePairDifferenceEnergy f x 0 = 0 := by
  simp [compactWeilClosePairDifferenceEnergy]

/-- The normalized difference channel is literally the difference energy divided by separation
squared, including at zero under Lean's totalized inverse convention. -/
theorem compactWeilClosePair_normalizedDifference_eq
    [NormedSpace ℝ F] (f : ℝ → F) (x h : ℝ) :
    ‖h⁻¹ • (f (x + h) - f x)‖ ^ 2 =
      compactWeilClosePairDifferenceEnergy f x h / h ^ 2 := by
  unfold compactWeilClosePairDifferenceEnergy
  rw [norm_smul, Real.norm_eq_abs, abs_inv, mul_pow, inv_pow, sq_abs,
    div_eq_mul_inv]
  ring

/-- Quadratic close-pair law: after division by separation squared, the lost difference channel
converges exactly to derivative energy. -/
theorem tendsto_compactWeilClosePair_differenceEnergy_div_sq
    [NormedSpace ℝ F] {f : ℝ → F} {x : ℝ} {d : F} (hf : HasDerivAt f d x) :
    Tendsto (fun h : ℝ => compactWeilClosePairDifferenceEnergy f x h / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖d‖ ^ 2)) := by
  have hslope := hf.tendsto_slope_zero.norm.pow 2
  exact hslope.congr' (Filter.Eventually.of_forall fun h =>
    compactWeilClosePair_normalizedDifference_eq f x h)

end RHTower
