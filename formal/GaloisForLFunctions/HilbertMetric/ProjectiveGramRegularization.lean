import GaloisForLFunctions.HilbertMetric.GaussianCoherentFisherClock

/-!
# Quantitative regularization of projective Gram area

Adding a nonnegative scalar to both diagonal entries of a two-channel Gram matrix changes its
area by at most the square root of `δ * trace + δ²`. The estimate survives dependent vectors and
stationary coherent trajectories. The exact rationalized error records the better rate away
from zero area, without introducing a spectral-gap premise.

The mechanism was identified in differential-geometry's
`Analysis/SpecialFunctions/Sqrt/GramDeterminant.lean` at revision
`7a48598d35109aa99d1cc678e2724c213cdf4ff3`. These proofs use the existing projective Gram energy
and Gaussian coherent-clock coordinates; no upstream definitions are imported.
-/

noncomputable section

open scoped NNReal

namespace GaloisForLFunctions.HilbertMetric

open _root_.HTGeometry

/-- Diagonal regularization adds precisely the trace term and the squared regularizer. -/
theorem projectiveQuantumTangentValue_regularization (mass overlap speedSq δ : ℝ) :
    projectiveQuantumTangentValue (mass + δ) overlap (speedSq + δ) =
      projectiveQuantumTangentValue mass overlap speedSq + δ * (mass + speedSq) + δ ^ 2 := by
  unfold projectiveQuantumTangentValue
  ring

private theorem sqrt_increment_estimate {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Real.sqrt (a + b) - Real.sqrt a ∧
      Real.sqrt (a + b) - Real.sqrt a ≤ Real.sqrt b ∧
        (Real.sqrt (a + b) - Real.sqrt a) *
          (Real.sqrt (a + b) + Real.sqrt a) = b := by
  have hab := Real.sq_sqrt (add_nonneg ha hb)
  have ha' := Real.sq_sqrt ha
  have hb' := Real.sq_sqrt hb
  refine ⟨sub_nonneg.mpr (Real.sqrt_le_sqrt (le_add_of_nonneg_right hb)), ?_, ?_⟩
  · have h := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    have hs : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    linarith
  · nlinarith

private theorem regularization_estimate {mass overlap speedSq : ℝ}
    (hm : 0 ≤ mass) (hs : 0 ≤ speedSq)
    (hg : 0 ≤ projectiveQuantumTangentValue mass overlap speedSq) (δ : ℝ≥0) :
    let A := Real.sqrt (projectiveQuantumTangentValue (mass + δ) overlap (speedSq + δ))
    let B := Real.sqrt (projectiveQuantumTangentValue mass overlap speedSq)
    0 ≤ A - B ∧ A - B ≤ Real.sqrt ((δ : ℝ) * (mass + speedSq) + (δ : ℝ) ^ 2) ∧
      (A - B) * (A + B) = (δ : ℝ) * (mass + speedSq) + (δ : ℝ) ^ 2 := by
  dsimp only
  rw [projectiveQuantumTangentValue_regularization, add_assoc]
  exact sqrt_increment_estimate hg (by positivity)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Intrinsic Gram area has a uniform square-root regularization bound, even at rank loss. -/
theorem projectiveGram_regularization_area_bounds (v w : E) (δ : ℝ≥0) :
    let A := Real.sqrt (projectiveQuantumTangentValue
      (‖v‖ ^ 2 + δ) ‖inner 𝕜 v w‖ (‖w‖ ^ 2 + δ))
    let B := Real.sqrt (projectiveGramTangentEnergy (𝕜 := 𝕜) v w)
    0 ≤ A - B ∧ A - B ≤
      Real.sqrt ((δ : ℝ) * (‖v‖ ^ 2 + ‖w‖ ^ 2) + (δ : ℝ) ^ 2) := by
  have h := regularization_estimate (sq_nonneg ‖v‖) (sq_nonneg ‖w‖)
    (projectiveGramTangentEnergy_nonneg (𝕜 := 𝕜) v w) δ
  exact ⟨h.1, h.2.1⟩

/-- Exact area-error identity; no division is required at a singular Gram pair. -/
theorem projectiveGram_regularization_area_error (v w : E) (δ : ℝ≥0) :
    let A := Real.sqrt (projectiveQuantumTangentValue
      (‖v‖ ^ 2 + δ) ‖inner 𝕜 v w‖ (‖w‖ ^ 2 + δ))
    let B := Real.sqrt (projectiveGramTangentEnergy (𝕜 := 𝕜) v w)
    (A - B) * (A + B) = (δ : ℝ) * (‖v‖ ^ 2 + ‖w‖ ^ 2) + (δ : ℝ) ^ 2 :=
  (regularization_estimate (sq_nonneg ‖v‖) (sq_nonneg ‖w‖)
    (projectiveGramTangentEnergy_nonneg (𝕜 := 𝕜) v w) δ).2.2

/-- The coherent-clock Gram determinant is its mass squared times Euclidean speed squared. -/
theorem coherentClock_projective_value {d : ℕ} (x v : Fin d → ℝ) :
    projectiveQuantumTangentValue (coherentClockMass x) (coherentClockOverlap x v)
      (coherentClockTangentSq x v) = coherentClockMass x ^ 2 * ∑ i, v i ^ 2 := by
  rw [coherentClockOverlap_formula, coherentClockTangentSq_formula]
  unfold projectiveQuantumTangentValue
  ring

/-- Coherent-clock projective area has an exact formula, including stationary trajectories. -/
theorem coherentClock_projective_area {d : ℕ} (x v : Fin d → ℝ) :
    Real.sqrt (projectiveQuantumTangentValue (coherentClockMass x)
      (coherentClockOverlap x v) (coherentClockTangentSq x v)) =
      coherentClockMass x * Real.sqrt (∑ i, v i ^ 2) := by
  rw [coherentClock_projective_value, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (coherentClockMass_pos x).le]

/-- Error control for diagonal regularization of the actual Gaussian value/cross/jet block. -/
theorem coherentClock_regularization_area_bounds {d : ℕ} (x v : Fin d → ℝ) (δ : ℝ≥0) :
    let A := Real.sqrt (projectiveQuantumTangentValue (coherentClockMass x + δ)
      (coherentClockOverlap x v) (coherentClockTangentSq x v + δ))
    let B := coherentClockMass x * Real.sqrt (∑ i, v i ^ 2)
    0 ≤ A - B ∧ A - B ≤
      Real.sqrt ((δ : ℝ) * (coherentClockMass x + coherentClockTangentSq x v) + (δ : ℝ) ^ 2) := by
  have hs : 0 ≤ coherentClockTangentSq x v := by
    rw [coherentClockTangentSq_formula]
    exact mul_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))
      (coherentClockMass_pos x).le
  have hg : 0 ≤ projectiveQuantumTangentValue (coherentClockMass x)
      (coherentClockOverlap x v) (coherentClockTangentSq x v) := by
    rw [coherentClock_projective_value]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h := regularization_estimate (coherentClockMass_pos x).le hs hg δ
  rw [coherentClock_projective_area] at h
  exact ⟨h.1, h.2.1⟩

/-- At zero velocity the square-root error bound is attained exactly. -/
theorem coherentClock_regularization_stationary {d : ℕ} (x : Fin d → ℝ) (δ : ℝ≥0) :
    Real.sqrt (projectiveQuantumTangentValue (coherentClockMass x + δ)
      (coherentClockOverlap x 0) (coherentClockTangentSq x 0 + δ)) =
      Real.sqrt ((δ : ℝ) * coherentClockMass x + (δ : ℝ) ^ 2) := by
  rw [coherentClockOverlap_formula, coherentClockTangentSq_formula]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_add, zero_mul]
  congr 1
  unfold projectiveQuantumTangentValue
  ring

end GaloisForLFunctions.HilbertMetric
