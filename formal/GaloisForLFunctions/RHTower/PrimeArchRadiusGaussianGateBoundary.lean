import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

namespace RHTower
noncomputable section

/-!
# An algebraic boundary test for the radius-mixing determinant gate

For the normalized moment tuple `(a,b,c,e)=(1,3-t,15,105)`, the radius
gate is negative for every sufficiently small positive `t`.  This is a
closed algebraic obstruction to deducing its sign from the generic radius
Gram inequality.  Realization by a decreasing density is a separate step.
-/

private def toyV (t : ℝ) : ℝ := t / 6
private def toyW (t : ℝ) : ℝ := t / 8
private def toyZ (t : ℝ) : ℝ := t / 24 + t ^ 2 / 144
private def toyD (t : ℝ) : ℝ := toyW t - toyV t ^ 2
private def toyQR (t : ℝ) : ℝ := 21 * 15 - 25 * (3 - t) ^ 2
private def toyPR (t : ℝ) : ℝ :=
  243 * 105 ^ 2 - 630 * (3 - t) * 15 * 105 + 343 * 15 ^ 3
private def toyB (t : ℝ) : ℝ :=
  9 * 105 - 504 * toyV t * 15 + 15120 * toyW t * (3 - t) - 181440 * toyZ t
private def toyC (t : ℝ) : ℝ :=
  toyZ t ^ 2 - 2 * toyV t * toyW t * toyZ t + toyW t ^ 3
private def toyP (t : ℝ) : ℝ := toyPR t - 11 * toyQR t * toyB t
/-- The four-moment radius gate for `(a,b,c,e)=(1,3-t,15,105)`. -/
def radiusGaussianPerturbationGate (t : ℝ) : ℝ :=
  toyD t * toyP t - 11 * toyQR t * 362880 * toyC t

private theorem toyC_square (t : ℝ) :
    toyC t = (toyZ t - toyV t * toyW t) ^ 2 + toyW t ^ 2 * toyD t := by
  dsimp [toyC, toyD]
  ring

/-- The radius-mixing four-moment gate is strictly negative near the
Gaussian tuple on the side with positive first prime--archimedean moment. -/
theorem radiusGaussianPerturbationGate_neg_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      radiusGaussianPerturbationGate t < 0 := by
  have hP0 : toyP 0 < 0 := by
    norm_num [toyP, toyPR, toyQR, toyB, toyV, toyW, toyZ]
  have hcont : Continuous toyP := by
    unfold toyP toyPR toyQR toyB toyV toyW toyZ
    fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), toyP t < 0 :=
    hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hP0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro t ht htmin
  have htδ : t < δ := lt_of_lt_of_le htmin (min_le_left δ 1)
  have ht1 : t < 1 := lt_of_lt_of_le htmin (min_le_right δ 1)
  have hP : toyP t < 0 := hball (by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htδ)
  have hd : 0 < toyD t := by
    have heq : toyD t = t * (9 / 2 - t) / 36 := by
      dsimp [toyD, toyW, toyV]
      ring
    rw [heq]
    exact div_pos (mul_pos ht (by linarith)) (by norm_num)
  have hq : 0 < toyQR t := by
    have ht2 : t ^ 2 < t := by nlinarith [mul_pos ht (sub_pos.mpr ht1)]
    dsimp [toyQR]
    nlinarith
  have hc : 0 ≤ toyC t := by
    rw [toyC_square]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hd.le)
  have hneg : toyD t * toyP t < 0 := mul_neg_of_pos_of_neg hd hP
  have hnonneg : 0 ≤ 11 * toyQR t * 362880 * toyC t := by positivity
  dsimp [radiusGaussianPerturbationGate]
  linarith

/-- The negative gate persists together with the low-order strict signs used
in the literal theta-source reductions.  The moments here remain algebraic
test data, not the completed theta moments. -/
theorem radiusGaussianPerturbationGate_neg_with_sourceLikeSigns :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      radiusGaussianPerturbationGate t < 0 ∧
      0 < toyV t ∧ 0 < 1 - 18 * toyV t ∧
      0 < 15 - (3 - t) ^ 2 ∧ 0 < toyQR t ∧
      14 * (3 - t) ^ 2 < 9 * 15 := by
  obtain ⟨ε₀, hε₀, hneg⟩ := radiusGaussianPerturbationGate_neg_near_zero
  refine ⟨min ε₀ (1 / 4), lt_min hε₀ (by norm_num), ?_⟩
  intro t ht htmin
  have htε₀ : t < ε₀ := lt_of_lt_of_le htmin (min_le_left ε₀ (1 / 4))
  have ht4 : t < 1 / 4 := lt_of_lt_of_le htmin (min_le_right ε₀ (1 / 4))
  have ht2 : t ^ 2 < t := by
    nlinarith [mul_pos ht (show 0 < 1 - t by linarith)]
  refine ⟨hneg t ht htε₀, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [toyV]
    linarith
  · dsimp [toyV]
    linarith
  · nlinarith
  · dsimp [toyQR]
    nlinarith
  · nlinarith

end
end RHTower
