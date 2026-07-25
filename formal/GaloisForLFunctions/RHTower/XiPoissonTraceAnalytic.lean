import GaloisForLFunctions.RHTower.XiPoissonVerticalType
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Analyticity of the Poisson zero trace

On a box `{sigma_0 < Re t} ∩ {|Im t| < M}` the Poisson multipliers are dominated by
`exp (M/2) * exp (-sigma_0 * R q)`, summable by `summable_xiPoissonWeight`, because the heights
`R q` are nonnegative and the displacements are bounded by `1/2`.  Weierstrass then gives
differentiability of the trace on each box, and boxes are a neighbourhood basis of the open right
half-plane, so the trace is analytic there.

The domination is exactly the unconditional envelope of `XiPoissonVerticalType`: it is the bounded
displacement, not any hypothesis on the zeros, that makes the trace an analytic function of the
heat time.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A box in the open right half-plane. -/
def xiPoissonBox (σ₀ M : ℝ) : Set ℂ := {t : ℂ | σ₀ < t.re ∧ |t.im| < M}

theorem isOpen_xiPoissonBox (σ₀ M : ℝ) : IsOpen (xiPoissonBox σ₀ M) := by
  refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re) ?_
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem differentiable_xiPoissonTerm (q : XiZeroCopy) :
    Differentiable ℂ (fun τ : ℂ => xiPoissonTerm τ q) := by
  unfold xiPoissonTerm
  fun_prop

/-- Uniform domination of the multipliers on a box. -/
theorem norm_xiPoissonTerm_le_on_box {σ₀ M : ℝ} (q : XiZeroCopy) {t : ℂ}
    (ht : t ∈ xiPoissonBox σ₀ M) :
    ‖xiPoissonTerm t q‖ ≤ Real.exp (M / 2) * xiPoissonWeight σ₀ q := by
  obtain ⟨hre, him⟩ := ht
  rw [norm_xiPoissonTerm, xiPoissonWeight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hR : 0 ≤ (xiPoissonPoint q).re := xiPoissonPoint_re_nonneg q
  have hJ : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  have h1 : σ₀ * (xiPoissonPoint q).re ≤ t.re * (xiPoissonPoint q).re :=
    mul_le_mul_of_nonneg_right hre.le hR
  have h2 : t.im * (xiPoissonPoint q).im ≤ M / 2 := by
    calc t.im * (xiPoissonPoint q).im ≤ |t.im * (xiPoissonPoint q).im| := le_abs_self _
      _ = |t.im| * |(xiPoissonPoint q).im| := abs_mul _ _
      _ ≤ M * (1 / 2) := by
          refine mul_le_mul him.le hJ.le (abs_nonneg _) ?_
          exact le_trans (abs_nonneg _) him.le
      _ = M / 2 := by ring
  linarith

/-- The Poisson trace is differentiable on every box of the open right half-plane. -/
theorem differentiableOn_xiPoissonTraceC_box {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ xiPoissonTraceC (xiPoissonBox σ₀ M) := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : XiZeroCopy => Real.exp (M / 2) * xiPoissonWeight σ₀ q)
    ((summable_xiPoissonWeight hσ₀).mul_left _)
    (fun q => (differentiable_xiPoissonTerm q).differentiableOn)
    (isOpen_xiPoissonBox σ₀ M)
    (fun q t ht => norm_xiPoissonTerm_le_on_box q ht)

/-- The Poisson trace is differentiable at every point of the open right half-plane. -/
theorem differentiableAt_xiPoissonTraceC {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ xiPoissonTraceC t := by
  have hmem : t ∈ xiPoissonBox (t.re / 2) (|t.im| + 1) :=
    ⟨by linarith, by linarith⟩
  refine (differentiableOn_xiPoissonTraceC_box (M := |t.im| + 1)
    (by linarith : (0 : ℝ) < t.re / 2)).differentiableAt ?_
  exact (isOpen_xiPoissonBox _ _).mem_nhds hmem

/-- **The Poisson trace is analytic on the open right half-plane**, with no hypothesis on the
zeros. -/
theorem analyticOnNhd_xiPoissonTraceC :
    AnalyticOnNhd ℂ xiPoissonTraceC {t : ℂ | 0 < t.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro t ht
  exact (differentiableAt_xiPoissonTraceC ht).differentiableWithinAt

end

end RHTower
