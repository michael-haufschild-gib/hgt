import GaloisForLFunctions.HTGeometry.TunableAbsorptionSum

/-!
# The tunable propagate step

Substituting uniform bounds `S` and `P` at the centre into the tunable absorption and absorbing the
`K_w²` term gives `K_w²(1 − δ) ≤ (1+ε)S²`, where `δ` bounds the displacement factor.

Stated multiplied out rather than as `K_w² ≤ (1+ε)S²/(1−δ)`, so no division and no `δ < 1` side
condition appear in the conclusion; a caller supplies whatever `δ` its chaining budget allows.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The tunable propagate step.** -/
theorem kernelRootQ_sq_le_tunable (h : PositiveMomentForm s) (z w : ℂ) {S P delta e : ℝ}
    (he : 0 < e)
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 4 * (1 + e⁻¹) *
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 * S ^ 2 * P ^ 2 ≤ delta)
    (N : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 * (1 - delta) ≤ (1 + e) * S ^ 2 := by
  have habs := kernelRoot_sq_le_absorption_tunable h N z w he
  have hKz0 : 0 ≤ kernelRoot s (fun j => monicOrthoC s j z) N := kernelRoot_nonneg _ _ _
  have hPz0 : 0 ≤ kernelRoot s (fun j => secondKindC s j z) N := kernelRoot_nonneg _ _ _
  have hKw0 : 0 ≤ kernelRoot s (fun j => monicOrthoC s j w) N := kernelRoot_nonneg _ _ _
  have hSn : 0 ≤ S := le_trans hKz0 (hS N)
  have hPn : 0 ≤ P := le_trans hPz0 (hP N)
  have hKzS : kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ hKz0 (hS N) 2
  have hPzP : kernelRoot s (fun j => secondKindC s j z) N ^ 2 ≤ P ^ 2 :=
    pow_le_pow_left₀ hPz0 (hP N) 2
  have hcoef : (0:ℝ) ≤ 4 * (1 + e⁻¹) *
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 := by positivity
  -- replace the centre kernels by their bounds in the displacement term
  have hdisp : 4 * (1 + e⁻¹) *
        (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
        kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
        kernelRoot s (fun j => secondKindC s j z) N ^ 2
      ≤ delta * kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 := by
    have hstep : 4 * (1 + e⁻¹) *
        (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
        kernelRoot s (fun j => secondKindC s j z) N ^ 2 ≤ delta := by
      refine le_trans ?_ hsmall
      gcongr
    have hmul := mul_le_mul_of_nonneg_right hstep
      (sq_nonneg (kernelRoot s (fun j => monicOrthoC s j w) N))
    nlinarith [hmul]
  have h1e : (1 + e) * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 ≤ (1 + e) * S ^ 2 := by
    have : (0:ℝ) < 1 + e := by linarith
    exact mul_le_mul_of_nonneg_left hKzS this.le
  linarith [habs, hdisp, h1e]

end HTGeometry
