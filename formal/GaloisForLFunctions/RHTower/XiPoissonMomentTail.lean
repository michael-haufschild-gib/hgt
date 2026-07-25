import GaloisForLFunctions.RHTower.XiPoissonMomentSummable
import GaloisForLFunctions.RHTower.XiPoissonBottomExtraction

/-!
# The moment-weighted tail vanishes

Step 1 of the real-variable converse.  Each derivative of the Poisson trace carries a factor
`alpha^^n`, and that factor is common to the bottom shell and to everything above it, so the spectral
gap suppresses the above-bottom part exactly as it did for the plain weight.  What survives the
weighting by `exp (g_1 v)` is the bottom shell alone.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **The moment-weighted extraction estimate.**  Weighting by the bottom height, the above-bottom
part of the `n`-th moment-weighted trace vanishes as the real time grows. -/
theorem tendsto_exp_bottomHeight_mul_aboveBottom_moment_tail {σ : ℝ} (hσ : 0 < σ) (n : ℕ)
    (hne : xiPoissonAboveBottom.Nonempty) :
    Tendsto
      (fun v : ℝ => Real.exp (xiPoissonBottomHeight * v) *
        ∑' q : xiPoissonAboveBottom,
          ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight (σ + v) (q : XiZeroCopy))
      atTop (nhds 0) := by
  classical
  obtain ⟨g₂, hgap, hg₂⟩ := exists_xiPoissonSecondHeight hne
  set C : ℝ := ∑' q : xiPoissonAboveBottom,
    ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight σ (q : XiZeroCopy) with hC
  have hsumσ : Summable (fun q : xiPoissonAboveBottom =>
      ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight σ (q : XiZeroCopy)) :=
    (summable_pow_mul_xiPoissonWeight hσ n).subtype _
  refine squeeze_zero'
    (g := fun v : ℝ => Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * C) ?_ ?_ ?_
  · filter_upwards with v
    refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun q => ?_)
    exact mul_nonneg (pow_nonneg (norm_nonneg _) n) (xiPoissonWeight_pos _ _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    have hsumv : Summable (fun q : xiPoissonAboveBottom =>
        ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight (σ + v) (q : XiZeroCopy)) :=
      (summable_pow_mul_xiPoissonWeight (by linarith : (0:ℝ) < σ + v) n).subtype _
    have hterm : ∀ q : xiPoissonAboveBottom,
        Real.exp (xiPoissonBottomHeight * v) *
            (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight (σ + v) (q : XiZeroCopy)) ≤
          Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
            (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight σ (q : XiZeroCopy)) := by
      intro q
      have hR : g₂ ≤ (xiPoissonPoint (q : XiZeroCopy)).re := hg₂ _ q.2
      have hw : Real.exp (xiPoissonBottomHeight * v) * xiPoissonWeight (σ + v) (q : XiZeroCopy) ≤
          Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * xiPoissonWeight σ (q : XiZeroCopy) := by
        rw [xiPoissonWeight, xiPoissonWeight, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hR, hv, hgap]
      have hpow : (0 : ℝ) ≤ ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n :=
        pow_nonneg (norm_nonneg _) n
      calc Real.exp (xiPoissonBottomHeight * v) *
            (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight (σ + v) (q : XiZeroCopy))
          = ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
              (Real.exp (xiPoissonBottomHeight * v) *
                xiPoissonWeight (σ + v) (q : XiZeroCopy)) := by ring
        _ ≤ ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
              (Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
                xiPoissonWeight σ (q : XiZeroCopy)) := mul_le_mul_of_nonneg_left hw hpow
        _ = Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
              (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
                xiPoissonWeight σ (q : XiZeroCopy)) := by ring
    calc Real.exp (xiPoissonBottomHeight * v) *
          ∑' q : xiPoissonAboveBottom,
            ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight (σ + v) (q : XiZeroCopy)
        = ∑' q : xiPoissonAboveBottom,
            Real.exp (xiPoissonBottomHeight * v) *
              (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
                xiPoissonWeight (σ + v) (q : XiZeroCopy)) := (tsum_mul_left).symm
      _ ≤ ∑' q : xiPoissonAboveBottom,
            Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) *
              (‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n *
                xiPoissonWeight σ (q : XiZeroCopy)) :=
          Summable.tsum_le_tsum hterm (hsumv.mul_left _) (hsumσ.mul_left _)
      _ = Real.exp (-((g₂ - xiPoissonBottomHeight) * v)) * C := tsum_mul_left
  · have hneg : -(g₂ - xiPoissonBottomHeight) < 0 := by linarith
    have h1 : Tendsto (fun v : ℝ => v * -(g₂ - xiPoissonBottomHeight)) atTop atBot :=
      Filter.Tendsto.atTop_mul_const_of_neg hneg Filter.tendsto_id
    have h2 : Tendsto (fun v : ℝ => Real.exp (-((g₂ - xiPoissonBottomHeight) * v)))
        atTop (nhds 0) := by
      have hcomp := Real.tendsto_exp_atBot.comp h1
      refine hcomp.congr fun v => ?_
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa using h2.mul_const C

end

end RHTower
