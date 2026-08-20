import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot

/-!
# The principal square root is Lipschitz relative to its own real part

For two points of the open right half plane the difference of principal roots is the difference of
the arguments divided by the sum of the roots, and that sum has real part at least either root's.
So a perturbation of the argument moves the root by at most the perturbation divided by the root:
in the far field, where the root is large, a bounded perturbation of the argument moves the root by
a bounded amount even though the argument itself moves by a large amount.
-/

open Complex

namespace HTGeometry

/-- **The root difference is controlled by the argument difference over the root.** -/
private theorem norm_csqrt_sub_le {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    ‖csqrt z - csqrt w‖ ≤ ‖z - w‖ / csqrtRe w := by
  have hzr : 0 < csqrtRe z := csqrtRe_pos hz
  have hwr : 0 < csqrtRe w := csqrtRe_pos hw
  have hfac : (csqrt z - csqrt w) * (csqrt z + csqrt w) = z - w := by
    have h1 : csqrt z ^ 2 = z := csqrt_sq hz
    have h2 : csqrt w ^ 2 = w := csqrt_sq hw
    linear_combination h1 - h2
  have hsumre : csqrtRe w ≤ (csqrt z + csqrt w).re := by
    rw [Complex.add_re, csqrt_re, csqrt_re]
    linarith
  have hsum : csqrtRe w ≤ ‖csqrt z + csqrt w‖ :=
    le_trans hsumre (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  have hsum0 : (0 : ℝ) < ‖csqrt z + csqrt w‖ := lt_of_lt_of_le hwr hsum
  have hnorm : ‖csqrt z - csqrt w‖ * ‖csqrt z + csqrt w‖ = ‖z - w‖ := by
    rw [← norm_mul, hfac]
  rw [le_div_iff₀ hwr]
  calc ‖csqrt z - csqrt w‖ * csqrtRe w
      ≤ ‖csqrt z - csqrt w‖ * ‖csqrt z + csqrt w‖ :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖z - w‖ := hnorm

/-- **The real part of the root moves by at most the argument perturbation over the root.** -/
theorem csqrtRe_sub_le {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    csqrtRe w - ‖z - w‖ / csqrtRe w ≤ csqrtRe z := by
  have hdiff : |csqrtRe z - csqrtRe w| ≤ ‖csqrt z - csqrt w‖ := by
    have h := Complex.abs_re_le_norm (csqrt z - csqrt w)
    rwa [Complex.sub_re, csqrt_re, csqrt_re] at h
  have hle := norm_csqrt_sub_le hz hw
  have habs : csqrtRe w - csqrtRe z ≤ ‖z - w‖ / csqrtRe w := by
    have h1 : csqrtRe w - csqrtRe z ≤ |csqrtRe z - csqrtRe w| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  linarith

end HTGeometry
