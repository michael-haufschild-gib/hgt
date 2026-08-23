import GaloisForLFunctions.RHTower.CauchyKernelHardy

noncomputable section

/-!
# The Cauchy transform of a Hardy boundary function

Conjugation carries the Cauchy kernel at `w` to the kernel at `conj w`, so the kernels below the
axis span the Hardy space and those above it span its orthogonal complement.  Pairing an `L²`
boundary function against a kernel is exactly its Cauchy transform:

```text
∫ G(x)/(x - w) dx = ⟪1/(· - conj w), G⟫.
```

Hence the Cauchy transform of a Hardy boundary function vanishes at every point strictly below the
real axis — the boundary form of Cauchy's theorem for `H²`, and the analytic input needed to turn
orthogonality against the family `F_γ` into vanishing at the points `γ`.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform

namespace RHTower

theorem conj_im_ne {w : ℂ} (hw : w.im ≠ 0) : ((starRingEnd ℂ) w).im ≠ 0 := by
  simpa using hw

theorem star_cauchyKernelLp {w : ℂ} (hw : w.im ≠ 0) :
    star ((memLp_cauchyKernel hw).toLp (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - w)⁻¹))
      = (memLp_cauchyKernel (conj_im_ne hw)).toLp
          (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - (starRingEnd ℂ) w)⁻¹) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star
      ((memLp_cauchyKernel hw).toLp (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - w)⁻¹)),
    (memLp_cauchyKernel hw).coeFn_toLp,
    (memLp_cauchyKernel (conj_im_ne hw)).coeFn_toLp] with x h1 h2 h3
  rw [h1, Pi.star_apply, h2, h3]
  show (starRingEnd ℂ) ((((x : ℝ) : ℂ) - w)⁻¹) = (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)⁻¹
  rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- Above the axis the Cauchy kernel lies in the orthogonal complement of the Hardy space. -/
theorem cauchyKernel_mem_hardyL2_orthogonal {v : ℂ} (hv : 0 < v.im) :
    (memLp_cauchyKernel (ne_of_gt hv)).toLp
        (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹) ∈ hardyL2ᗮ := by
  have hconj : ((starRingEnd ℂ) v).im < 0 := by simpa using hv
  have hmem : (memLp_cauchyKernel (ne_of_lt hconj)).toLp
      (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - (starRingEnd ℂ) v)⁻¹) ∈ hardyL2 :=
    cauchyKernel_mem_hardyL2 hconj
  rw [← map_star_hardyL2]
  refine ⟨_, hmem, ?_⟩
  rw [lpStarₛₗ_apply, star_cauchyKernelLp (ne_of_lt hconj)]
  simp

/-- **The Cauchy transform of a Hardy boundary function vanishes below the axis.** -/
theorem integral_cauchyTransform_eq_zero {G : Lp ℂ 2 (volume : Measure ℝ)}
    (hG : G ∈ hardyL2) {w : ℂ} (hw : w.im < 0) :
    (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0 := by
  have hconj : 0 < ((starRingEnd ℂ) w).im := by simpa using hw
  set k : Lp ℂ 2 (volume : Measure ℝ) :=
    (memLp_cauchyKernel (ne_of_gt hconj)).toLp
      (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - (starRingEnd ℂ) w)⁻¹) with hk
  have hkmem : k ∈ hardyL2ᗮ := cauchyKernel_mem_hardyL2_orthogonal hconj
  have hzero : (inner ℂ k G : ℂ) = 0 :=
    inner_eq_zero_symm.mp (Submodule.mem_orthogonal _ _ |>.mp hkmem G hG)
  rw [← hzero, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [(memLp_cauchyKernel (ne_of_gt hconj)).coeFn_toLp] with x h1
  rw [RCLike.inner_apply]
  show (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)
    = (G : ℝ → ℂ) x * (starRingEnd ℂ) ((k : ℝ → ℂ) x)
  simp only [hk]
  rw [h1, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj, div_eq_mul_inv]

end RHTower
