import GaloisForLFunctions.HTGeometry.CauchyKernelMellin
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# The Mellin integrand of a canonical product, and its decay on horizontal lines

The Mellin representation of `∑_{n ≥ 1} x / (n^s + x)` has integrand

```text
F(w) = x^{-w} ζ(-s w) · (-π / sin (π w)) .
```

Two of its three factors are harmless on a vertical strip: `x^{-w}` depends only on the abscissa,
and `ζ(-sw)` grows at most polynomially in the height.  The third decays like `e^{-π|t|}`.  So the
whole integrand decays exponentially, uniformly in the abscissa on any compact range.  That single
estimate supplies both the vertical integrability of each contour and the vanishing of the
horizontal sides of every rectangle used to shift between contours.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- The Mellin integrand of the canonical-product logarithmic derivative. -/
def barnesIntegrand (s x : ℝ) (w : ℂ) : ℂ :=
  ((x : ℝ) : ℂ) ^ (-w) * riemannZeta (-(s : ℂ) * w)
    * (-((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)))

/-- A positive base raised to a bounded exponent is bounded. -/
theorem exists_bound_rpow_neg {x : ℝ} (hx : 0 < x) (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ σ₁ → x ^ (-σ) ≤ C := by
  have hrw : ∀ u : ℝ, x ^ u = Real.exp (Real.log x * u) := fun u => Real.rpow_def_of_pos hx u
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (Real.log x * u)) (Icc (-σ₁) (-σ₀)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -σ₁) (b := -σ₀)).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ h0 h1 => ?_⟩
  have hmem : (-σ) ∈ Icc (-σ₁) (-σ₀) := ⟨by linarith, by linarith⟩
  have h := hC (-σ) hmem
  rw [hrw]
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

/-- The reflection kernel on a vertical line decays exponentially in the height. -/
theorem norm_reflectionKernel_vertical_le {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖-((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * I)))‖
      ≤ 4 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
  set z : ℂ := (Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * I) with hz
  have him : z.im = Real.pi * t := GaloisForLFunctions.HTGeometry.im_pi_mul_vertical σ t
  have habs : |z.im| = Real.pi * |t| := by
    rw [him, abs_mul, abs_of_pos Real.pi_pos]
  have hz1 : (1 : ℝ) ≤ |z.im| := by
    rw [habs]
    nlinarith [Real.two_le_pi, ht]
  have hbase := GaloisForLFunctions.HTGeometry.norm_inv_sin_le_exp hz1
  rw [habs] at hbase
  have hrw : -((Real.pi : ℂ) / Complex.sin z) = -((Real.pi : ℂ) * (Complex.sin z)⁻¹) := by
    rw [div_eq_mul_inv]
  rw [hrw, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc Real.pi * ‖(Complex.sin z)⁻¹‖
      ≤ Real.pi * (4 * Real.exp (-(Real.pi * |t|))) :=
        mul_le_mul_of_nonneg_left hbase (le_of_lt Real.pi_pos)
    _ = 4 * Real.pi * Real.exp (-(Real.pi * |t|)) := by ring

/-- **Uniform exponential decay of the Mellin integrand on a vertical strip.**  One constant and one
exponent serve every abscissa in `[σ₀, σ₁]` above the height `1 + 1/s`. -/
theorem exists_bound_norm_barnesIntegrand {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (σ₀ σ₁ : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ σ₁ → 1 + 1 / s ≤ |t| →
      ‖barnesIntegrand s x ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t|)) := by
  classical
  obtain ⟨Cx, hCx0, hCx⟩ := exists_bound_rpow_neg hx σ₀ σ₁
  obtain ⟨Cζ, Nζ, hCζ0, hCζ⟩ :=
    exists_bound_norm_riemannZeta_strip (s * (|σ₀| + |σ₁|))
  refine ⟨Cx * (Cζ * s ^ Nζ) * (4 * Real.pi), Nζ, by positivity, ?_⟩
  intro σ t hσ0 hσ1 ht
  have hs1 : (0 : ℝ) < 1 / s := by positivity
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht1
  -- the three factors
  have hxfac : ‖((x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((σ : ℂ) + (t : ℂ) * I)).re = -σ := by simp
    rw [hre]
    exact hCx σ hσ0 hσ1
  have hshape : -(s : ℂ) * ((σ : ℂ) + (t : ℂ) * I)
      = ((-(s * σ) : ℝ) : ℂ) + ((-(s * t) : ℝ) : ℂ) * I := by push_cast; ring
  have habsst : |(-(s * t))| = s * |t| := by
    rw [abs_neg, abs_mul, abs_of_pos hs]
  have hzfac : ‖riemannZeta (-(s : ℂ) * ((σ : ℂ) + (t : ℂ) * I))‖ ≤ Cζ * s ^ Nζ * |t| ^ Nζ := by
    rw [hshape]
    have habsσ : |(-(s * σ))| ≤ s * (|σ₀| + |σ₁|) := by
      rw [abs_neg, abs_mul, abs_of_pos hs]
      have hσabs : |σ| ≤ |σ₀| + |σ₁| := by
        rcases le_total σ 0 with hneg | hpos
        · rw [abs_of_nonpos hneg]
          have : -σ ≤ -σ₀ := by linarith
          have h0 : -σ₀ ≤ |σ₀| := neg_le_abs σ₀
          linarith [abs_nonneg σ₁]
        · rw [abs_of_nonneg hpos]
          have h1 : σ₁ ≤ |σ₁| := le_abs_self σ₁
          linarith [abs_nonneg σ₀]
      exact mul_le_mul_of_nonneg_left hσabs (le_of_lt hs)
    have hheight : (1 : ℝ) ≤ |(-(s * t))| := by
      rw [habsst]
      have hmul : s * (1 + 1 / s) ≤ s * |t| := mul_le_mul_of_nonneg_left ht (le_of_lt hs)
      have hval : s * (1 + 1 / s) = s + 1 := by field_simp
      rw [hval] at hmul
      linarith
    have h := hCζ (-(s * σ)) (-(s * t)) habsσ hheight
    rw [habsst] at h
    refine h.trans (le_of_eq ?_)
    rw [mul_pow]
    ring
  have hkfac := norm_reflectionKernel_vertical_le (σ := σ) (t := t) ht1
  -- assemble
  rw [barnesIntegrand, norm_mul, norm_mul]
  have hnn1 : (0 : ℝ) ≤ Cζ * s ^ Nζ * |t| ^ Nζ := by positivity
  have hstep1 := mul_le_mul hxfac hzfac (norm_nonneg _) hCx0
  have hstep2 := mul_le_mul hstep1 hkfac (norm_nonneg _) (mul_nonneg hCx0 hnn1)
  refine hstep2.trans (le_of_eq ?_)
  ring

end

end RHTower
