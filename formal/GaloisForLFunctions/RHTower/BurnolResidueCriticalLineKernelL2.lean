import GaloisForLFunctions.RHTower.SmoothAFEZetaLeftLineBound
import GaloisForLFunctions.HTGeometry.ZetaGammaFieldHypertranscendence
import GaloisForLFunctions.HTGeometry.CauchyKernelLineMass
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Burnol's critical-line residue kernel is square-integrable

The strong-convergence step in Burnol's Theorem 5.2 uses, on the line
`Z = -1/2 + it`, the fixed datum

`ζ(Z) / (Z (Z + 2))`

and the parameter-dependent residue kernel

`ζ(Z) (2 + s) / ((Z + 2) (Z - s))`.

The estimate is unconditional.  The exact functional equation and the uniform Dirichlet-series
bound on `Re (1-Z) = 3/2` give *linear* growth of `ζ(Z)`.  One factor `Z` therefore cancels, and
the fixed datum is dominated by an ordinary shifted Cauchy kernel.  If `Re s ≥ -1/4`, then
`‖Z-s‖ ≥ 1/4`; consequently the parameter-dependent multiplier has quadratic growth in `‖s‖`.

This is the literal analytic estimate used in the paper, not an abstract `L²` hypothesis.

## Main results

* `norm_riemannZeta_leftLine_le_linear`
* `memLp_burnolCriticalLineBaseKernel`
* `memLp_burnolResidueCriticalLineKernel`
* `norm_burnolResidueCriticalLineKernel_le_quadratic`
-/

open Complex MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Linear zeta growth on Burnol's shifted critical line.** -/
theorem norm_riemannZeta_leftLine_le_linear (t : ℝ) :
    ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ ≤
      (GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)) *
        ‖smoothAFEZetaLeftLinePt t‖ := by
  let z := smoothAFEZetaLeftLinePt t
  have hz0 : z ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z] at hre
    rw [smoothAFEZetaLeftLinePt_re, Complex.one_re] at hre
    norm_num at hre
  have hGamma : Complex.Gammaℝ (1 - z) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [z]
    rw [one_sub_smoothAFEZetaLeftLinePt_re]
    norm_num
  have hreflect := zeta_eq_zetaChi_mul hz0 hz1 hGamma
  have hzetaRight : ‖riemannZeta (1 - z)‖ ≤
      GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) := by
    apply GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num)
    dsimp only [z]
    rw [one_sub_smoothAFEZetaLeftLinePt_re]
  rw [hreflect, norm_mul,
    show ‖zetaChi z‖ = ‖z‖ / (2 * Real.pi) by
      dsimp only [z]
      exact norm_zetaChi_smoothAFEZetaLeftLinePt t]
  calc
    ‖z‖ / (2 * Real.pi) * ‖riemannZeta (1 - z)‖ ≤
        ‖z‖ / (2 * Real.pi) * GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) := by
          gcongr
    _ = (GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)) * ‖z‖ := by
      ring

/-- Burnol's fixed square-integrable critical-line datum `ζ(Z)/(Z(Z+2))`. -/
def burnolCriticalLineBaseKernel (t : ℝ) : ℂ :=
  riemannZeta (smoothAFEZetaLeftLinePt t) /
    (smoothAFEZetaLeftLinePt t * (smoothAFEZetaLeftLinePt t + 2))

theorem norm_burnolCriticalLineBaseKernel_le (t : ℝ) :
    ‖burnolCriticalLineBaseKernel t‖ ≤
      (GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)) *
        ‖(smoothAFEZetaLeftLinePt t + 2)⁻¹‖ := by
  have hz0 := smoothAFEZetaLeftLinePt_ne_zero t
  rw [burnolCriticalLineBaseKernel, norm_div, norm_mul]
  rw [norm_inv]
  have hlin := norm_riemannZeta_leftLine_le_linear t
  have hnz : ‖smoothAFEZetaLeftLinePt t‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  calc
    ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ /
          (‖smoothAFEZetaLeftLinePt t‖ * ‖smoothAFEZetaLeftLinePt t + 2‖) ≤
        ((GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)) *
          ‖smoothAFEZetaLeftLinePt t‖) /
            (‖smoothAFEZetaLeftLinePt t‖ * ‖smoothAFEZetaLeftLinePt t + 2‖) := by
      gcongr
    _ = (GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)) *
          ‖smoothAFEZetaLeftLinePt t + 2‖⁻¹ := by
      field_simp

theorem integrable_norm_sq_leftLine_add_two_inv :
    Integrable (fun t : ℝ => ‖(smoothAFEZetaLeftLinePt t + 2)⁻¹‖ ^ 2) volume := by
  have h := integrable_norm_sq_cauchyKernel_line (Z := (0 : ℂ))
    (σ := 3 / 2) (by norm_num)
  convert h using 1
  ext t
  rw [show smoothAFEZetaLeftLinePt t + 2 =
      ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I by
        unfold smoothAFEZetaLeftLinePt
        push_cast
        ring]
  rw [show (0 : ℂ) - (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      -(((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) by ring,
    inv_neg, norm_neg]

theorem continuous_burnolCriticalLineBaseKernel : Continuous burnolCriticalLineBaseKernel := by
  rw [continuous_iff_continuousAt]
  intro t
  have hline : Continuous smoothAFEZetaLeftLinePt := by
    unfold smoothAFEZetaLeftLinePt
    fun_prop
  have hz0 : smoothAFEZetaLeftLinePt t ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hz1 : smoothAFEZetaLeftLinePt t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [smoothAFEZetaLeftLinePt_re, Complex.one_re] at hre
    norm_num at hre
  have hz2 : smoothAFEZetaLeftLinePt t + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, smoothAFEZetaLeftLinePt_re] at hre
    norm_num at hre
  apply ContinuousAt.div
    ((analyticOn_riemannZeta _ (by simpa using hz1)).continuousAt.comp hline.continuousAt)
    (hline.continuousAt.mul (hline.continuousAt.add continuousAt_const))
    (mul_ne_zero hz0 hz2)

/-- **Burnol's fixed critical-line datum belongs to `L²`.** -/
theorem memLp_burnolCriticalLineBaseKernel :
    MemLp burnolCriticalLineBaseKernel 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    continuous_burnolCriticalLineBaseKernel.aestronglyMeasurable).2
  let C : ℝ := GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi)
  have hmaj : Integrable
      (fun t : ℝ => (C * ‖(smoothAFEZetaLeftLinePt t + 2)⁻¹‖) ^ 2) volume := by
    have h := integrable_norm_sq_leftLine_add_two_inv.const_mul (C ^ 2)
    convert h using 1
    ext t
    ring
  refine hmaj.mono'
    ((continuous_burnolCriticalLineBaseKernel.norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards with t
  have h := norm_burnolCriticalLineBaseKernel_le t
  rw [Real.norm_of_nonneg (sq_nonneg ‖burnolCriticalLineBaseKernel t‖)]
  change ‖burnolCriticalLineBaseKernel t‖ ≤
    C * ‖(smoothAFEZetaLeftLinePt t + 2)⁻¹‖ at h
  nlinarith [norm_nonneg (burnolCriticalLineBaseKernel t)]

/-- Burnol's parameter-dependent critical-line kernel. -/
def burnolResidueCriticalLineKernel (s : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (smoothAFEZetaLeftLinePt t) * (2 + s) /
    ((smoothAFEZetaLeftLinePt t + 2) * (smoothAFEZetaLeftLinePt t - s))

/-- Rational multiplier carrying the fixed base datum to the residue kernel. -/
def burnolResidueCriticalLineMultiplier (s : ℂ) (t : ℝ) : ℂ :=
  smoothAFEZetaLeftLinePt t * (2 + s) / (smoothAFEZetaLeftLinePt t - s)

theorem quarter_le_norm_leftLine_sub {s : ℂ} (hs : -(1 / 4 : ℝ) ≤ s.re) (t : ℝ) :
    (1 / 4 : ℝ) ≤ ‖smoothAFEZetaLeftLinePt t - s‖ := by
  have hre : (smoothAFEZetaLeftLinePt t - s).re = -1 / 2 - s.re := by
    rw [Complex.sub_re, smoothAFEZetaLeftLinePt_re]
  calc
    (1 / 4 : ℝ) ≤ |(smoothAFEZetaLeftLinePt t - s).re| := by
      rw [hre, abs_of_nonpos (by linarith)]
      linarith
    _ ≤ ‖smoothAFEZetaLeftLinePt t - s‖ := Complex.abs_re_le_norm _

theorem norm_leftLine_div_sub_le {s : ℂ} (hs : -(1 / 4 : ℝ) ≤ s.re) (t : ℝ) :
    ‖smoothAFEZetaLeftLinePt t‖ / ‖smoothAFEZetaLeftLinePt t - s‖ ≤
      1 + 4 * ‖s‖ := by
  let z := smoothAFEZetaLeftLinePt t
  have hsep : (1 / 4 : ℝ) ≤ ‖z - s‖ := quarter_le_norm_leftLine_sub hs t
  have hpos : 0 < ‖z - s‖ := lt_of_lt_of_le (by norm_num) hsep
  have htri : ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by
    calc
      ‖z‖ = ‖(z - s) + s‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
  have hsdiv : ‖s‖ / ‖z - s‖ ≤ 4 * ‖s‖ := by
    have hinv : ‖z - s‖⁻¹ ≤ 4 := by
      have h := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 4)).2 hsep
      norm_num at h ⊢
      exact h
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hinv (norm_nonneg s)]
  calc
    ‖z‖ / ‖z - s‖ ≤ (‖z - s‖ + ‖s‖) / ‖z - s‖ := by gcongr
    _ = 1 + ‖s‖ / ‖z - s‖ := by field_simp
    _ ≤ 1 + 4 * ‖s‖ := by linarith

theorem burnolResidueCriticalLineKernel_eq (s : ℂ) (t : ℝ) :
    burnolResidueCriticalLineKernel s t = burnolCriticalLineBaseKernel t *
      burnolResidueCriticalLineMultiplier s t := by
  have hz0 : smoothAFEZetaLeftLinePt t ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hz2 : smoothAFEZetaLeftLinePt t + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, smoothAFEZetaLeftLinePt_re] at hre
    norm_num at hre
  rw [burnolResidueCriticalLineKernel, burnolCriticalLineBaseKernel,
    burnolResidueCriticalLineMultiplier]
  field_simp

theorem norm_burnolResidueCriticalLineKernel_le {s : ℂ}
    (hs : -(1 / 4 : ℝ) ≤ s.re) (t : ℝ) :
    ‖burnolResidueCriticalLineKernel s t‖ ≤
      (‖2 + s‖ * (1 + 4 * ‖s‖)) * ‖burnolCriticalLineBaseKernel t‖ := by
  rw [burnolResidueCriticalLineKernel_eq, norm_mul,
    burnolResidueCriticalLineMultiplier, norm_div, norm_mul]
  have hratio := norm_leftLine_div_sub_le hs t
  calc
    ‖burnolCriticalLineBaseKernel t‖ *
        (‖smoothAFEZetaLeftLinePt t‖ * ‖2 + s‖ /
          ‖smoothAFEZetaLeftLinePt t - s‖) =
        ‖burnolCriticalLineBaseKernel t‖ * ‖2 + s‖ *
          (‖smoothAFEZetaLeftLinePt t‖ /
            ‖smoothAFEZetaLeftLinePt t - s‖) := by ring
    _ ≤ ‖burnolCriticalLineBaseKernel t‖ * ‖2 + s‖ * (1 + 4 * ‖s‖) := by
      gcongr
    _ = (‖2 + s‖ * (1 + 4 * ‖s‖)) * ‖burnolCriticalLineBaseKernel t‖ := by ring

/-- The literal multiplier has the polynomial envelope used in Burnol's contour estimate. -/
theorem norm_burnolResidueCriticalLineKernel_le_quadratic {s : ℂ}
    (hs : -(1 / 4 : ℝ) ≤ s.re) (t : ℝ) :
    ‖burnolResidueCriticalLineKernel s t‖ ≤
      (9 * (1 + ‖s‖ ^ 2)) * ‖burnolCriticalLineBaseKernel t‖ := by
  have hraw := norm_burnolResidueCriticalLineKernel_le hs t
  have hadd : ‖2 + s‖ ≤ 2 + ‖s‖ := by
    calc
      ‖2 + s‖ ≤ ‖(2 : ℂ)‖ + ‖s‖ := norm_add_le _ _
      _ = 2 + ‖s‖ := by norm_num
  have hpoly : ‖2 + s‖ * (1 + 4 * ‖s‖) ≤ 9 * (1 + ‖s‖ ^ 2) := by
    have hr := norm_nonneg s
    have hfac : 0 ≤ 1 + 4 * ‖s‖ := by positivity
    calc
      ‖2 + s‖ * (1 + 4 * ‖s‖) ≤ (2 + ‖s‖) * (1 + 4 * ‖s‖) := by
        gcongr
      _ ≤ 9 * (1 + ‖s‖ ^ 2) := by
        nlinarith [sq_nonneg (‖s‖ - 1)]
  exact hraw.trans <| mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)

theorem norm_burnolResidueCriticalLineMultiplier_le_quadratic {s : ℂ}
    (hs : -(1 / 4 : ℝ) ≤ s.re) (t : ℝ) :
    ‖burnolResidueCriticalLineMultiplier s t‖ ≤ 9 * (1 + ‖s‖ ^ 2) := by
  rw [burnolResidueCriticalLineMultiplier, norm_div, norm_mul]
  have hratio := norm_leftLine_div_sub_le hs t
  have hadd : ‖2 + s‖ ≤ 2 + ‖s‖ := by
    calc
      ‖2 + s‖ ≤ ‖(2 : ℂ)‖ + ‖s‖ := norm_add_le _ _
      _ = 2 + ‖s‖ := by norm_num
  calc
    ‖smoothAFEZetaLeftLinePt t‖ * ‖2 + s‖ /
        ‖smoothAFEZetaLeftLinePt t - s‖ =
        ‖2 + s‖ *
          (‖smoothAFEZetaLeftLinePt t‖ /
            ‖smoothAFEZetaLeftLinePt t - s‖) := by ring
    _ ≤ ‖2 + s‖ * (1 + 4 * ‖s‖) := by gcongr
    _ ≤ (2 + ‖s‖) * (1 + 4 * ‖s‖) := by gcongr
    _ ≤ 9 * (1 + ‖s‖ ^ 2) := by
      nlinarith [norm_nonneg s, sq_nonneg (‖s‖ - 1)]

/-- Explicit `L²` seminorm bound needed for Burnol's contour integration in the source variable. -/
theorem eLpNorm_burnolResidueCriticalLineKernel_le_quadratic {s : ℂ}
    (hs : -(1 / 4 : ℝ) ≤ s.re) :
    eLpNorm (burnolResidueCriticalLineKernel s) 2 volume ≤
      ‖(9 * (1 + ‖s‖ ^ 2) : ℝ)‖ₑ *
        eLpNorm burnolCriticalLineBaseKernel 2 volume := by
  have h := MeasureTheory.eLpNorm_mul_le_of_bound
    (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))
    (by positivity : (0 : ℝ) ≤ 9 * (1 + ‖s‖ ^ 2))
    (norm_burnolResidueCriticalLineMultiplier_le_quadratic hs)
    burnolCriticalLineBaseKernel
  have heq : (fun t : ℝ => burnolResidueCriticalLineMultiplier s t *
      burnolCriticalLineBaseKernel t) = burnolResidueCriticalLineKernel s := by
    funext t
    rw [burnolResidueCriticalLineKernel_eq]
    ring
  rwa [heq] at h

theorem continuous_burnolResidueCriticalLineKernel (s : ℂ)
    (hs : -(1 / 4 : ℝ) ≤ s.re) :
    Continuous (burnolResidueCriticalLineKernel s) := by
  have hbase := continuous_burnolCriticalLineBaseKernel
  have hline : Continuous smoothAFEZetaLeftLinePt := by
    unfold smoothAFEZetaLeftLinePt
    fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  have heq : (fun u : ℝ => burnolResidueCriticalLineKernel s u) = fun u =>
      burnolCriticalLineBaseKernel u *
        burnolResidueCriticalLineMultiplier s u :=
    funext (burnolResidueCriticalLineKernel_eq s)
  change ContinuousAt (fun u : ℝ => burnolResidueCriticalLineKernel s u) t
  rw [heq]
  apply ContinuousAt.mul hbase.continuousAt
  unfold burnolResidueCriticalLineMultiplier
  apply ContinuousAt.div
    (hline.continuousAt.mul continuousAt_const)
    (hline.continuousAt.sub continuousAt_const)
  exact norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num) (quarter_le_norm_leftLine_sub hs t))

/-- **Burnol's residue kernel belongs to `L²` uniformly at each source-strip point.** -/
theorem memLp_burnolResidueCriticalLineKernel (s : ℂ)
    (hs : -(1 / 4 : ℝ) ≤ s.re) :
    MemLp (burnolResidueCriticalLineKernel s) 2 volume := by
  exact MemLp.of_le_mul
    (c := ‖2 + s‖ * (1 + 4 * ‖s‖))
    memLp_burnolCriticalLineBaseKernel
    (continuous_burnolResidueCriticalLineKernel s hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_burnolResidueCriticalLineKernel_le hs))

end

end RHTower
