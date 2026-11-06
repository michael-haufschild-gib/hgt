import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheComplexSaddleOfAGaussianAverage
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightXiModel

/-!
# The slope of `ξ` at a typical height of power level

At a typical height of level `T^E` (no zero right of `½ + η/4` within height `2`, and `|ζ| ≤ T^E`), the logarithmic
derivative of `ξ` is within `B ≍ E log T / η²` of the horizontal slope, on a complex neighbourhood of the horizontal
segment. So it is analytic there with Lipschitz constant `4B/η`, and this supplies the data of the complex saddle:

* `norm_logDeriv_xi_sub_slope_le`: the slope bound;
* `lineLogDeriv_lipschitz`: the Cauchy estimate;
* `exists_saddle_fixedPoint`: the fixed point `u = y + 2τ (ξ′/ξ)(½ + u + iX)`, by contraction;
* `norm_window_model_le`: the quadratic model of `ξ` on the line through the saddle;
* `norm_archG_le_of_segment`, `norm_xi_le_anchor`: the size of `ξ` across the strip, relative to an anchor right of
  `½ + 2η`, with the loss `powerRatio ≍ T^{E(1 + 12/η)}`.
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology
open scoped Interval
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The slope error at level `T^E`. -/
def powerSlopeError (E η T : ℝ) : ℝ := 24 * (E * Real.log T + 9) / η ^ 2 + 5

theorem powerSlopeError_pos {E η T : ℝ} (hE : 0 ≤ E) (hT : 1 ≤ T) : 0 < powerSlopeError E η T := by
  have hlog := Real.log_nonneg hT
  unfold powerSlopeError
  positivity

/-- **A height of depth `d`.** No zero lies right of `½ + d + η/4` within height `2`, and `|ζ| ≤ T^E + 2` on
`Re s ≥ ½`, `|Im s − t| ≤ 2`. The level bound excludes crowds. -/
structure DepthTypical (d η E T t : ℝ) : Prop where
  hd : 0 ≤ d
  hd2 : d ≤ 1 / 2
  mem : t ∈ Icc T (2 * T)
  ne_zero : ∀ {s : ℂ}, 1 / 2 + d + η / 4 ≤ s.re → |s.im - t| ≤ 2 → riemannZeta s ≠ 0
  norm_le : ∀ {s : ℂ}, 1 / 2 ≤ s.re → |s.im - t| ≤ 2 → ‖riemannZeta s‖ ≤ T ^ E + 2

/-- A typical height is a height of depth `0`. -/
theorem _root_.RHTower.zetaTypicalHeight.depthTypical {η E T t : ℝ}
    (h : RHTower.zetaTypicalHeight η E T t) (hT : 1 ≤ T) : DepthTypical 0 η E T t where
  hd := le_rfl
  hd2 := by norm_num
  mem := h.1
  ne_zero := fun hs hst => h.ne_zero (by linarith only [hs]) hst
  norm_le := fun hs hst => h.norm_le hT hs hst

namespace DepthTypical

variable {d η E T t : ℝ}

/-- The disc of radius `3/2 − d − η/4` about `2 + it` satisfies the hypotheses of Borel–Carathéodory. -/
theorem disc_hypotheses (h : DepthTypical d η E T t) (hη0 : 0 < η) (hT : 8 ≤ T) :
    DifferentiableOn ℂ riemannZeta (ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4))
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4), riemannZeta s ≠ 0)
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4), ‖riemannZeta s‖ ≤ T ^ E + 2)
      ∧ 1 / 3 ≤ ‖riemannZeta (2 + (t : ℂ) * I)‖ := by
  have hd := h.hd
  have hgeom : ∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4),
      1 / 2 + d + η / 4 < s.re ∧ |s.im - t| ≤ 2 := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h1 := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hs)
    have h2 := abs_le.mp ((Complex.abs_im_le_norm _).trans hs.le)
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
      Complex.mul_im] at h1 h2
    norm_num at h1 h2
    exact ⟨by linarith only [h1.1], abs_le.mpr ⟨by linarith only [h2.1, hd, hη0],
      by linarith only [h2.2, hd, hη0]⟩⟩
  refine ⟨?_, fun s hs => ?_, fun s hs => ?_, ?_⟩
  · intro s hs
    have hg := hgeom s hs
    have hne : s ≠ 1 := by
      intro h1
      rw [h1] at hg
      simp at hg
      have := abs_le.mp hg.2
      linarith only [this.2, h.mem.1, hT]
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  · have hg := hgeom s hs
    exact h.ne_zero hg.1.le hg.2
  · have hg := hgeom s hs
    exact h.norm_le (by linarith only [hg.1, hd, hη0]) hg.2
  · exact (norm_riemannZeta_bounds_of_two_le_re (by simp)).1

/-- The logarithmic derivative at depth `d`. -/
theorem norm_logDeriv_le (h : DepthTypical d η E T t) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) (hE : 0 ≤ E) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - d - η) :
    ‖logDeriv riemannZeta s‖ ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by
  have hd := h.hd
  have hd2 := h.hd2
  obtain ⟨hdiff, hne, hM, hm⟩ := h.disc_hypotheses hη0 hT
  have hb := GaloisForLFunctions.HTGeometry.norm_logDeriv_le (ρ := 3 / 2 - d - η)
    (r := 3 / 2 - d - η / 2) (by linarith only [hd2, hη1]) (by linarith only [hη0])
    (by linarith only [hη0]) hdiff hne hM (by norm_num) hm hs
  rw [logDeriv_apply]
  refine hb.trans ?_
  have hL := zetaTypicalHeight.log_ratio_le (T := T) (ε := E) (by linarith only [hT]) hE
  have hL0 : 0 ≤ Real.log ((T ^ E + 2) / (1 / 3)) + 1 := by
    have : 1 ≤ (T ^ E + 2) / (1 / 3) := by
      rw [le_div_iff₀ (by norm_num)]
      have := Real.rpow_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T) E
      linarith only [this]
    linarith only [Real.log_nonneg this]
  have e : 3 / 2 - d - η / 4 - (3 / 2 - d - η / 2) = η / 4 := by ring
  have e2 : 3 / 2 - d - η / 2 - (3 / 2 - d - η) = η / 2 := by ring
  rw [e, e2]
  have hr0 : 0 ≤ 3 / 2 - d - η / 2 := by linarith only [hd2, hη1]
  have hfac : (3 / 2 - d - η / 2) / (η / 4) / (η / 2) ≤ 12 / η ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hd, hη0, sq_nonneg η, mul_pos hη0 hη0,
      mul_nonneg hd (sq_nonneg η), pow_pos hη0 3, mul_nonneg hη0.le (sq_nonneg η)]
  calc 2 * (Real.log ((T ^ E + 2) / (1 / 3)) + 1) * (3 / 2 - d - η / 2) / (η / 4) / (η / 2)
      = 2 * (Real.log ((T ^ E + 2) / (1 / 3)) + 1) *
          ((3 / 2 - d - η / 2) / (η / 4) / (η / 2)) := by ring
    _ ≤ 2 * (E * Real.log T + 9) * (12 / η ^ 2) := by
        have h0 : 0 ≤ (3 / 2 - d - η / 2) / (η / 4) / (η / 2) :=
          div_nonneg (div_nonneg hr0 (by positivity)) (by positivity)
        exact mul_le_mul (by linarith only [hL]) hfac h0 (by linarith only [hL, hL0])
    _ = 24 * (E * Real.log T + 9) / η ^ 2 := by ring

/-- The lower bound for `ζ` at depth `d`. -/
theorem norm_ge (h : DepthTypical d η E T t) (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hE : 0 ≤ E) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - d - η / 2) :
    Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3 ≤ ‖riemannZeta s‖ := by
  have hd := h.hd
  have hd2 := h.hd2
  obtain ⟨hdiff, hne, hM, hm⟩ := h.disc_hypotheses hη0 hT
  have hb := GaloisForLFunctions.HTGeometry.norm_lower_bound_of_ball (r := 3 / 2 - d - η / 2)
    (by linarith only [hd2, hη1]) (by linarith only [hη0]) hdiff hne hM (by norm_num) hm hs
  refine le_trans ?_ hb
  have hL := zetaTypicalHeight.log_ratio_le (T := T) (ε := E) (by linarith only [hT]) hE
  have e : 3 / 2 - d - η / 4 - (3 / 2 - d - η / 2) = η / 4 := by ring
  rw [e]
  have hL0 : 0 ≤ Real.log ((T ^ E + 2) / (1 / 3)) + 1 := by
    have : 1 ≤ (T ^ E + 2) / (1 / 3) := by
      rw [le_div_iff₀ (by norm_num)]
      have := Real.rpow_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T) E
      linarith only [this]
    linarith only [Real.log_nonneg this]
  have hkey : 2 * (Real.log ((T ^ E + 2) / (1 / 3)) + 1) * (3 / 2 - d - η / 2) / (η / 4)
      ≤ 12 * (E * Real.log T + 9) / η := by
    calc 2 * (Real.log ((T ^ E + 2) / (1 / 3)) + 1) * (3 / 2 - d - η / 2) / (η / 4)
        = (Real.log ((T ^ E + 2) / (1 / 3)) + 1) * (8 * (3 / 2 - d - η / 2) / η) := by
          field_simp
          ring
      _ ≤ (E * Real.log T + 9) * (12 / η) := by
          refine mul_le_mul (by linarith only [hL]) ?_ ?_ (by linarith only [hL, hL0])
          · rw [div_le_div_iff₀ hη0 hη0]
            nlinarith only [hd, hη0, mul_pos hη0 hη0, mul_nonneg hd hη0.le]
          · exact div_nonneg (by linarith only [hd2, hη1]) hη0.le
      _ = 12 * (E * Real.log T + 9) / η := by ring
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hkey)
  linarith only [hexp]

end DepthTypical

/-- `ξ′/ξ` in the coordinate `s = ½ + w + iX`. -/
def lineLogDeriv (X : ℝ) (w : ℂ) : ℂ := logDeriv xi (1 / 2 + w + I * X)

theorem line_point (X : ℝ) (w : ℂ) :
    (1 / 2 + w + I * X : ℂ) = ((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.one_re]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_im, Complex.one_im]
    ring

theorem norm_horizontalSlope_sub_le {X Y : ℝ} (hX : 2 ≤ X) (hYX : |Y - X| ≤ 1) :
    ‖horizontalSlope Y - horizontalSlope X‖ ≤ 1 := by
  have hX0 : 0 < X := by linarith only [hX]
  have hY : 1 ≤ Y := by linarith only [hX, (abs_le.mp hYX).1]
  have hY0 : 0 < Y := by linarith only [hY]
  have hslope : horizontalSlope Y - horizontalSlope X = ((Real.log (Y / X) / 2 : ℝ) : ℂ) := by
    simp only [horizontalSlope]
    rw [Real.log_div hY0.ne' (by positivity), Real.log_div hX0.ne' (by positivity),
      Real.log_div hY0.ne' hX0.ne']
    push_cast
    ring
  rw [hslope, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two, div_le_one (by norm_num)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < Y / X by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < X / Y by positivity)
  have h3 : Real.log (X / Y) = -Real.log (Y / X) := by
    rw [Real.log_div hX0.ne' hY0.ne', Real.log_div hY0.ne' hX0.ne']
    ring
  have hup : Y / X - 1 ≤ 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hX0]
    linarith only [(abs_le.mp hYX).2, hX]
  have hlow : X / Y - 1 ≤ 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hY0]
    linarith only [(abs_le.mp hYX).1, hY]
  rw [abs_le]
  constructor <;> linarith only [h1, h2, h3, hup, hlow]

private theorem disc_bound {d η σ Y t : ℝ} (hσ : 1 / 2 + d + 2 * η ≤ σ) (hσ2 : σ ≤ 2) (hYt : |Y - t| ≤ η) :
    ‖(σ : ℂ) + Y * I - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - d - η := by
  have he : (σ : ℂ) + Y * I - (2 + (t : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) + ((Y - t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hσ2)]
  linarith only [hσ, hYt]

/-- **The slope of `ξ` at level `T^E`.** -/
theorem norm_logDeriv_xi_sub_slope_le {d η E T t X σ Y : ℝ}
    (h : DepthTypical d η E T t) (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hX : 1000 ≤ X) (hYX : |Y - X| ≤ 1) (hYt : |Y - t| ≤ η) (hσ : 1 / 2 + d + 2 * η ≤ σ)
    (hσX : σ ≤ X / 64) :
    ‖logDeriv xi ((σ : ℂ) + Y * I) - horizontalSlope X‖ ≤ powerSlopeError E η T := by
  have hY := abs_le.mp hYX
  have hY999 : 999 ≤ Y := by linarith only [hX, hY.1]
  have hσ0 : 0 < σ := by linarith only [hη, hσ, h.hd]
  have him : ((σ : ℂ) + Y * I).im ≠ 0 := by
    simpa using (show Y ≠ 0 by linarith only [hY999])
  have hne1 : (σ : ℂ) + Y * I ≠ 1 := fun he => him (by rw [he]; simp)
  have hζ : riemannZeta ((σ : ℂ) + Y * I) ≠ 0 :=
    h.ne_zero (by simp; linarith only [hη, hσ])
      (by simpa using hYt.trans (by linarith only [hη1]))
  have he : logDeriv xi ((σ : ℂ) + Y * I) =
      logDeriv archG ((σ : ℂ) + Y * I) + logDeriv riemannZeta ((σ : ℂ) + Y * I) := by
    rw [logDeriv_xi_fourFactor_offReal him hζ, logDeriv_archG (by simpa using hσ0) hne1]
  have harch := norm_logDeriv_archG_sub_horizontalSlope_le_one hσ0
    (by linarith only [hσX, hX, hY.1]) (by linarith only [hY999] : 200 ≤ Y)
  have hslope := norm_horizontalSlope_sub_le (by linarith only [hX] : 2 ≤ X) hYX
  have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
  have hB : 0 ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by positivity
  have hz : ‖logDeriv riemannZeta ((σ : ℂ) + Y * I)‖ ≤ 24 * (E * Real.log T + 9) / η ^ 2 + 3 := by
    rcases le_or_gt σ 2 with hσ2 | hσ2
    · have hb := h.norm_logDeriv_le hη hη1 hT hE (disc_bound hσ hσ2 hYt)
      linarith only [hb]
    · have hb := norm_logDeriv_riemannZeta_le_inv_sub_one_add_two
        (show 1 < σ by linarith only [hσ2]) Y
      have hi : 1 / (σ - 1) ≤ 1 := (div_le_one (by linarith only [hσ2])).mpr
        (by linarith only [hσ2])
      linarith only [hb, hi, hB]
  have hsum : logDeriv xi ((σ : ℂ) + Y * I) - horizontalSlope X =
      (logDeriv archG ((σ : ℂ) + Y * I) - horizontalSlope Y) +
        logDeriv riemannZeta ((σ : ℂ) + Y * I) + (horizontalSlope Y - horizontalSlope X) := by
    rw [he]
    ring
  rw [hsum]
  unfold powerSlopeError
  have h1 := norm_add₃_le (a := logDeriv archG ((σ : ℂ) + Y * I) - horizontalSlope Y)
    (b := logDeriv riemannZeta ((σ : ℂ) + Y * I)) (c := horizontalSlope Y - horizontalSlope X)
  linarith only [h1, harch, hz, hslope]

/-- The box of `w` on which the slope bound holds. -/
def saddleRegion (d η t X : ℝ) : Set ℂ :=
  {w | d + 2 * η ≤ w.re ∧ w.re ≤ 15 ∧ |X + w.im - t| ≤ η}

/-- The convex box on which the Lipschitz bound holds. -/
def innerBox (d η : ℝ) : Set ℂ :=
  {w | d + 3 * η ≤ w.re ∧ w.re ≤ 14 ∧ |w.im| ≤ η / 4}

theorem convex_innerBox (d η : ℝ) : Convex ℝ (innerBox d η) := by
  have hset : innerBox d η = {w : ℂ | d + 3 * η ≤ w.re} ∩ ({w : ℂ | w.re ≤ 14} ∩
      ({w : ℂ | -(η / 4) ≤ w.im} ∩ {w : ℂ | w.im ≤ η / 4})) := by
    ext w
    simp only [innerBox, Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
  rw [hset]
  exact (convex_halfSpace_re_ge _).inter ((convex_halfSpace_re_le _).inter
    ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)))

theorem xi_ne_zero_of_mem_saddleRegion {d η E T t X : ℝ} {w : ℂ}
    (h : DepthTypical d η E T t) (hη : 0 < η) (hη1 : η ≤ 1) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η) (hw : w ∈ saddleRegion d η t X) : xi (1 / 2 + w + I * X) ≠ 0 := by
  obtain ⟨h1, _, h3⟩ := hw
  rw [line_point]
  have him_abs : |w.im| ≤ 2 * η := by
    have he : w.im = (X + w.im - t) - (X - t) := by ring
    rw [he]
    refine (abs_sub _ _).trans ?_
    linarith only [h3, hXt]
  have hY : 998 ≤ X + w.im := by
    have := (abs_le.mp him_abs).1
    linarith only [this, hX, hη1]
  have him : (((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I).im ≠ 0 := by
    simpa using (show X + w.im ≠ 0 by linarith only [hY])
  have hne1 : ((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I ≠ 1 :=
    fun he => him (by rw [he]; simp)
  rw [xi_eq_archG_mul_zeta_offReal him]
  refine mul_ne_zero (archG_ne_zero ?_ hne1) (h.ne_zero ?_ ?_)
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
    linarith only [hη, h1, h.hd]
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
    linarith only [hη, h1]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact h3.trans (by linarith only [hη1])

theorem norm_lineLogDeriv_sub_le {d η E T t X : ℝ} {w : ℂ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X) (hXt : |X - t| ≤ η)
    (hw : w ∈ saddleRegion d η t X) :
    ‖lineLogDeriv X w - horizontalSlope X‖ ≤ powerSlopeError E η T := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold lineLogDeriv
  rw [line_point]
  have him_abs : |w.im| ≤ 2 * η := by
    have he : w.im = (X + w.im - t) - (X - t) := by ring
    rw [he]
    refine (abs_sub _ _).trans ?_
    linarith only [h3, hXt]
  refine norm_logDeriv_xi_sub_slope_le h hη (by linarith only [hη1]) hT hE hX ?_ ?_ ?_ ?_
  · rw [add_sub_cancel_left]
    linarith only [him_abs, hη1]
  · exact h3
  · linarith only [h1]
  · linarith only [h2, hX]

theorem differentiable_deriv_xi : Differentiable ℂ (deriv xi) := fun z =>
  ((xi_differentiable.differentiableOn (s := univ)).deriv isOpen_univ z (mem_univ z)).differentiableAt
    univ_mem

theorem differentiableAt_lineLogDeriv {X : ℝ} {w : ℂ} (hne : xi (1 / 2 + w + I * X) ≠ 0) :
    DifferentiableAt ℂ (lineLogDeriv X) w := by
  have he : lineLogDeriv X = fun w => deriv xi (1 / 2 + w + I * X) / xi (1 / 2 + w + I * X) := by
    funext z
    exact logDeriv_apply _ _
  rw [he]
  have hin : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 + z + I * X : ℂ)) w := by fun_prop
  exact ((differentiable_deriv_xi _).comp w hin).div ((xi_differentiable _).comp w hin) hne

/-- The Cauchy estimate on the inner box. -/
theorem norm_deriv_lineLogDeriv_le {d η E T t X : ℝ} {w : ℂ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hw : w ∈ innerBox d η) :
    ‖deriv (lineLogDeriv X) w‖ ≤ 4 * powerSlopeError E η T / η := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hsub : ∀ z ∈ closedBall w (η / 4), z ∈ saddleRegion d η t X := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hz)
    have him := (Complex.abs_im_le_norm _).trans hz
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    have h3' := abs_le.mp h3
    have him' := abs_le.mp him
    have hXt'' := abs_le.mp hXt
    refine ⟨by linarith only [hre.1, h1, hη], by linarith only [hre.2, h2, hη8], abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith only [him'.1, h3'.1, hXt''.1]
    · linarith only [him'.2, h3'.2, hXt''.2]
  have hd : DifferentiableOn ℂ (fun z => lineLogDeriv X z - horizontalSlope X)
      (closedBall w (η / 4)) := fun z hz =>
    ((differentiableAt_lineLogDeriv (xi_ne_zero_of_mem_saddleRegion h hη (by linarith only [hη8]) hX
      hXt' (hsub z hz))).sub_const _).differentiableWithinAt
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < η / 4)
    (hd.diffContOnCl_ball subset_rfl) (C := powerSlopeError E η T) (fun z hz =>
      norm_lineLogDeriv_sub_le h hη (by linarith only [hη8]) hT hE hX hXt'
        (hsub z (sphere_subset_closedBall hz)))
  rw [deriv_sub_const] at hC
  refine hC.trans (le_of_eq ?_)
  field_simp

/-- `ξ′/ξ` is Lipschitz on the inner box. -/
theorem lineLogDeriv_lipschitz {d η E T t X : ℝ} {w₁ w₂ : ℂ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (h₁ : w₁ ∈ innerBox d η) (h₂ : w₂ ∈ innerBox d η) :
    ‖lineLogDeriv X w₂ - lineLogDeriv X w₁‖ ≤ 4 * powerSlopeError E η T / η * ‖w₂ - w₁‖ := by
  have hsub : ∀ z ∈ innerBox d η, z ∈ saddleRegion d η t X := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    have h3' := abs_le.mp h3
    have hXt'' := abs_le.mp hXt
    refine ⟨by linarith only [h1, hη], by linarith only [h2], abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith only [h3'.1, hXt''.1, hη]
    · linarith only [h3'.2, hXt''.2, hη]
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  exact (convex_innerBox d η).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => differentiableAt_lineLogDeriv
      (xi_ne_zero_of_mem_saddleRegion h hη (by linarith only [hη8]) hX hXt' (hsub z hz)))
    (fun z hz => norm_deriv_lineLogDeriv_le h hη hη8 hT hE hX hXt hz) h₁ h₂

/-- **The complex saddle exists.** The map `w ↦ y + 2τ (ξ′/ξ)(½ + w + iX)` contracts a small ball about the
Euler-free saddle `y + 2τ a(X)`. -/
theorem exists_saddle_fixedPoint {d η E T t X τ y : ℝ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hτ : 0 < τ)
    (hsub : closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * powerSlopeError E η T) ⊆
      innerBox d η)
    (hlip : 2 * τ * (4 * powerSlopeError E η T / η) ≤ 1 / 2) :
    ∃ u ∈ closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * powerSlopeError E η T),
      u = (y : ℂ) + 2 * (τ : ℂ) * lineLogDeriv X u := by
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hTB := powerSlopeError_pos (η := η) hE (by linarith only [hT] : 1 ≤ T)
  set c₀ := (y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X with hc₀
  set R := 2 * τ * powerSlopeError E η T with hR
  have hR0 : 0 ≤ R := by positivity
  let G : ℂ → ℂ := fun w => (y : ℂ) + 2 * (τ : ℂ) * lineLogDeriv X w
  have hnorm2 : ‖(2 : ℂ) * (τ : ℂ)‖ = 2 * τ := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hmaps : MapsTo G (closedBall c₀ R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have he : G w - c₀ = 2 * (τ : ℂ) * (lineLogDeriv X w - horizontalSlope X) := by
      simp only [G, hc₀]
      ring
    have hbox := hsub hw
    obtain ⟨h1, h2, h3⟩ := hbox
    have h3' := abs_le.mp h3
    have hXt'' := abs_le.mp hXt
    have hreg : w ∈ saddleRegion d η t X := by
      refine ⟨by linarith only [h1, hη], by linarith only [h2], abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith only [h3'.1, hXt''.1, hη]
      · linarith only [h3'.2, hXt''.2, hη]
    rw [he, norm_mul, hnorm2]
    exact mul_le_mul_of_nonneg_left
      (norm_lineLogDeriv_sub_le h hη (by linarith only [hη8]) hT hE hX hXt' hreg) (by positivity)
  let K : NNReal := 1 / 2
  have hK : (K : ℝ) = 1 / 2 := by simp [K]
  have hcontr : ContractingWith K (hmaps.restrict G (closedBall c₀ R) (closedBall c₀ R)) := by
    refine ⟨by rw [← NNReal.coe_lt_coe, hK]; norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, hK]
    rw [dist_eq_norm, dist_eq_norm]
    have he : G a - G b = 2 * (τ : ℂ) * (lineLogDeriv X a - lineLogDeriv X b) := by
      simp only [G]
      ring
    rw [he, norm_mul, hnorm2]
    have hL := lineLogDeriv_lipschitz h hη hη8 hT hE hX hXt (hsub hb) (hsub ha)
    calc
      _ ≤ 2 * τ * (4 * powerSlopeError E η T / η * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 * τ * (4 * powerSlopeError E η T / η) * ‖a - b‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  haveI : CompleteSpace (closedBall c₀ R) := isClosed_closedBall.completeSpace_coe
  obtain ⟨p, hp, _⟩ := hcontr.exists_fixedPoint ⟨c₀, mem_closedBall_self hR0⟩ (edist_ne_top _ _)
  refine ⟨p.1, p.2, ?_⟩
  have := congrArg Subtype.val hp
  simpa only [MapsTo.val_restrict_apply] using this.symm

/-- **The second-order model on the line through the saddle.** -/
theorem norm_window_model_le {d η E T t X a δ v : ℝ} {ℓ : ℂ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hℓ : ℓ = lineLogDeriv X ((a : ℂ) + (δ : ℂ) * I))
    (hbox : ∀ x ∈ [[a, a + v]], (x : ℂ) + (δ : ℂ) * I ∈ innerBox d η) :
    ‖xi (1 / 2 + ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) + I * X) -
        xi (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X) * Complex.exp ((v : ℂ) * ℓ)‖ ≤
      ‖xi (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X)‖ * Real.exp (v * ℓ.re) *
        (Real.exp (4 * powerSlopeError E η T / η * v ^ 2) - 1) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hTB := powerSlopeError_pos (η := η) hE (by linarith only [hT] : 1 ≤ T)
  have hpt (x : ℝ) : (1 / 2 + ((x : ℂ) + (δ : ℂ) * I) + I * X : ℂ) =
      1 / 2 + (x : ℂ) + I * ((X + δ : ℝ) : ℂ) := by
    push_cast
    ring
  have hmodel := HTGeometry.norm_sub_mul_exp_le (F := xiLine (X + δ)) (F' := xiLineDeriv (X + δ))
    (a := ℓ) (η := 4 * powerSlopeError E η T / η * |v|) (u := a) (w := a + v)
    (by have := abs_pos.mpr hv; positivity) (fun x _ => hasDerivAt_xiLine (X + δ) x)
    (fun x hx => by
      have hin := hbox x hx
      have hin0 : (a : ℂ) + (δ : ℂ) * I ∈ innerBox d η := hbox a left_mem_uIcc
      have hreg : (x : ℂ) + (δ : ℂ) * I ∈ saddleRegion d η t X := by
        obtain ⟨h1, h2, h3⟩ := hin
        have h3' := abs_le.mp h3
        have hXt'' := abs_le.mp hXt
        refine ⟨by linarith only [h1, hη], by linarith only [h2], abs_le.mpr ⟨?_, ?_⟩⟩
        · linarith only [h3'.1, hXt''.1, hη]
        · linarith only [h3'.2, hXt''.2, hη]
      have hne := xi_ne_zero_of_mem_saddleRegion h hη (by linarith only [hη8]) hX hXt' hreg
      rw [hpt] at hne
      have hne' : xiLine (X + δ) x ≠ 0 := hne
      have hL := lineLogDeriv_lipschitz h hη hη8 hT hE hX hXt hin0 hin
      have hdiff : ‖(x : ℂ) + (δ : ℂ) * I - ((a : ℂ) + (δ : ℂ) * I)‖ ≤ |v| := by
        have he : (x : ℂ) + (δ : ℂ) * I - ((a : ℂ) + (δ : ℂ) * I) = ((x - a : ℝ) : ℂ) := by
          push_cast
          ring
        rw [he, Complex.norm_real, Real.norm_eq_abs]
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith only [h1]), abs_of_nonneg (by linarith only [h1, h2])]
          linarith only [h2]
        · rw [abs_of_nonpos (by linarith only [h2]), abs_of_nonpos (by linarith only [h1, h2])]
          linarith only [h1]
      have hslope : xiLineDeriv (X + δ) x =
          lineLogDeriv X ((x : ℂ) + (δ : ℂ) * I) * xiLine (X + δ) x := by
        unfold lineLogDeriv
        rw [hpt, logDeriv_apply]
        exact (div_mul_cancel₀ _ hne').symm
      rw [hslope, ← sub_mul, norm_mul, hℓ]
      refine mul_le_mul_of_nonneg_right (hL.trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left hdiff (by positivity))
  have hsimp : a + v - a = v := by ring
  have hvv : 4 * powerSlopeError E η T / η * |v| * |v| = 4 * powerSlopeError E η T / η * v ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  rw [hsimp, hvv] at hmodel
  have hl1 : xiLine (X + δ) (a + v) =
      xi (1 / 2 + ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) + I * X) := by
    unfold xiLine
    congr 1
    push_cast
    ring
  have hl0 : xiLine (X + δ) a = xi (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X) := by
    unfold xiLine
    congr 1
    push_cast
    ring
  rw [hl1, hl0] at hmodel
  exact hmodel

/-! ## The size of `ξ` across the strip -/

/-- `G` crosses a bounded segment at height `X` with the slope `½ log(X/2π) + iπ/4`, up to a bounded factor. -/
theorem norm_archG_le_of_segment {X : ℝ} (hX : 1000 ≤ X) {s₀ s₁ : ℂ} (h0 : 0 < s₀.re) (h1 : 0 < s₁.re)
    (h0' : s₀.re ≤ 16) (h1' : s₁.re ≤ 16) (hy0 : |s₀.im - X| ≤ 1) (hy1 : |s₁.im - X| ≤ 1) :
    ‖archG s₁‖ ≤ ‖archG s₀‖ *
      Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re - (s₁.im - s₀.im) * (Real.pi / 4)) *
        Real.exp (2 * ‖s₁ - s₀‖ + 1) := by
  let p : ℝ → ℂ := fun r => s₀ + (r : ℂ) * (s₁ - s₀)
  have hpre (r : ℝ) : (p r).re = s₀.re + r * (s₁.re - s₀.re) := by
    simp [p, Complex.add_re, Complex.mul_re]
  have hpim (r : ℝ) : (p r).im = s₀.im + r * (s₁.im - s₀.im) := by
    simp [p, Complex.add_im, Complex.mul_im]
  have hconv (r : ℝ) (hr : r ∈ [[(0 : ℝ), 1]]) (A B C : ℝ) (hA : A ≤ C) (hB : B ≤ C) :
      A + r * (B - A) ≤ C := by
    rw [uIcc_of_le zero_le_one] at hr
    nlinarith only [hr.1, hr.2, hA, hB, mul_nonneg hr.1 (sub_nonneg.mpr hA)]
  have hconv' (r : ℝ) (hr : r ∈ [[(0 : ℝ), 1]]) (A B C : ℝ) (hA : C ≤ A) (hB : C ≤ B) :
      C ≤ A + r * (B - A) := by
    rw [uIcc_of_le zero_le_one] at hr
    nlinarith only [hr.1, hr.2, hA, hB, mul_nonneg hr.1 (sub_nonneg.mpr hA)]
  have hy0' := abs_le.mp hy0
  have hy1' := abs_le.mp hy1
  have hbounds (r : ℝ) (hr : r ∈ [[(0 : ℝ), 1]]) :
      0 < (p r).re ∧ (p r).re ≤ 16 ∧ X - 1 ≤ (p r).im ∧ (p r).im ≤ X + 1 := by
    rw [hpre, hpim]
    refine ⟨?_, hconv r hr _ _ _ h0' h1', hconv' r hr _ _ _ (by linarith only [hy0'.1])
      (by linarith only [hy1'.1]), hconv r hr _ _ _ (by linarith only [hy0'.2])
      (by linarith only [hy1'.2])⟩
    rcases le_total s₀.re s₁.re with hl | hl
    · exact lt_of_lt_of_le h0 (hconv' r hr _ _ _ le_rfl hl)
    · exact lt_of_lt_of_le h1 (hconv' r hr _ _ _ hl le_rfl)
  have hderiv (r : ℝ) (hr : r ∈ [[(0 : ℝ), 1]]) :
      HasDerivAt (fun x : ℝ => archG (p x)) (deriv archG (p r) * (s₁ - s₀)) r := by
    have hd := (differentiableAt_archG (w := p r) (hbounds r hr).1).hasDerivAt
    have hi : HasDerivAt (fun z : ℂ => s₀ + z * (s₁ - s₀)) (s₁ - s₀) (r : ℂ) := by
      have hh := ((hasDerivAt_id' (r : ℂ)).mul_const (s₁ - s₀)).const_add s₀
      simpa only [one_mul] using hh
    exact (hd.comp (r : ℂ) hi).comp_ofReal
  have hbound (r : ℝ) (hr : r ∈ [[(0 : ℝ), 1]]) :
      ‖deriv archG (p r) * (s₁ - s₀) - (horizontalSlope X * (s₁ - s₀)) * archG (p r)‖ ≤
        (2 * ‖s₁ - s₀‖ + 1) * ‖archG (p r)‖ := by
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbounds r hr
    have hY : 200 ≤ (p r).im := by linarith only [hb3, hX]
    have him : (p r) ≠ 1 := by
      intro he
      rw [he] at hY
      norm_num at hY
    have hne := archG_ne_zero hb1 him
    have hlog := norm_logDeriv_archG_sub_horizontalSlope_le_one hb1
      (by linarith only [hb2, hb3, hX]) hY
    rw [Complex.re_add_im] at hlog
    have hsl := norm_horizontalSlope_sub_le (by linarith only [hX] : 2 ≤ X)
      (abs_le.mpr ⟨by linarith only [hb3], by linarith only [hb4]⟩ : |(p r).im - X| ≤ 1)
    have hd : deriv archG (p r) = logDeriv archG (p r) * archG (p r) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hne]
    have he : deriv archG (p r) * (s₁ - s₀) - (horizontalSlope X * (s₁ - s₀)) * archG (p r) =
        ((logDeriv archG (p r) - horizontalSlope (p r).im) +
          (horizontalSlope (p r).im - horizontalSlope X)) * (s₁ - s₀) * archG (p r) := by
      rw [hd]
      ring
    rw [he, norm_mul, norm_mul]
    have hn := norm_add_le (logDeriv archG (p r) - horizontalSlope (p r).im)
      (horizontalSlope (p r).im - horizontalSlope X)
    have hs0 := norm_nonneg (s₁ - s₀)
    have hA0 := norm_nonneg (archG (p r))
    refine mul_le_mul_of_nonneg_right ?_ hA0
    nlinarith only [hn, hlog, hsl, hs0]
  have hm := HTGeometry.norm_sub_mul_exp_le (η := 2 * ‖s₁ - s₀‖ + 1) (u := 0) (w := 1)
    (by positivity) hderiv hbound
  simp only [sub_zero, Complex.ofReal_one, one_mul, abs_one, mul_one] at hm
  have hp0 : p 0 = s₀ := by simp [p]
  have hp1 : p 1 = s₁ := by simp [p]
  rw [hp0, hp1] at hm
  have hre : (horizontalSlope X * (s₁ - s₀)).re =
      (s₁.re - s₀.re) * (horizontalSlope X).re - (s₁.im - s₀.im) * (Real.pi / 4) := by
    rw [Complex.mul_re, horizontalSlope_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [hre] at hm
  have hn := norm_sub_norm_le (archG s₁) (archG s₀ * Complex.exp (horizontalSlope X * (s₁ - s₀)))
  rw [norm_mul, Complex.norm_exp, hre] at hn
  have hE1 : 0 ≤ ‖archG s₀‖ *
      Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re - (s₁.im - s₀.im) * (Real.pi / 4)) := by
    positivity
  nlinarith only [hm, hn, hE1]

/-- The loss of the anchor comparison at level `T^E`. -/
def powerRatio (E η T : ℝ) : ℝ :=
  3 * (T ^ E + 2) * Real.exp (12 * (E * Real.log T + 9) / η + 40)

theorem powerRatio_nonneg {E η T : ℝ} (hT : 1 ≤ T) : 0 ≤ powerRatio E η T := by
  have := Real.rpow_nonneg (by linarith only [hT] : 0 ≤ T) E
  unfold powerRatio
  positivity

/-- **`ξ` across the strip, relative to an anchor.** Against an anchor right of `½ + 2η`, every point of the strip
has size at most `powerRatio` times the exponential model with rate `½ log(X/2π)`. -/
theorem norm_xi_le_anchor {d η E T t X : ℝ} {s₀ s₁ : ℂ} (h : DepthTypical d η E T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (h0 : 1 / 2 + d + 2 * η ≤ s₀.re) (h0' : s₀.re ≤ 16) (h0t : |s₀.im - t| ≤ η) (h1 : 1 / 2 ≤ s₁.re)
    (h1' : s₁.re ≤ 16) (h1t : |s₁.im - t| ≤ 2) (hy0 : |s₀.im - X| ≤ 1) (hy1 : |s₁.im - X| ≤ 1) :
    ‖xi s₁‖ ≤ powerRatio E η T * ‖xi s₀‖ * Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) := by
  have hy0' := abs_le.mp hy0
  have hy1' := abs_le.mp hy1
  have him0 : s₀.im ≠ 0 := by linarith only [hy0'.1, hX] |> fun h => (ne_of_gt h)
  have him1 : s₁.im ≠ 0 := by linarith only [hy1'.1, hX] |> fun h => (ne_of_gt h)
  have hre0 : 0 < s₀.re := by linarith only [hη, h0, h.hd]
  have hre1 : 0 < s₁.re := by linarith only [h1]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT]
  have hlog := Real.log_nonneg hT1
  have hD : 0 ≤ 12 * (E * Real.log T + 9) / η := by positivity
  rw [xi_eq_archG_mul_zeta_offReal him1, xi_eq_archG_mul_zeta_offReal him0, norm_mul, norm_mul]
  have hz1 : ‖riemannZeta s₁‖ ≤ T ^ E + 2 := h.norm_le h1 h1t
  have hz0 : Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3 ≤ ‖riemannZeta s₀‖ := by
    rcases le_or_gt s₀.re 2 with hs2 | hs2
    · refine h.norm_ge hη hη1 hT hE ?_
      have he := disc_bound (d := d) (Y := s₀.im) (σ := s₀.re) h0 hs2 h0t
      rw [Complex.re_add_im] at he
      linarith only [he, hη]
    · have hb := (norm_riemannZeta_bounds_of_two_le_re hs2.le).1
      have hexp : Real.exp (-(12 * (E * Real.log T + 9) / η)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hD)
      linarith only [hb, hexp]
  have ha := norm_archG_le_of_segment hX hre0 hre1 h0' h1' hy0 hy1
  have hdist : ‖s₁ - s₀‖ ≤ 18 := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im (s₁ - s₀)
    simp only [Complex.sub_re, Complex.sub_im] at hnorm
    have h3 : |s₁.re - s₀.re| ≤ 16 := abs_le.mpr ⟨by linarith only [hre1, h0'], by linarith only [hre0, h1']⟩
    have h4 : |s₁.im - s₀.im| ≤ 2 := abs_le.mpr
      ⟨by linarith only [hy0'.2, hy1'.1], by linarith only [hy0'.1, hy1'.2]⟩
    linarith only [hnorm, h3, h4]
  have him2 : |s₁.im - s₀.im| ≤ 2 := abs_le.mpr
    ⟨by linarith only [hy0'.2, hy1'.1], by linarith only [hy0'.1, hy1'.2]⟩
  have hexp : Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re - (s₁.im - s₀.im) * (Real.pi / 4)) *
      Real.exp (2 * ‖s₁ - s₀‖ + 1) ≤
      Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) * Real.exp 40 := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_lt_four
    have hpi0 := Real.pi_pos
    have hm : -((s₁.im - s₀.im) * (Real.pi / 4)) ≤ 2 := by
      have h5 := neg_abs_le (s₁.im - s₀.im)
      have h6 := le_abs_self (s₁.im - s₀.im)
      nlinarith only [h5, h6, him2, hpi, hpi0, abs_nonneg (s₁.im - s₀.im)]
    linarith only [hm, hdist]
  have hA0 := norm_nonneg (archG s₀)
  have hZ0 := norm_nonneg (riemannZeta s₀)
  have hrt := Real.rpow_nonneg (by linarith only [hT] : 0 ≤ T) E
  have hanchor : ‖archG s₀‖ ≤
      3 * Real.exp (12 * (E * Real.log T + 9) / η) * (‖archG s₀‖ * ‖riemannZeta s₀‖) := by
    have hm := mul_le_mul_of_nonneg_left hz0 hA0
    have hcancel : 3 * Real.exp (12 * (E * Real.log T + 9) / η) *
        (Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3) = 1 := by
      rw [Real.exp_neg]
      field_simp
    calc
      _ = 3 * Real.exp (12 * (E * Real.log T + 9) / η) *
          (‖archG s₀‖ * (Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3)) := by
        rw [mul_left_comm, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  calc
    _ ≤ (‖archG s₀‖ * (Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) * Real.exp 40)) *
        (T ^ E + 2) := by
      refine mul_le_mul ?_ hz1 (norm_nonneg _) (by positivity)
      refine ha.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp hA0
    _ ≤ ((3 * Real.exp (12 * (E * Real.log T + 9) / η) * (‖archG s₀‖ * ‖riemannZeta s₀‖)) *
        (Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) * Real.exp 40)) * (T ^ E + 2) := by
      gcongr
    _ = _ := by
      unfold powerRatio
      rw [Real.exp_add]
      ring

end

end GaloisForLFunctions.ZeroConfigurationGeometry
