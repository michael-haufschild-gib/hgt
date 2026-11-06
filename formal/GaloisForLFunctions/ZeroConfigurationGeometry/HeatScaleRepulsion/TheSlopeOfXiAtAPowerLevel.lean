import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheComplexSaddleOfAGaussianAverage
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightXiModel

/-!
# The slope of `ξ` at a typical height of power level

At a typical height of level `T^E` (no zero right of `½ + η/4` within height `2`, and `|ζ| ≤ T^E`), the logarithmic
derivative of `ξ` is within `B ≍ E log T / η²` of the horizontal slope, on a complex neighbourhood of the horizontal
segment. So it is analytic there with Lipschitz constant `4B/η`, and this supplies the data of the complex saddle:

* `norm_logDeriv_sub_slope_le`: the slope bound;
* `lineLogDeriv_lipschitz`: the Cauchy estimate;
* `exists_saddle_fixedPoint`: the fixed point `u = y + 2τ (ξ′/ξ)(½ + u + iX)`, by contraction;
* `norm_window_model_le`: the quadratic model of `ξ` on the line through the saddle;
* `norm_archG_le_of_segment`, `LevelPair.norm_le_anchor`: the size of `ξ` across the strip, relative to an anchor right
  of `½ + 2η`, with the loss `powerRatio ≍ T^{E(1 + 12/η)}`.

Nothing here uses `ξ` beyond the factorization `ξ = G ζ` and the level of `ζ`, so the statements are made for a pair
`Λ = G Z` (`LevelPair`). This also covers `ξ` with a zero divided out.
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
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

/-- **A function of zeta type at level `T^E`.** `Z` is zero-free right of `½ + d + η/4` within height `2`, has size at
most `T^E + 2`, is anchored at `2 + it` and is bounded logarithmically right of the abscissa `2`; and `Λ = G Z` is
entire. -/
structure LevelPair (Z Λ : ℂ → ℂ) (d η E T t : ℝ) : Prop where
  hd : 0 ≤ d
  hd2 : d ≤ 1 / 2
  mem : t ∈ Icc T (2 * T)
  entire : Differentiable ℂ Λ
  factor : ∀ {s : ℂ}, 0 < s.re → s.im ≠ 0 → Λ s = archG s * Z s
  diff : ∀ {s : ℂ}, 1 / 2 + d + η / 4 ≤ s.re → |s.im - t| ≤ 2 → DifferentiableAt ℂ Z s
  ne_zero : ∀ {s : ℂ}, 1 / 2 + d + η / 4 ≤ s.re → |s.im - t| ≤ 2 → Z s ≠ 0
  norm_le : ∀ {s : ℂ}, 1 / 2 ≤ s.re → |s.im - t| ≤ 2 → ‖Z s‖ ≤ T ^ E + 2
  anchor : 1 / 3 ≤ ‖Z (2 + (t : ℂ) * I)‖
  far_logDeriv : ∀ {s : ℂ}, 2 < s.re → |s.im - t| ≤ 2 →
    ‖logDeriv Z s‖ ≤ 24 * (E * Real.log T + 9) / η ^ 2 + 3
  far_ge : ∀ {s : ℂ}, 2 < s.re → s.re ≤ 3 → |s.im - t| ≤ 2 →
    Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3 ≤ ‖Z s‖

namespace LevelPair

variable {Z Λ : ℂ → ℂ} {d η E T t : ℝ}

/-- The disc of radius `3/2 − d − η/4` about `2 + it` satisfies the hypotheses of Borel–Carathéodory. -/
theorem disc_hypotheses (h : LevelPair Z Λ d η E T t) (hη0 : 0 < η) :
    DifferentiableOn ℂ Z (ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4))
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4), Z s ≠ 0)
      ∧ (∀ s ∈ ball (2 + (t : ℂ) * I) (3 / 2 - d - η / 4), ‖Z s‖ ≤ T ^ E + 2)
      ∧ 1 / 3 ≤ ‖Z (2 + (t : ℂ) * I)‖ := by
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
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, h.anchor⟩
  · have hg := hgeom s hs
    exact (h.diff hg.1.le hg.2).differentiableWithinAt
  · have hg := hgeom s hs
    exact h.ne_zero hg.1.le hg.2
  · have hg := hgeom s hs
    exact h.norm_le (by linarith only [hg.1, hd, hη0]) hg.2

/-- The logarithmic derivative at depth `d`. -/
theorem norm_logDeriv_le (h : LevelPair Z Λ d η E T t) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) (hE : 0 ≤ E) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - d - η) :
    ‖logDeriv Z s‖ ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by
  have hd := h.hd
  have hd2 := h.hd2
  obtain ⟨hdiff, hne, hM, hm⟩ := h.disc_hypotheses hη0
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

/-- The lower bound at depth `d`. -/
theorem norm_ge (h : LevelPair Z Λ d η E T t) (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T)
    (hE : 0 ≤ E) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - d - η / 2) :
    Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3 ≤ ‖Z s‖ := by
  have hd := h.hd
  have hd2 := h.hd2
  obtain ⟨hdiff, hne, hM, hm⟩ := h.disc_hypotheses hη0
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

end LevelPair

/-- `ξ` and `ζ` form a pair at a height of depth `d`. -/
theorem DepthTypical.levelPair {d η E T t : ℝ} (h : DepthTypical d η E T t) (hη : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) (hE : 0 ≤ E) : LevelPair riemannZeta xi d η E T t where
  hd := h.hd
  hd2 := h.hd2
  mem := h.mem
  entire := xi_differentiable
  factor := fun _ him => xi_eq_archG_mul_zeta_offReal him
  diff := fun {s} _ hst => by
    refine differentiableAt_riemannZeta fun h1 => ?_
    rw [h1] at hst
    simp only [Complex.one_im] at hst
    have := (abs_le.mp hst).1
    linarith only [this, h.mem.1, hT]
  ne_zero := h.ne_zero
  norm_le := h.norm_le
  anchor := (norm_riemannZeta_bounds_of_two_le_re (by simp)).1
  far_logDeriv := fun {s} hs _ => by
    have hb := norm_logDeriv_riemannZeta_le_inv_sub_one_add_two (show 1 < s.re by linarith only [hs]) s.im
    rw [Complex.re_add_im] at hb
    have hi : 1 / (s.re - 1) ≤ 1 := (div_le_one (by linarith only [hs])).mpr (by linarith only [hs])
    have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
    have hB : 0 ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by positivity
    linarith only [hb, hi, hB]
  far_ge := fun {s} hs _ _ => by
    have hb := (norm_riemannZeta_bounds_of_two_le_re hs.le).1
    have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
    have hD : 0 ≤ 12 * (E * Real.log T + 9) / η := by positivity
    have hexp : Real.exp (-(12 * (E * Real.log T + 9) / η)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hD)
    linarith only [hb, hexp]

/-- `Λ′/Λ` in the coordinate `s = ½ + w + iX`. -/
def lineLogDeriv (Λ : ℂ → ℂ) (X : ℝ) (w : ℂ) : ℂ := logDeriv Λ (1 / 2 + w + I * X)

/-- `Λ` on the horizontal line at height `X`. -/
def lineFn (Λ : ℂ → ℂ) (X w : ℝ) : ℂ := Λ (1 / 2 + w + I * X)

theorem hasDerivAt_lineFn {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (X x : ℝ) :
    HasDerivAt (lineFn Λ X) (deriv Λ (1 / 2 + x + I * X)) x := by
  have hin : HasDerivAt (fun z : ℂ => (1 / 2 + z + I * X : ℂ)) 1 (x : ℂ) :=
    ((hasDerivAt_id' (x : ℂ)).const_add (1 / 2)).add_const (I * (X : ℂ))
  have hc := (hΛ (1 / 2 + (x : ℂ) + I * X)).hasDerivAt.comp (x : ℂ) hin
  rw [mul_one] at hc
  exact hc.comp_ofReal

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

/-- `Λ′/Λ = G′/G + Z′/Z` off the real axis. -/
theorem LevelPair.logDeriv_eq {Z Λ : ℂ → ℂ} {d η E T t : ℝ} (h : LevelPair Z Λ d η E T t) {s : ℂ}
    (hre : 0 < s.re) (him : s.im ≠ 0) (hdZ : DifferentiableAt ℂ Z s) (hZ : Z s ≠ 0) :
    logDeriv Λ s = logDeriv archG s + logDeriv Z s := by
  have hne1 : s ≠ 1 := fun he => him (by rw [he]; simp)
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.im ≠ 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_ne_fun Complex.continuous_im continuous_const)
  have hev : Λ =ᶠ[𝓝 s] fun z => archG z * Z z := by
    filter_upwards [hopen.mem_nhds ⟨hre, him⟩] with z hz using h.factor hz.1 hz.2
  rw [← logDeriv_mul s (archG_ne_zero hre hne1) hZ (differentiableAt_archG hre) hdZ,
    logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- **The slope at level `T^E`.** -/
theorem norm_logDeriv_sub_slope_le {Z Λ : ℂ → ℂ} {d η E T t X σ Y : ℝ}
    (h : LevelPair Z Λ d η E T t) (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hX : 1000 ≤ X) (hYX : |Y - X| ≤ 1) (hYt : |Y - t| ≤ η) (hσ : 1 / 2 + d + 2 * η ≤ σ)
    (hσX : σ ≤ X / 64) :
    ‖logDeriv Λ ((σ : ℂ) + Y * I) - horizontalSlope X‖ ≤ powerSlopeError E η T := by
  have hY := abs_le.mp hYX
  have hY999 : 999 ≤ Y := by linarith only [hX, hY.1]
  have hσ0 : 0 < σ := by linarith only [hη, hσ, h.hd]
  have him : ((σ : ℂ) + Y * I).im ≠ 0 := by
    simpa using (show Y ≠ 0 by linarith only [hY999])
  have hre : ((σ : ℂ) + Y * I).re = σ := by simp
  have him' : ((σ : ℂ) + Y * I).im = Y := by simp
  have hbox1 : 1 / 2 + d + η / 4 ≤ ((σ : ℂ) + Y * I).re := by rw [hre]; linarith only [hη, hσ]
  have hbox2 : |((σ : ℂ) + Y * I).im - t| ≤ 2 := by
    rw [him']
    exact hYt.trans (by linarith only [hη1])
  have he := h.logDeriv_eq (s := (σ : ℂ) + Y * I) (by rw [hre]; exact hσ0) him
    (h.diff hbox1 hbox2) (h.ne_zero hbox1 hbox2)
  have harch := norm_logDeriv_archG_sub_horizontalSlope_le_one hσ0
    (by linarith only [hσX, hX, hY.1]) (by linarith only [hY999] : 200 ≤ Y)
  have hslope := norm_horizontalSlope_sub_le (by linarith only [hX] : 2 ≤ X) hYX
  have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
  have hB : 0 ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by positivity
  have hz : ‖logDeriv Z ((σ : ℂ) + Y * I)‖ ≤ 24 * (E * Real.log T + 9) / η ^ 2 + 3 := by
    rcases le_or_gt σ 2 with hσ2 | hσ2
    · have hb := h.norm_logDeriv_le hη hη1 hT hE (disc_bound hσ hσ2 hYt)
      linarith only [hb]
    · exact h.far_logDeriv (by rw [hre]; exact hσ2) hbox2
  have hsum : logDeriv Λ ((σ : ℂ) + Y * I) - horizontalSlope X =
      (logDeriv archG ((σ : ℂ) + Y * I) - horizontalSlope Y) +
        logDeriv Z ((σ : ℂ) + Y * I) + (horizontalSlope Y - horizontalSlope X) := by
    rw [he]
    ring
  rw [hsum]
  unfold powerSlopeError
  have h1 := norm_add₃_le (a := logDeriv archG ((σ : ℂ) + Y * I) - horizontalSlope Y)
    (b := logDeriv Z ((σ : ℂ) + Y * I)) (c := horizontalSlope Y - horizontalSlope X)
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

/-- **The data of the saddle.** On the box `saddleRegion`, `Λ` is zero-free with slope error `B`; across the strip it has
loss `K` against an anchor; and right of `9/2` it grows like `ξ`. -/
structure LineModel (Λ : ℂ → ℂ) (d η B K t : ℝ) : Prop where
  hd : 0 ≤ d
  entire : Differentiable ℂ Λ
  hB : 0 < B
  hK : 0 < K
  ne_zero : ∀ {X : ℝ} {w : ℂ}, 1000 ≤ X → |X - t| ≤ η → w ∈ saddleRegion d η t X →
    Λ (1 / 2 + w + I * X) ≠ 0
  slope : ∀ {X : ℝ} {w : ℂ}, 1000 ≤ X → |X - t| ≤ η → w ∈ saddleRegion d η t X →
    ‖lineLogDeriv Λ X w - horizontalSlope X‖ ≤ B
  anchor : ∀ {X : ℝ} {s₀ s₁ : ℂ}, 1000 ≤ X → 1 / 2 + d + 2 * η ≤ s₀.re → s₀.re ≤ 3 →
    |s₀.im - t| ≤ η → 1 / 2 ≤ s₁.re → s₁.re ≤ 16 → |s₁.im - t| ≤ 2 → |s₀.im - X| ≤ 1 →
    |s₁.im - X| ≤ 1 →
    ‖Λ s₁‖ ≤ K * ‖Λ s₀‖ * Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re)
  integrable : ∀ {τ X : ℝ}, 0 < τ →
    Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / (16 * τ))) * ‖lineFn Λ X w‖)
  model : ∀ {X w : ℝ}, 200 ≤ X → 9 / 2 ≤ w → w ≤ X / 32 - 1 / 2 →
    ‖lineFn Λ X w‖ ≤ ‖lineFn Λ X (9 / 2)‖ * Real.exp ((w - 9 / 2) * (horizontalSlope X).re) *
      Real.exp (1 / 8 * (w - 9 / 2))
  grow : ∀ {X W w : ℝ}, 200 ≤ X → 9 / 2 ≤ W → W ≤ w →
    ‖lineFn Λ X w‖ ≤ ‖lineFn Λ X W‖ *
      Real.exp (((horizontalSlope X).re + 2 + (w + 1 / 2) / (2 * X)) * (w - W))

theorem LevelPair.ne_zero_of_mem_saddleRegion {Z Λ : ℂ → ℂ} {d η E T t X : ℝ} {w : ℂ}
    (h : LevelPair Z Λ d η E T t) (hη : 0 < η) (hη1 : η ≤ 1) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η) (hw : w ∈ saddleRegion d η t X) : Λ (1 / 2 + w + I * X) ≠ 0 := by
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
  have hre : (((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I).re = 1 / 2 + w.re := by simp
  have him' : (((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I).im = X + w.im := by simp
  have hre0 : 0 < (((1 / 2 + w.re : ℝ) : ℂ) + ((X + w.im : ℝ) : ℂ) * I).re := by
    rw [hre]
    linarith only [hη, h1, h.hd]
  rw [h.factor hre0 him]
  refine mul_ne_zero (archG_ne_zero hre0 hne1) (h.ne_zero ?_ ?_)
  · rw [hre]
    linarith only [hη, h1]
  · rw [him']
    exact h3.trans (by linarith only [hη1])

theorem LevelPair.norm_lineLogDeriv_sub_le {Z Λ : ℂ → ℂ} {d η E T t X : ℝ} {w : ℂ}
    (h : LevelPair Z Λ d η E T t) (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hX : 1000 ≤ X) (hXt : |X - t| ≤ η) (hw : w ∈ saddleRegion d η t X) :
    ‖lineLogDeriv Λ X w - horizontalSlope X‖ ≤ powerSlopeError E η T := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold lineLogDeriv
  rw [line_point]
  have him_abs : |w.im| ≤ 2 * η := by
    have he : w.im = (X + w.im - t) - (X - t) := by ring
    rw [he]
    refine (abs_sub _ _).trans ?_
    linarith only [h3, hXt]
  refine norm_logDeriv_sub_slope_le h hη (by linarith only [hη1]) hT hE hX ?_ ?_ ?_ ?_
  · rw [add_sub_cancel_left]
    linarith only [him_abs, hη1]
  · exact h3
  · linarith only [h1]
  · linarith only [h2, hX]

theorem differentiable_deriv_of_differentiable {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) :
    Differentiable ℂ (deriv Λ) := fun z =>
  ((hΛ.differentiableOn (s := univ)).deriv isOpen_univ z (mem_univ z)).differentiableAt univ_mem

theorem differentiableAt_lineLogDeriv {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) {X : ℝ} {w : ℂ}
    (hne : Λ (1 / 2 + w + I * X) ≠ 0) : DifferentiableAt ℂ (lineLogDeriv Λ X) w := by
  have he : lineLogDeriv Λ X = fun w => deriv Λ (1 / 2 + w + I * X) / Λ (1 / 2 + w + I * X) := by
    funext z
    exact logDeriv_apply _ _
  rw [he]
  have hin : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 + z + I * X : ℂ)) w := by fun_prop
  exact ((differentiable_deriv_of_differentiable hΛ _).comp w hin).div ((hΛ _).comp w hin) hne

namespace LineModel

variable {Λ : ℂ → ℂ} {d η B K t : ℝ}

theorem continuous_lineFn (h : LineModel Λ d η B K t) (X : ℝ) : Continuous (lineFn Λ X) :=
  h.entire.continuous.comp (by fun_prop)

/-- The Cauchy estimate on the inner box. -/
theorem norm_deriv_lineLogDeriv_le (h : LineModel Λ d η B K t) {X : ℝ} {w : ℂ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hw : w ∈ innerBox d η) :
    ‖deriv (lineLogDeriv Λ X) w‖ ≤ 4 * B / η := by
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
  have hd : DifferentiableOn ℂ (fun z => lineLogDeriv Λ X z - horizontalSlope X)
      (closedBall w (η / 4)) := fun z hz =>
    ((differentiableAt_lineLogDeriv h.entire (h.ne_zero hX hXt' (hsub z hz))).sub_const
      _).differentiableWithinAt
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < η / 4)
    (hd.diffContOnCl_ball subset_rfl) (C := B) (fun z hz =>
      h.slope hX hXt' (hsub z (sphere_subset_closedBall hz)))
  rw [deriv_sub_const] at hC
  refine hC.trans (le_of_eq ?_)
  field_simp

/-- `Λ′/Λ` is Lipschitz on the inner box. -/
theorem lineLogDeriv_lipschitz (h : LineModel Λ d η B K t) {X : ℝ} {w₁ w₂ : ℂ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (h₁ : w₁ ∈ innerBox d η) (h₂ : w₂ ∈ innerBox d η) :
    ‖lineLogDeriv Λ X w₂ - lineLogDeriv Λ X w₁‖ ≤ 4 * B / η * ‖w₂ - w₁‖ := by
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
    (fun z hz => differentiableAt_lineLogDeriv h.entire (h.ne_zero hX hXt' (hsub z hz)))
    (fun z hz => h.norm_deriv_lineLogDeriv_le hη hη8 hX hXt hz) h₁ h₂

/-- **The complex saddle exists.** The map `w ↦ y + 2τ (Λ′/Λ)(½ + w + iX)` contracts a small ball about the
Euler-free saddle `y + 2τ a(X)`. -/
theorem exists_saddle_fixedPoint (h : LineModel Λ d η B K t) {X τ y : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hτ : 0 < τ)
    (hsub : closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * B) ⊆ innerBox d η)
    (hlip : 2 * τ * (4 * B / η) ≤ 1 / 2) :
    ∃ u ∈ closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * B),
      u = (y : ℂ) + 2 * (τ : ℂ) * lineLogDeriv Λ X u := by
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hTB := h.hB
  set c₀ := (y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X with hc₀
  set R := 2 * τ * B with hR
  have hR0 : 0 ≤ R := by positivity
  let G : ℂ → ℂ := fun w => (y : ℂ) + 2 * (τ : ℂ) * lineLogDeriv Λ X w
  have hnorm2 : ‖(2 : ℂ) * (τ : ℂ)‖ = 2 * τ := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hmaps : MapsTo G (closedBall c₀ R) (closedBall c₀ R) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have he : G w - c₀ = 2 * (τ : ℂ) * (lineLogDeriv Λ X w - horizontalSlope X) := by
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
    exact mul_le_mul_of_nonneg_left (h.slope hX hXt' hreg) (by positivity)
  let K' : NNReal := 1 / 2
  have hK : (K' : ℝ) = 1 / 2 := by simp [K']
  have hcontr : ContractingWith K' (hmaps.restrict G (closedBall c₀ R) (closedBall c₀ R)) := by
    refine ⟨by rw [← NNReal.coe_lt_coe, hK]; norm_num, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, hK]
    rw [dist_eq_norm, dist_eq_norm]
    have he : G a - G b = 2 * (τ : ℂ) * (lineLogDeriv Λ X a - lineLogDeriv Λ X b) := by
      simp only [G]
      ring
    rw [he, norm_mul, hnorm2]
    have hL := h.lineLogDeriv_lipschitz hη hη8 hX hXt (hsub hb) (hsub ha)
    calc
      _ ≤ 2 * τ * (4 * B / η * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 * τ * (4 * B / η) * ‖a - b‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
  haveI : CompleteSpace (closedBall c₀ R) := isClosed_closedBall.completeSpace_coe
  obtain ⟨p, hp, _⟩ := hcontr.exists_fixedPoint ⟨c₀, mem_closedBall_self hR0⟩ (edist_ne_top _ _)
  refine ⟨p.1, p.2, ?_⟩
  have := congrArg Subtype.val hp
  simpa only [MapsTo.val_restrict_apply] using this.symm

/-- **The second-order model on the line through the saddle.** -/
theorem norm_window_model_le (h : LineModel Λ d η B K t) {X a δ v : ℝ} {ℓ : ℂ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hℓ : ℓ = lineLogDeriv Λ X ((a : ℂ) + (δ : ℂ) * I))
    (hbox : ∀ x ∈ [[a, a + v]], (x : ℂ) + (δ : ℂ) * I ∈ innerBox d η) :
    ‖Λ (1 / 2 + ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) + I * X) -
        Λ (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X) * Complex.exp ((v : ℂ) * ℓ)‖ ≤
      ‖Λ (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X)‖ * Real.exp (v * ℓ.re) *
        (Real.exp (4 * B / η * v ^ 2) - 1) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hTB := h.hB
  have hpt (x : ℝ) : (1 / 2 + ((x : ℂ) + (δ : ℂ) * I) + I * X : ℂ) =
      1 / 2 + (x : ℂ) + I * ((X + δ : ℝ) : ℂ) := by
    push_cast
    ring
  have hmodel := HTGeometry.norm_sub_mul_exp_le (F := lineFn Λ (X + δ))
    (F' := fun x : ℝ => deriv Λ (1 / 2 + (x : ℂ) + I * ((X + δ : ℝ) : ℂ)))
    (a := ℓ) (η := 4 * B / η * |v|) (u := a) (w := a + v)
    (by have := abs_pos.mpr hv; positivity) (fun x _ => hasDerivAt_lineFn h.entire (X + δ) x)
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
      have hne := h.ne_zero hX hXt' hreg
      rw [hpt] at hne
      have hne' : lineFn Λ (X + δ) x ≠ 0 := hne
      have hL := h.lineLogDeriv_lipschitz hη hη8 hX hXt hin0 hin
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
      have hslope : deriv Λ (1 / 2 + (x : ℂ) + I * ((X + δ : ℝ) : ℂ)) =
          lineLogDeriv Λ X ((x : ℂ) + (δ : ℂ) * I) * lineFn Λ (X + δ) x := by
        unfold lineLogDeriv
        rw [hpt, logDeriv_apply]
        exact (div_mul_cancel₀ _ hne').symm
      rw [hslope, ← sub_mul, norm_mul, hℓ]
      refine mul_le_mul_of_nonneg_right (hL.trans ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left hdiff (by positivity))
  have hsimp : a + v - a = v := by ring
  have hvv : 4 * B / η * |v| * |v| = 4 * B / η * v ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  rw [hsimp, hvv] at hmodel
  have hl1 : lineFn Λ (X + δ) (a + v) =
      Λ (1 / 2 + ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) + I * X) := by
    unfold lineFn
    congr 1
    push_cast
    ring
  have hl0 : lineFn Λ (X + δ) a = Λ (1 / 2 + ((a : ℂ) + (δ : ℂ) * I) + I * X) := by
    unfold lineFn
    congr 1
    push_cast
    ring
  rw [hl1, hl0] at hmodel
  exact hmodel

end LineModel

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

/-- **`Λ` across the strip, relative to an anchor.** Against an anchor right of `½ + 2η`, every point of the strip
has size at most `powerRatio` times the exponential model with rate `½ log(X/2π)`. -/
theorem LevelPair.norm_le_anchor {Z Λ : ℂ → ℂ} {d η E T t X : ℝ} {s₀ s₁ : ℂ}
    (h : LevelPair Z Λ d η E T t)
    (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (h0 : 1 / 2 + d + 2 * η ≤ s₀.re) (h0' : s₀.re ≤ 3) (h0t : |s₀.im - t| ≤ η) (h1 : 1 / 2 ≤ s₁.re)
    (h1' : s₁.re ≤ 16) (h1t : |s₁.im - t| ≤ 2) (hy0 : |s₀.im - X| ≤ 1) (hy1 : |s₁.im - X| ≤ 1) :
    ‖Λ s₁‖ ≤ powerRatio E η T * ‖Λ s₀‖ * Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) := by
  have hy0' := abs_le.mp hy0
  have hy1' := abs_le.mp hy1
  have him0 : s₀.im ≠ 0 := by linarith only [hy0'.1, hX] |> fun h => (ne_of_gt h)
  have him1 : s₁.im ≠ 0 := by linarith only [hy1'.1, hX] |> fun h => (ne_of_gt h)
  have hre0 : 0 < s₀.re := by linarith only [hη, h0, h.hd]
  have hre1 : 0 < s₁.re := by linarith only [h1]
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT]
  have hlog := Real.log_nonneg hT1
  have hD : 0 ≤ 12 * (E * Real.log T + 9) / η := by positivity
  rw [h.factor hre1 him1, h.factor hre0 him0, norm_mul, norm_mul]
  have hz1 : ‖Z s₁‖ ≤ T ^ E + 2 := h.norm_le h1 h1t
  have hz0 : Real.exp (-(12 * (E * Real.log T + 9) / η)) / 3 ≤ ‖Z s₀‖ := by
    rcases le_or_gt s₀.re 2 with hs2 | hs2
    · refine h.norm_ge hη hη1 hT hE ?_
      have he := disc_bound (d := d) (Y := s₀.im) (σ := s₀.re) h0 hs2 h0t
      rw [Complex.re_add_im] at he
      linarith only [he, hη]
    · exact h.far_ge hs2 h0' (h0t.trans (by linarith only [hη1]))
  have ha := norm_archG_le_of_segment hX hre0 hre1 (by linarith only [h0']) h1' hy0 hy1
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
  have hZ0 := norm_nonneg (Z s₀)
  have hrt := Real.rpow_nonneg (by linarith only [hT] : 0 ≤ T) E
  have hanchor : ‖archG s₀‖ ≤
      3 * Real.exp (12 * (E * Real.log T + 9) / η) * (‖archG s₀‖ * ‖Z s₀‖) := by
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
    _ ≤ ((3 * Real.exp (12 * (E * Real.log T + 9) / η) * (‖archG s₀‖ * ‖Z s₀‖)) *
        (Real.exp ((s₁.re - s₀.re) * (horizontalSlope X).re) * Real.exp 40)) * (T ^ E + 2) := by
      gcongr
    _ = _ := by
      unfold powerRatio
      rw [Real.exp_add]
      ring

/-- A level pair supplies the line model, given the behaviour of `Λ` right of `9/2`. -/
theorem LevelPair.lineModel {Z Λ : ℂ → ℂ} {d η E T t : ℝ} (h : LevelPair Z Λ d η E T t)
    (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hint : ∀ {τ X : ℝ}, 0 < τ →
      Integrable (fun w : ℝ => Real.exp (-(w ^ 2 / (16 * τ))) * ‖lineFn Λ X w‖))
    (hmodel : ∀ {X w : ℝ}, 200 ≤ X → 9 / 2 ≤ w → w ≤ X / 32 - 1 / 2 →
      ‖lineFn Λ X w‖ ≤ ‖lineFn Λ X (9 / 2)‖ * Real.exp ((w - 9 / 2) * (horizontalSlope X).re) *
        Real.exp (1 / 8 * (w - 9 / 2)))
    (hgrow : ∀ {X W w : ℝ}, 200 ≤ X → 9 / 2 ≤ W → W ≤ w →
      ‖lineFn Λ X w‖ ≤ ‖lineFn Λ X W‖ *
        Real.exp (((horizontalSlope X).re + 2 + (w + 1 / 2) / (2 * X)) * (w - W))) :
    LineModel Λ d η (powerSlopeError E η T) (powerRatio E η T) t where
  hd := h.hd
  entire := h.entire
  hB := powerSlopeError_pos hE (by linarith only [hT])
  hK := by
    have hT0 : 0 < T := by linarith only [hT]
    have := Real.rpow_pos_of_pos hT0 E
    unfold powerRatio
    positivity
  ne_zero := fun hX hXt hw =>
    h.ne_zero_of_mem_saddleRegion hη (by linarith only [hη2]) hX hXt hw
  slope := fun hX hXt hw => h.norm_lineLogDeriv_sub_le hη hη2 hT hE hX hXt hw
  anchor := fun hX h0 h0' h0t h1 h1' h1t hy0 hy1 =>
    h.norm_le_anchor hη (by linarith only [hη2]) hT hE hX h0 h0' h0t h1 h1' h1t hy0 hy1
  integrable := hint
  model := hmodel
  grow := hgrow

end

end GaloisForLFunctions.ZeroConfigurationGeometry
