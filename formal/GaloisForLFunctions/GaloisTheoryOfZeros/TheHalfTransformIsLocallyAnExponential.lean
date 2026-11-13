import GaloisForLFunctions.GaloisTheoryOfZeros.TheHalfTransformIsXiAtTheSaddlePoint

/-!
# The half transform is locally an exponential

Near a far point `(τ₀, z₀)` the half transform `𝒜(τ, z)` of the heat family is an exponential in
both variables. Put `s₀ = 1/2 + iz₀`, let `a₀` be the slope of `ξ` at the base point `s₀ + κ` and
`M₀ = ξ(s₀ + 2τ₀a₀) e^{−τ₀a₀²}` the saddle value. For `τ₀, τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, `‖z − z₀‖ ≤ 1` and `‖z₀‖` large,

`𝒜(τ, z) = M₀ e^{i a₀ (z − z₀) + a₀² (τ − τ₀)} (1 + θ)`,  `‖θ‖ ≤ ε`

(`exists_norm_halfHeat_sub_saddleModel_le`). The rate in the time is the square of the rate in
the point: the model solves the heat equation `∂_τ = −∂_z²` of the family.

Mechanism. The saddle value at `(τ, s)` is `ξ(q) e^{−τa²}`, `q = s + 2τa`. The two saddle points
`p = s₀ + 2τ₀a₀` and `q` lie in a disc around the base point of radius `O(Re a₀)`, to its right
by `t₀ Re a₀`, and there the slope of `ξ` is `a₀` up to an error that decays exponentially in
`Re a₀` (the modulus of the base point is `2π e^{2 Re a₀}`). One comparison of two values of `ξ`
along the segment from `p` to `q` gives `ξ(q) = ξ(p) e^{(q − p) a₀} (1 + o(1))`, and

`(q − p) a₀ − τa² + τ₀a₀² = a₀ (s − s₀) + a₀² (τ − τ₀) − τ (a − a₀)²`,

where `a − a₀ = O(1/‖s₀ + κ‖)`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Elementary facts -/

/-- `K (1 + x)² e^{−cx} ≤ ε` for `x` large. -/
theorem exists_forall_sq_mul_exp_neg_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (K : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, A ≤ x → K * (1 + x) ^ 2 * Real.exp (-(c * x)) ≤ ε := by
  have h1 : Tendsto (fun x : ℝ => c * (1 + x)) atTop atTop :=
    (tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hc
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
  have h3 : Tendsto (fun x : ℝ => K * Real.exp c / c ^ 2 *
      ((c * (1 + x)) ^ 2 * Real.exp (-(c * (1 + x))))) atTop (𝓝 0) := by
    have := h2.const_mul (K * Real.exp c / c ^ 2)
    rw [mul_zero] at this
    exact this
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (h3.eventually_lt_const hε)
  refine ⟨max a 0, le_max_right _ _, fun x hx => ?_⟩
  have h4 := (ha x ((le_max_left _ _).trans hx)).le
  have e : K * Real.exp c / c ^ 2 * ((c * (1 + x)) ^ 2 * Real.exp (-(c * (1 + x)))) =
      K * (1 + x) ^ 2 * Real.exp (-(c * x)) := by
    have h5 : Real.exp (-(c * (1 + x))) = (Real.exp c)⁻¹ * Real.exp (-(c * x)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    have hc' : c ≠ 0 := hc.ne'
    have he : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
    rw [h5]
    field_simp
  rwa [e] at h4

/-- `2^y ≤ e^{1 − x/2}` for `y ≤ 1/2 − x` and `x ≥ 1`. -/
theorem two_rpow_le_exp {x y : ℝ} (hx : 1 ≤ x) (hy : y ≤ 1 / 2 - x) :
    (2 : ℝ) ^ y ≤ Real.exp (1 - x / 2) := by
  rw [Real.rpow_def_of_pos two_pos]
  apply Real.exp_le_exp.2
  have h1 := Real.log_two_gt_d9
  have h2 : Real.log 2 * y ≤ Real.log 2 * (1 / 2 - x) :=
    mul_le_mul_of_nonneg_left hy (by linarith)
  have h3 : Real.log 2 * (1 / 2 - x) ≤ 1 / 2 * (1 / 2 - x) :=
    mul_le_mul_of_nonpos_right (by linarith) (by linarith)
  linarith

/-- `(1 + x)² ≤ e^{2x}` for `x ≥ 0`. -/
theorem one_add_sq_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ 2 ≤ Real.exp (2 * x) := by
  have h1 := Real.add_one_le_exp x
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ x + 1) h1
  rw [h2]
  linarith

/-! ## Two nearby points and their saddle points -/

/-- The radius of a disc around the base point `s₀ + κ` that contains the saddle points of all
points within distance one of `s₀`, at all times of the box; `α` is the real part of the slope. -/
def modelRadius (T₀ κ α : ℝ) : ℝ := 1 + κ + 2 * T₀ * (2 + α)

/-- The deviation of the slope of `ξ` from the slope at the base point on that disc, to the right
of the base point by `t₀ (α − 1) − 1`. -/
def modelSlopeError (t₀ T₀ κ α : ℝ) : ℝ :=
  (16 + 2 * modelRadius T₀ κ α) / (2 * Real.pi * Real.exp (2 * α)) +
    Real.exp (1 - t₀ * (α - 1) / 2) / 12

/-- Two points `s₀, s` within distance one, at two times of the box, with their slopes; the base
point `s₀ + κ` is far from the origin on the scale of the saddle. -/
structure SlopePair (t₀ T₀ κ : ℝ) (τ₀ s₀ a₀ τ s a : ℂ) : Prop where
  base : SlopeConfig t₀ T₀ κ τ₀ s₀ a₀
  far₀ : 2 * T₀ + κ ≤ t₀ * a₀.re
  pt : SlopeConfig t₀ T₀ κ τ s a
  far : 2 * T₀ + κ ≤ t₀ * a.re
  near : ‖s - s₀‖ ≤ 1
  radius_le : modelRadius T₀ κ a₀.re ≤ ‖s₀ + (κ : ℂ)‖ / 4
  one_le : 1 ≤ t₀ * (a₀.re - 1)

namespace SlopePair

variable {t₀ T₀ κ : ℝ} {τ₀ s₀ a₀ τ s a : ℂ}

theorem six_le_radius (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    6 ≤ modelRadius T₀ κ a₀.re := by
  have h1 := h.base.hκ
  have h2 := mul_nonneg h.base.T₀_pos.le
    (by linarith [h.base.four_le_re] : (0 : ℝ) ≤ 2 + a₀.re)
  rw [modelRadius]
  linarith

theorem four_mul_le_radius (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    4 * T₀ ≤ modelRadius T₀ κ a₀.re := by
  have h1 := h.base.hκ
  have h2 := mul_nonneg h.base.T₀_pos.le (by linarith [h.base.four_le_re] : (0 : ℝ) ≤ a₀.re)
  rw [modelRadius]
  linarith

theorem le_norm_base (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) : 24 ≤ ‖s₀ + (κ : ℂ)‖ := by
  linarith [h.six_le_radius, h.radius_le]

/-- The slopes at the two base points differ by `2/‖s₀ + κ‖` at most. -/
theorem norm_slope_sub_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    ‖a - a₀‖ ≤ 2 / ‖s₀ + (κ : ℂ)‖ := by
  have hB := h.le_norm_base
  have hre : |(s - s₀).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h.near
  have him : |(s - s₀).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h.near
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have h1 := norm_xiSlope_sub_base_le (b := s₀ + (κ : ℂ)) (w := s + (κ : ℂ)) (κ := 1) (h := 1)
    (m := ‖s₀ + (κ : ℂ)‖ / 4) (by linarith [h.base.base_re]) (by linarith [h.pt.base_re])
    zero_le_one
    (by rw [Complex.add_re, Complex.add_re]; linarith [(abs_le.1 hre).1])
    (by rw [Complex.add_im, Complex.add_im, add_sub_add_right_eq_sub]; exact him)
    (by linarith) (by linarith)
  rw [← h.pt.ha, ← h.base.ha] at h1
  have e : s + (κ : ℂ) - (s₀ + (κ : ℂ)) = s - s₀ := by ring
  rw [e] at h1
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h2 := mul_le_mul_of_nonneg_right h.near (by linarith : (0 : ℝ) ≤ ‖s₀ + (κ : ℂ)‖)
  linarith

theorem abs_re_sub_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) : |a.re - a₀.re| ≤ 1 / 12 := by
  have h1 := (Complex.abs_re_le_norm (a - a₀)).trans h.norm_slope_sub_le
  rw [Complex.sub_re] at h1
  have h2 : 2 / ‖s₀ + (κ : ℂ)‖ ≤ 2 / 24 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h.le_norm_base
  linarith

/-- The saddle point of `(τ₀, s₀)` lies in the disc around the base point. -/
theorem norm_saddle₀_sub_base_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    ‖s₀ + 2 * τ₀ * a₀ - (s₀ + (κ : ℂ))‖ ≤ modelRadius T₀ κ a₀.re := by
  have e : s₀ + 2 * τ₀ * a₀ - (s₀ + (κ : ℂ)) = 2 * τ₀ * a₀ - (κ : ℂ) := by ring
  rw [e, modelRadius]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [h.base.hκ])]
  have h1 := h.base.norm_two_mul_le
  have h2 := h.base.T₀_pos
  linarith

/-- The saddle point of `(τ, s)` lies in the disc around the base point of `s₀`. -/
theorem norm_saddle_sub_base_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    ‖s + 2 * τ * a - (s₀ + (κ : ℂ))‖ ≤ modelRadius T₀ κ a₀.re := by
  have e : s + 2 * τ * a - (s₀ + (κ : ℂ)) = (s - s₀) + (2 * τ * a - (κ : ℂ)) := by ring
  rw [e, modelRadius]
  refine (norm_add_le _ _).trans ?_
  have h0 := norm_sub_le (2 * τ * a) (κ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [h.base.hκ])] at h0
  have h1 := h.pt.norm_two_mul_le
  have h2 := h.base.T₀_pos
  have h3 := (abs_le.1 h.abs_re_sub_le).2
  have h4 : 2 * T₀ * (1 + a.re) ≤ 2 * T₀ * (2 + a₀.re) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [h.near]

theorem norm_saddle_sub_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    ‖s + 2 * τ * a - (s₀ + 2 * τ₀ * a₀)‖ ≤ 2 * modelRadius T₀ κ a₀.re := by
  have e : s + 2 * τ * a - (s₀ + 2 * τ₀ * a₀) =
      (s + 2 * τ * a - (s₀ + (κ : ℂ))) - (s₀ + 2 * τ₀ * a₀ - (s₀ + (κ : ℂ))) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith [h.norm_saddle_sub_base_le, h.norm_saddle₀_sub_base_le]

/-- Both saddle points lie to the right of the base point by `t₀ (Re a₀ − 1) − 1`. -/
theorem le_re_saddle₀ (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    (s₀ + (κ : ℂ)).re - 1 + t₀ * (a₀.re - 1) ≤ (s₀ + 2 * τ₀ * a₀).re := by
  have h1 := h.base.le_re_two_mul h.far₀
  have h2 := h.base.ht₀
  rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]
  linarith

theorem le_re_saddle (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) :
    (s₀ + (κ : ℂ)).re - 1 + t₀ * (a₀.re - 1) ≤ (s + 2 * τ * a).re := by
  have h1 := h.pt.le_re_two_mul h.far
  have h2 := h.base.ht₀
  have h3 := (abs_le.1 h.abs_re_sub_le).1
  have h4 : t₀ * (a₀.re - 1) ≤ t₀ * a.re := mul_le_mul_of_nonneg_left (by linarith) h2.le
  have hre : |(s - s₀).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h.near
  rw [Complex.sub_re] at hre
  rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]
  linarith [(abs_le.1 hre).1]

/-- **The slope of `ξ` between the two saddle points.** On the segment from `s₀ + 2τ₀a₀` to
`s + 2τa` the logarithmic derivative of `ξ` is `a₀` up to the slope error: the segment lies in
the disc around the base point, whose radius is small against the modulus `2π e^{2 Re a₀}` of the
base point, and far to the right, where `ζ'/ζ` is exponentially small. -/
theorem norm_logDeriv_xi_sub_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) {w : ℂ}
    (hw : w ∈ segment ℝ (s₀ + 2 * τ₀ * a₀) (s + 2 * τ * a)) :
    1 < w.re ∧ ‖logDeriv xi w - a₀‖ ≤ modelSlopeError t₀ T₀ κ a₀.re := by
  have hB := h.le_norm_base
  have hD := h.radius_le
  have hD6 := h.six_le_radius
  have hb := h.base.base_re
  have h1 := h.one_le
  -- the segment lies in the disc around the base point
  have hball : ‖w - (s₀ + (κ : ℂ))‖ ≤ modelRadius T₀ κ a₀.re := by
    have hp : s₀ + 2 * τ₀ * a₀ ∈ closedBall (s₀ + (κ : ℂ)) (modelRadius T₀ κ a₀.re) := by
      rw [mem_closedBall, dist_eq_norm]
      exact h.norm_saddle₀_sub_base_le
    have hq : s + 2 * τ * a ∈ closedBall (s₀ + (κ : ℂ)) (modelRadius T₀ κ a₀.re) := by
      rw [mem_closedBall, dist_eq_norm]
      exact h.norm_saddle_sub_base_le
    have := (convex_closedBall (s₀ + (κ : ℂ)) (modelRadius T₀ κ a₀.re)).segment_subset hp hq hw
    rwa [mem_closedBall, dist_eq_norm] at this
  have him : |w.im - (s₀ + (κ : ℂ)).im| ≤ modelRadius T₀ κ a₀.re := by
    rw [← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans hball
  -- and to the right of the base point
  obtain ⟨θ, hθ0, hθ1, hre, -⟩ := re_im_of_mem_segment hw
  have hre' : (s₀ + (κ : ℂ)).re - 1 + t₀ * (a₀.re - 1) ≤ w.re := by
    have := le_convexCombo hθ0 hθ1 h.le_re_saddle₀ h.le_re_saddle
    rw [hre]
    linarith
  have hmain := norm_logDeriv_xi_sub_xiSlope_base_le (b := s₀ + (κ : ℂ)) (w := w) (κ := 0)
    (h := modelRadius T₀ κ a₀.re) (m := ‖s₀ + (κ : ℂ)‖ / 4) (by linarith) (by linarith) le_rfl
    (by linarith) him (by linarith) (by linarith)
  rw [← h.base.ha] at hmain
  refine ⟨by linarith, hmain.trans ?_⟩
  rw [modelSlopeError, ← h.base.norm_base]
  have e1 : 4 / (‖s₀ + (κ : ℂ)‖ / 4) = 16 / ‖s₀ + (κ : ℂ)‖ := by
    rw [div_div_eq_mul_div]
    norm_num
  have e2 : ‖w - (s₀ + (κ : ℂ))‖ / (2 * (‖s₀ + (κ : ℂ)‖ / 4)) ≤
      2 * modelRadius T₀ κ a₀.re / ‖s₀ + (κ : ℂ)‖ := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have := mul_le_mul_of_nonneg_right hball (by linarith : (0 : ℝ) ≤ ‖s₀ + (κ : ℂ)‖)
    linarith
  have e3 : (2 : ℝ) ^ (5 - w.re) ≤ Real.exp (1 - t₀ * (a₀.re - 1) / 2) :=
    two_rpow_le_exp h1 (by linarith)
  rw [add_div, e1]
  linarith

/-- **The saddle value against its exponential model.** If the slope error over the distance of
the two saddle points is at most `ε₁ ≤ 1`, the saddle value at `(τ, s)` is the saddle value at
`(τ₀, s₀)` times `e^{a₀ (s − s₀) + a₀² (τ − τ₀)}` up to the relative error `5ε₁`. -/
theorem norm_saddle_sub_model_le (h : SlopePair t₀ T₀ κ τ₀ s₀ a₀ τ s a) {ε₁ : ℝ}
    (hε₁ : ε₁ ≤ 1)
    (hη : modelSlopeError t₀ T₀ κ a₀.re * (2 * modelRadius T₀ κ a₀.re) ≤ ε₁) :
    ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) -
        xi (s₀ + 2 * τ₀ * a₀) * cexp (-(τ₀ * a₀ ^ 2)) *
          cexp (a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀))‖ ≤
      5 * ε₁ * ‖xi (s₀ + 2 * τ₀ * a₀) * cexp (-(τ₀ * a₀ ^ 2)) *
          cexp (a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀))‖ := by
  have hB := h.le_norm_base
  have hD6 := h.six_le_radius
  have hD4 := h.four_mul_le_radius
  have hT0 := h.base.T₀_pos
  have hBpos : 0 < ‖s₀ + (κ : ℂ)‖ := by linarith
  -- the slope error
  have hfirst : 0 < (16 + 2 * modelRadius T₀ κ a₀.re) / ‖s₀ + (κ : ℂ)‖ :=
    div_pos (by linarith) hBpos
  have hηge : (16 + 2 * modelRadius T₀ κ a₀.re) / ‖s₀ + (κ : ℂ)‖ ≤
      modelSlopeError t₀ T₀ κ a₀.re := by
    rw [modelSlopeError, ← h.base.norm_base]
    have := Real.exp_pos (1 - t₀ * (a₀.re - 1) / 2)
    linarith
  have hηpos : 0 < modelSlopeError t₀ T₀ κ a₀.re := hfirst.trans_le hηge
  have hε₁0 : 0 ≤ ε₁ := (mul_nonneg hηpos.le (by linarith)).trans hη
  -- `32 D ≤ ε₁ ‖s₀ + κ‖`
  have h32 : 32 * modelRadius T₀ κ a₀.re ≤ ε₁ * ‖s₀ + (κ : ℂ)‖ := by
    have h1 : (16 + 2 * modelRadius T₀ κ a₀.re) / ‖s₀ + (κ : ℂ)‖ *
        (2 * modelRadius T₀ κ a₀.re) ≤ ε₁ :=
      (mul_le_mul_of_nonneg_right hηge (by linarith)).trans hη
    rw [div_mul_eq_mul_div, div_le_iff₀ hBpos] at h1
    have h2 : 0 ≤ modelRadius T₀ κ a₀.re * modelRadius T₀ κ a₀.re :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = s₀ + 2 * τ₀ * a₀ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℂ, q = s + 2 * τ * a := ⟨_, rfl⟩
  have hcmp := norm_xi_sub_mul_exp_le (p := s₀ + 2 * τ₀ * a₀) (q := s + 2 * τ * a) (a := a₀)
    hηpos (fun w hw => h.norm_logDeriv_xi_sub_le hw)
  have hdist := h.norm_saddle_sub_le
  rw [← hp, ← hq] at hcmp hdist ⊢
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = -(τ * (a - a₀) ^ 2) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ, G = a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀) - τ₀ * a₀ ^ 2 -
      (q - p) * a₀ := ⟨_, rfl⟩
  -- the exponents
  have hE1 : cexp (-(τ * a ^ 2)) = cexp G * cexp u := by
    rw [← Complex.exp_add]
    congr 1
    rw [hG, hu, hq, hp]
    ring
  have hE2 : cexp (-(τ₀ * a₀ ^ 2)) * cexp (a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀)) =
      cexp G * cexp ((q - p) * a₀) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hG]
    ring
  have key : xi q * cexp (-(τ * a ^ 2)) -
      xi p * cexp (-(τ₀ * a₀ ^ 2)) * cexp (a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀)) =
      cexp G * ((xi q - xi p * cexp ((q - p) * a₀)) * cexp u +
        xi p * cexp ((q - p) * a₀) * (cexp u - 1)) := by
    rw [mul_assoc (xi p), hE2, hE1]
    ring
  have hMod : xi p * cexp (-(τ₀ * a₀ ^ 2)) * cexp (a₀ * (s - s₀) + a₀ ^ 2 * (τ - τ₀)) =
      cexp G * (xi p * cexp ((q - p) * a₀)) := by
    rw [mul_assoc (xi p), hE2]
    ring
  rw [key, hMod, norm_mul, norm_mul (cexp G)]
  obtain ⟨X, hX⟩ : ∃ X : ℂ, X = xi p * cexp ((q - p) * a₀) := ⟨_, rfl⟩
  have hXn : ‖X‖ = ‖xi p‖ * Real.exp (((q - p) * a₀).re) := by
    rw [hX, norm_mul, Complex.norm_exp]
  rw [← hX] at hcmp ⊢
  rw [← hXn] at hcmp
  -- the comparison of the two values of `ξ`
  have hΛ : modelSlopeError t₀ T₀ κ a₀.re * ‖q - p‖ ≤ ε₁ :=
    (mul_le_mul_of_nonneg_left hdist hηpos.le).trans hη
  have hΛ0 : 0 ≤ modelSlopeError t₀ T₀ κ a₀.re * ‖q - p‖ :=
    mul_nonneg hηpos.le (norm_nonneg _)
  have hexp1 : Real.exp (modelSlopeError t₀ T₀ κ a₀.re * ‖q - p‖) - 1 ≤ 2 * ε₁ := by
    have h1 := Real.abs_exp_sub_one_le
      (x := modelSlopeError t₀ T₀ κ a₀.re * ‖q - p‖) (by rw [abs_of_nonneg hΛ0]; linarith)
    rw [abs_of_nonneg hΛ0] at h1
    have h2 := le_abs_self (Real.exp (modelSlopeError t₀ T₀ κ a₀.re * ‖q - p‖) - 1)
    linarith
  have hdiff : ‖xi q - X‖ ≤ ‖X‖ * (2 * ε₁) :=
    hcmp.trans (mul_le_mul_of_nonneg_left hexp1 (norm_nonneg _))
  -- the correction `e^{−τ (a − a₀)²}`
  have hun : ‖u‖ ≤ ε₁ / 2 := by
    rw [hu, norm_neg, norm_mul, norm_pow]
    have h1 := h.norm_slope_sub_le
    have h2 : ‖a - a₀‖ ^ 2 ≤ (2 / ‖s₀ + (κ : ℂ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ‖τ‖ * ‖a - a₀‖ ^ 2 ≤ T₀ * (2 / ‖s₀ + (κ : ℂ)‖) ^ 2 :=
      mul_le_mul h.pt.hτT h2 (sq_nonneg _) hT0.le
    refine h3.trans ?_
    rw [div_pow, mul_div_assoc', div_le_iff₀ (pow_pos hBpos 2)]
    have h4 : ε₁ * ‖s₀ + (κ : ℂ)‖ * 1 ≤ ε₁ * ‖s₀ + (κ : ℂ)‖ * ‖s₀ + (κ : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hε₁0 hBpos.le)
    have e : ε₁ / 2 * ‖s₀ + (κ : ℂ)‖ ^ 2 = ε₁ * ‖s₀ + (κ : ℂ)‖ * ‖s₀ + (κ : ℂ)‖ / 2 := by ring
    rw [e]
    linarith
  have hcu : ‖cexp u - 1‖ ≤ ε₁ := by
    have h1 := Complex.norm_exp_sub_one_le (x := u) (by linarith)
    linarith
  have hcu2 : ‖cexp u‖ ≤ 2 := by
    have e : cexp u = (cexp u - 1) + 1 := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one]
    linarith
  have hsum : ‖(xi q - X) * cexp u + X * (cexp u - 1)‖ ≤ 5 * ε₁ * ‖X‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖xi q - X‖ * ‖cexp u‖ ≤ ‖X‖ * (2 * ε₁) * 2 :=
      mul_le_mul hdiff hcu2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (by linarith))
    have h2 : ‖X‖ * ‖cexp u - 1‖ ≤ ‖X‖ * ε₁ := mul_le_mul_of_nonneg_left hcu (norm_nonneg _)
    linarith
  calc ‖cexp G‖ * ‖(xi q - X) * cexp u + X * (cexp u - 1)‖
      ≤ ‖cexp G‖ * (5 * ε₁ * ‖X‖) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 5 * ε₁ * (‖cexp G‖ * ‖X‖) := by ring

end SlopePair

/-! ## The size of the error -/

/-- The error of the model is of size `(1 + α)² (e^{−2α} + e^{−t₀α/2})`. -/
theorem modelSlopeError_mul_le {t₀ T₀ κ α : ℝ} (hT₀ : 0 < T₀) (hκ : 5 ≤ κ) (hα : 0 ≤ α) :
    modelSlopeError t₀ T₀ κ α * (2 * modelRadius T₀ κ α) ≤
      2 * (1 + κ + 4 * T₀) ^ 2 * (1 + α) ^ 2 * Real.exp (-(2 * α)) +
        Real.exp (1 + t₀ / 2) * (1 + κ + 4 * T₀) * (1 + α) ^ 2 * Real.exp (-(t₀ / 2 * α)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + κ + 4 * T₀ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 1 + α := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = modelRadius T₀ κ α := ⟨_, rfl⟩
  rw [modelSlopeError, ← hD, ← hK, ← hN]
  have hK6 : 6 ≤ K := by rw [hK]; linarith
  have hN1 : 1 ≤ N := by rw [hN]; linarith
  have hTα : 0 ≤ T₀ * α := mul_nonneg hT₀.le hα
  have hD0 : 0 ≤ D := by
    rw [hD, modelRadius]
    linarith
  have hKN : 6 ≤ K * N := by nlinarith
  have hDle : D ≤ K * N := by
    rw [hD, modelRadius, hK, hN]
    have h1 : 0 ≤ (1 + κ + 2 * T₀) * α := mul_nonneg (by linarith) hα
    linarith
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hE0 := Real.exp_pos (2 * α)
  have hpi := Real.pi_gt_three
  -- the first term
  have hnum : (16 + 2 * D) * (2 * D) ≤ 10 * K ^ 2 * N ^ 2 := by
    have h1 : 16 + 2 * D ≤ 5 * (K * N) := by linarith
    have h2 : 2 * D ≤ 2 * (K * N) := by linarith
    have h3 := mul_le_mul h1 h2 (by linarith) (by linarith)
    have e : 5 * (K * N) * (2 * (K * N)) = 10 * K ^ 2 * N ^ 2 := by ring
    linarith
  have hfirst : (16 + 2 * D) / (2 * Real.pi * Real.exp (2 * α)) * (2 * D) ≤
      2 * K ^ 2 * N ^ 2 * Real.exp (-(2 * α)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), Real.exp_neg]
    have h1 : 2 * K ^ 2 * N ^ 2 * (Real.exp (2 * α))⁻¹ * (2 * Real.pi * Real.exp (2 * α)) =
        4 * Real.pi * (K ^ 2 * N ^ 2) := by
      field_simp
      ring
    rw [h1]
    have h2 : 0 ≤ K ^ 2 * N ^ 2 := by positivity
    have h3 : 12 * (K ^ 2 * N ^ 2) ≤ 4 * Real.pi * (K ^ 2 * N ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    linarith
  -- the second term
  have hexp : Real.exp (1 - t₀ * (α - 1) / 2) =
      Real.exp (1 + t₀ / 2) * Real.exp (-(t₀ / 2 * α)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp (1 - t₀ * (α - 1) / 2) / 12 * (2 * D) ≤
      Real.exp (1 + t₀ / 2) * K * N ^ 2 * Real.exp (-(t₀ / 2 * α)) := by
    rw [hexp]
    have hc0 : 0 ≤ Real.exp (1 + t₀ / 2) * Real.exp (-(t₀ / 2 * α)) :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have h1 : 2 * D / 12 ≤ K * N ^ 2 := by
      have : K * N ≤ K * N ^ 2 := mul_le_mul_of_nonneg_left hN2 (by linarith)
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hc0
    have e1 : Real.exp (1 + t₀ / 2) * Real.exp (-(t₀ / 2 * α)) / 12 * (2 * D) =
        Real.exp (1 + t₀ / 2) * Real.exp (-(t₀ / 2 * α)) * (2 * D / 12) := by ring
    have e2 : Real.exp (1 + t₀ / 2) * K * N ^ 2 * Real.exp (-(t₀ / 2 * α)) =
        Real.exp (1 + t₀ / 2) * Real.exp (-(t₀ / 2 * α)) * (K * N ^ 2) := by ring
    rw [e1, e2]
    exact h2
  rw [add_mul]
  exact add_le_add hfirst hsecond

/-! ## The exponential model -/

/-- The local exponential model of the saddle value at `(τ₀, s₀)`: rate `a₀` in the point and
`a₀²` in the time, `a₀` the slope at the base point `s₀ + κ`. -/
def saddleModel (κ : ℝ) (τ₀ s₀ τ s : ℂ) : ℂ :=
  saddleValue κ τ₀ s₀ *
    cexp (saddleSlope κ s₀ * (s - s₀) + saddleSlope κ s₀ ^ 2 * (τ - τ₀))

theorem saddleModel_self (κ : ℝ) (τ₀ s₀ : ℂ) : saddleModel κ τ₀ s₀ τ₀ s₀ = saddleValue κ τ₀ s₀ := by
  rw [saddleModel, sub_self, sub_self, mul_zero, mul_zero, add_zero, Complex.exp_zero, mul_one]

/-- A point within distance one of a far point has a slope within one of its slope. -/
theorem saddleSlope_re_sub_one_le {κ : ℝ} {s₀ s : ℂ} (hs₀ : 2 ≤ ‖s₀ + (κ : ℂ)‖)
    (hnear : ‖s - s₀‖ ≤ 1) : (saddleSlope κ s₀).re - 1 ≤ (saddleSlope κ s).re := by
  rw [saddleSlope, saddleSlope, xiSlope_re, xiSlope_re]
  have e : s + (κ : ℂ) = (s₀ + (κ : ℂ)) - (s₀ - s) := by ring
  have h1 : ‖s₀ + (κ : ℂ)‖ / 2 ≤ ‖s + (κ : ℂ)‖ := by
    have h2 := norm_sub_norm_le (s₀ + (κ : ℂ)) (s₀ - s)
    rw [← e, norm_sub_rev s₀ s] at h2
    linarith
  have h3 := Real.log_le_log (by linarith : (0 : ℝ) < ‖s₀ + (κ : ℂ)‖ / 2) h1
  rw [Real.log_div (by linarith) two_ne_zero] at h3
  have h4 := Real.log_two_lt_d9
  linarith

/-- **The saddle value is locally an exponential.** For `τ₀, τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, points `s₀, s` within distance one whose base points lie in
`Re ≥ 11/2`, and `Re a₀ ≥ A`, the saddle value at `(τ, s)` is its exponential model at `(τ₀, s₀)`
up to the relative error `ε`. -/
theorem exists_norm_saddleValue_sub_saddleModel_le {t₀ κ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀)
    (hκ : 5 ≤ κ) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ₀ τ s₀ s : ℂ, t₀ ≤ τ₀.re → ‖τ₀‖ ≤ T₀ → t₀ ≤ τ.re → ‖τ‖ ≤ T₀ →
      11 / 2 ≤ s₀.re + κ → 11 / 2 ≤ s.re + κ → ‖s - s₀‖ ≤ 1 → A ≤ (saddleSlope κ s₀).re →
      ‖saddleValue κ τ s - saddleModel κ τ₀ s₀ τ s‖ ≤ ε * ‖saddleModel κ τ₀ s₀ τ s‖ := by
  by_cases hT : t₀ ≤ T₀
  swap
  · exact ⟨0, fun τ₀ τ s₀ s h1 h2 _ _ _ _ _ _ =>
      absurd (h1.trans ((Complex.re_le_norm τ₀).trans h2)) hT⟩
  have hT0 : 0 < T₀ := ht₀.trans_le hT
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (ε / 5) 1 := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (by positivity) one_pos
  have hε₁1 : ε₁ ≤ 1 := by
    rw [hε₁def]
    exact min_le_right _ _
  have hε₁ε : 5 * ε₁ ≤ ε := by
    have := min_le_left (ε / 5) 1
    rw [← hε₁def] at this
    linarith
  obtain ⟨A₁, -, hA₁⟩ := exists_forall_sq_mul_exp_neg_le (c := 2) two_pos (half_pos hε₁0)
    (2 * (1 + κ + 4 * T₀) ^ 2)
  obtain ⟨A₂, -, hA₂⟩ := exists_forall_sq_mul_exp_neg_le (c := t₀ / 2) (half_pos ht₀)
    (half_pos hε₁0) (Real.exp (1 + t₀ / 2) * (1 + κ + 4 * T₀))
  have hlam : 0 < 1 / gaussRate t₀ T₀ := by
    rw [gaussRate]
    positivity
  have hdiv : 0 ≤ (2 * T₀ + κ) / t₀ := div_nonneg (by linarith) ht₀.le
  refine ⟨max (farThreshold t₀ T₀ κ + 1) (max (κ + 4 * T₀) (max (1 + 1 / t₀) (max A₁ A₂))),
    fun τ₀ τ s₀ s hτ₀t hτ₀T hτt hτT hs₀ hs hnear hA => ?_⟩
  have hfar := (le_max_left _ _).trans hA
  have hA' := (le_max_right _ _).trans hA
  have hK := (le_max_left _ _).trans hA'
  have hA'' := (le_max_right _ _).trans hA'
  have hone := (le_max_left _ _).trans hA''
  have hA''' := (le_max_right _ _).trans hA''
  have hα1 := (le_max_left _ _).trans hA'''
  have hα2 := (le_max_right _ _).trans hA'''
  rw [farThreshold, slopeThreshold] at hfar
  have hα0 : 0 ≤ (saddleSlope κ s₀).re := by linarith
  -- the configuration at `(τ₀, s₀)`
  have h₀ : SlopeConfig t₀ T₀ κ τ₀ s₀ (saddleSlope κ s₀) :=
    ⟨ht₀, hτ₀t, hτ₀T, hκ, hs₀, rfl, by rw [slopeThreshold]; linarith⟩
  have hfar₀ : 2 * T₀ + κ ≤ t₀ * (saddleSlope κ s₀).re := by
    have h1 : (2 * T₀ + κ) / t₀ ≤ (saddleSlope κ s₀).re := by linarith
    rw [div_le_iff₀ ht₀] at h1
    linarith
  have hnb := h₀.norm_base
  have hexp := one_add_sq_le_exp_two_mul hα0
  have hpi := Real.pi_gt_three
  have hE1 : 1 ≤ Real.exp (2 * (saddleSlope κ s₀).re) := Real.one_le_exp (by linarith)
  have hpiE : 3 * Real.exp (2 * (saddleSlope κ s₀).re) ≤
      Real.pi * Real.exp (2 * (saddleSlope κ s₀).re) :=
    mul_le_mul_of_nonneg_right hpi.le (by linarith)
  -- the configuration at `(τ, s)`
  have hslope := saddleSlope_re_sub_one_le (κ := κ) (s₀ := s₀) (s := s)
    (by rw [hnb]; linarith) hnear
  have h : SlopeConfig t₀ T₀ κ τ s (saddleSlope κ s) :=
    ⟨ht₀, hτt, hτT, hκ, hs, rfl, by rw [slopeThreshold]; linarith⟩
  have hfar' : 2 * T₀ + κ ≤ t₀ * (saddleSlope κ s).re := by
    have h1 : (2 * T₀ + κ) / t₀ ≤ (saddleSlope κ s).re := by linarith
    rw [div_le_iff₀ ht₀] at h1
    linarith
  -- the disc around the base point
  have hrad : modelRadius T₀ κ (saddleSlope κ s₀).re ≤ ‖s₀ + (κ : ℂ)‖ / 4 := by
    rw [hnb, modelRadius]
    have h1 : (1 + κ + 4 * T₀) * (1 + (saddleSlope κ s₀).re) ≤
        (1 + (saddleSlope κ s₀).re) * (1 + (saddleSlope κ s₀).re) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : 0 ≤ (1 + κ + 2 * T₀) * (saddleSlope κ s₀).re := mul_nonneg (by linarith) hα0
    have e : (1 + (saddleSlope κ s₀).re) * (1 + (saddleSlope κ s₀).re) =
        (1 + (saddleSlope κ s₀).re) ^ 2 := by ring
    linarith
  have hone' : 1 ≤ t₀ * ((saddleSlope κ s₀).re - 1) := by
    have h1 : 1 / t₀ ≤ (saddleSlope κ s₀).re - 1 := by linarith
    rw [div_le_iff₀ ht₀] at h1
    linarith
  have hpair : SlopePair t₀ T₀ κ τ₀ s₀ (saddleSlope κ s₀) τ s (saddleSlope κ s) :=
    ⟨h₀, hfar₀, h, hfar', hnear, hrad, hone'⟩
  have hη : modelSlopeError t₀ T₀ κ (saddleSlope κ s₀).re *
      (2 * modelRadius T₀ κ (saddleSlope κ s₀).re) ≤ ε₁ := by
    have h1 := modelSlopeError_mul_le (t₀ := t₀) hT0 hκ hα0
    have h2 := hA₁ _ hα1
    have h3 := hA₂ _ hα2
    linarith
  have hmain := hpair.norm_saddle_sub_model_le hε₁1 hη
  exact (show ‖saddleValue κ τ s - saddleModel κ τ₀ s₀ τ s‖ ≤
      5 * ε₁ * ‖saddleModel κ τ₀ s₀ τ s‖ from hmain).trans
    (mul_le_mul_of_nonneg_right hε₁ε (norm_nonneg _))

/-- **The half transform is locally an exponential.** For `τ₀, τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, `z₀, z` with imaginary parts at most `Y`, `‖z − z₀‖ ≤ 1` and
`‖z₀‖ ≥ R`, the half transform `𝒜(τ, z)` is `M₀ e^{i a₀ (z − z₀) + a₀² (τ − τ₀)}` up to the
relative error `ε`, with `M₀ ≠ 0` the saddle value and `a₀` the slope at `(τ₀, z₀)`. -/
theorem exists_norm_halfHeat_sub_saddleModel_le {t₀ Y ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀)
    (hY : 0 ≤ Y) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ₀ τ z₀ z : ℂ, t₀ ≤ τ₀.re → ‖τ₀‖ ≤ T₀ → t₀ ≤ τ.re → ‖τ‖ ≤ T₀ →
      z₀.im ≤ Y → z.im ≤ Y → R ≤ ‖z₀‖ → ‖z - z₀‖ ≤ 1 →
      saddleValue (Y + 5) τ₀ (1 / 2 + I * z₀) ≠ 0 ∧
        ‖halfHeat τ z - saddleModel (Y + 5) τ₀ (1 / 2 + I * z₀) τ (1 / 2 + I * z)‖ ≤
          ε * ‖saddleModel (Y + 5) τ₀ (1 / 2 + I * z₀) τ (1 / 2 + I * z)‖ := by
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (ε / 3) 1 := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (by positivity) one_pos
  have hε₁1 : ε₁ ≤ 1 := by
    rw [hε₁def]
    exact min_le_right _ _
  have hε₁ε : 3 * ε₁ ≤ ε := by
    have := min_le_left (ε / 3) 1
    rw [← hε₁def] at this
    linarith
  obtain ⟨R₁, hR₁⟩ := exists_halfHeat_sub_saddleValue_le T₀ ht₀ hY hε₁0
  obtain ⟨A, hA⟩ := exists_norm_saddleValue_sub_saddleModel_le (κ := Y + 5) T₀ ht₀
    (by linarith) hε₁0
  refine ⟨max (R₁ + 1) (2 * Real.pi * Real.exp (2 * A) + (Y + 11 / 2)),
    fun τ₀ τ z₀ z hτ₀t hτ₀T hτt hτT hz₀ hz hR hnear => ?_⟩
  have hR1 := (le_max_left _ _).trans hR
  have hR2 := (le_max_right _ _).trans hR
  have hzn : R₁ ≤ ‖z‖ := by
    have h1 := norm_sub_norm_le z₀ z
    rw [norm_sub_rev] at h1
    linarith
  have hre : ∀ w : ℂ, (1 / 2 + I * w : ℂ).re = 1 / 2 - w.im := fun w => by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have hs₀ : 11 / 2 ≤ (1 / 2 + I * z₀ : ℂ).re + (Y + 5) := by
    rw [hre]
    linarith
  have hs : 11 / 2 ≤ (1 / 2 + I * z : ℂ).re + (Y + 5) := by
    rw [hre]
    linarith
  have hb : 2 * Real.pi * Real.exp (2 * A) ≤ ‖(1 / 2 + I * z₀ : ℂ) + ((Y + 5 : ℝ) : ℂ)‖ := by
    have e : (1 / 2 + I * z₀ : ℂ) + ((Y + 5 : ℝ) : ℂ) = I * z₀ - (-((Y + 11 / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    have h1 := norm_sub_norm_le (I * z₀) (-((Y + 11 / 2 : ℝ) : ℂ))
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)] at h1
    rw [e]
    linarith
  have hsn : ‖(1 / 2 + I * z : ℂ) - (1 / 2 + I * z₀)‖ ≤ 1 := by
    have e : (1 / 2 + I * z : ℂ) - (1 / 2 + I * z₀) = I * (z - z₀) := by ring
    rw [e, norm_mul, Complex.norm_I, one_mul]
    exact hnear
  obtain ⟨hne, -⟩ := hR₁ τ₀ z₀ hτ₀t hτ₀T hz₀ (by linarith)
  obtain ⟨-, h1⟩ := hR₁ τ z hτt hτT hz hzn
  have h2 := hA τ₀ τ (1 / 2 + I * z₀) (1 / 2 + I * z) hτ₀t hτ₀T hτt hτT hs₀ hs hsn
    (le_saddleSlope_re hb)
  refine ⟨hne, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℂ, M = saddleValue (Y + 5) τ (1 / 2 + I * z) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℂ, W = saddleModel (Y + 5) τ₀ (1 / 2 + I * z₀) τ (1 / 2 + I * z) :=
    ⟨_, rfl⟩
  rw [← hM] at h1 h2
  rw [← hW] at h2 ⊢
  have hMW : ‖M‖ ≤ 2 * ‖W‖ := by
    have h3 := norm_sub_norm_le M W
    have h4 := mul_le_mul_of_nonneg_right hε₁1 (norm_nonneg W)
    linarith
  have e : halfHeat τ z - W = (halfHeat τ z - M) + (M - W) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h5 : ε₁ * ‖M‖ ≤ ε₁ * (2 * ‖W‖) := mul_le_mul_of_nonneg_left hMW hε₁0.le
  have h6 := mul_le_mul_of_nonneg_right hε₁ε (norm_nonneg W)
  linarith

end

end GaloisForLFunctions.GaloisTheoryOfZeros
