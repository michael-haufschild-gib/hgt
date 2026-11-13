import GaloisForLFunctions.GaloisTheoryOfZeros.TheHalfTransformIsXiAtTheSaddlePoint

/-!
# The reflected half transform is dominated

Below a horizontal line the heat family `H_τ(z) = 𝒜(τ, z) + 𝒜(τ, −z)` is carried by the first
half transform. Put `s = 1/2 + iz`, `a = ½ log((s + 5)/2π)` and `M = ξ(s + 2τa) e^{−τa²}`, the
saddle value of `𝒜(τ, z)`. For `τ` in the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `Im z ≤ −(12 + 21T₀)`,

`‖𝒜(τ, −z)‖ = ‖∫_0^∞ g_τ(u) ξ(1 − s + u) du‖ ≤ ε ‖M‖`  for `‖z‖` large

(`exists_norm_reflected_le`, `exists_norm_halfHeat_neg_le`). Hence `H_τ(z) = M (1 + o(1))` there
(`exists_norm_complexHeat_sub_saddleValue_le`), and the far zeros of the heat family at forward
times lie in the strip `|Im z| < 12 + 21T₀` (`exists_complexHeat_ne_zero_of_le_abs_im`).

Mechanism. The reflected half line runs from `1 − s` through the critical strip to the corner
`b' = 11/2 − i Im s`, the reflected base point, and on to the right.

* Before the corner `ξ(1 − s + u) = ξ(s − u)` is at most `ξ(s + 5) e^{4u + O(Re a)}`, and
  `ξ(s + 5)` is smaller than `M` by `e^{−Re(τa²)}`.
* Beyond the corner, for `b'` far from the origin, the ray is moved to the height of the saddle
  of `b'`. Wherever that saddle lies, ray and side are at most
  `ξ(b') e^{Re(τa'²) − κ' Re a' + O(Re a')}`, `a'` the slope at `b'`, `κ'` the corner. From
  `conj b'` to `s + 5` the function `ξ` grows at slope at least `Re a' − 1`, so this is at most
  `M e^{−(Re a')(Re s − 1/2)/2 + O(Re a')}`: small once `Re s − 1/2 ≥ 12 + 21T₀`.
* For `b'` near the origin the corner is far out and no shift is needed: the Gaussian beats the
  growth of `ξ` to the right of `b'`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Elementary facts -/

theorem norm_le_norm_of_abs_le {w w' : ℂ} (hre : |w.re| ≤ |w'.re|) (him : |w.im| ≤ |w'.im|) :
    ‖w‖ ≤ ‖w'‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.2 hre) (sq_le_sq.2 him))

/-- `log x ≤ δx − 1 − log δ`. -/
theorem log_le_mul_sub_one_sub_log {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    Real.log x ≤ δ * x - 1 - Real.log δ := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hδ hx)
  rw [Real.log_mul hδ.ne' hx.ne'] at h
  linarith

/-- `bx ≤ (a/4) x² + b²/a`. -/
theorem mul_le_quarter_sq_add_div {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    b * x ≤ a / 4 * x ^ 2 + b ^ 2 / a := by
  have hne : a ≠ 0 := ha.ne'
  have e : a / 4 * x ^ 2 + b ^ 2 / a - b * x = (a * x / 2 - b) ^ 2 / a := by
    field_simp
    ring
  have h : 0 ≤ (a * x / 2 - b) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
  linarith

theorem mul_exp_mul_mul_exp (x y A B : ℝ) :
    x * Real.exp A * (y * Real.exp B) = y * (x * Real.exp (A + B)) := by
  rw [Real.exp_add]
  ring

theorem mul_mul_exp_add (x y A B : ℝ) :
    x * (y * Real.exp (A + B)) = x * (y * Real.exp A * Real.exp B) := by
  rw [Real.exp_add]
  ring

/-- `(1 + x) e^{−x/2} ≤ 2`. -/
theorem one_add_mul_exp_neg_half_le (x : ℝ) : (1 + x) * Real.exp (-(x / 2)) ≤ 2 := by
  have h1 := Real.add_one_le_exp (x / 2)
  have h3 := Real.exp_pos (-(x / 2))
  have h2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h4 : (1 + x) * Real.exp (-(x / 2)) ≤ 2 * Real.exp (x / 2) * Real.exp (-(x / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) h3.le
  rw [mul_assoc, h2] at h4
  linarith

/-- `(u − κ)² ≤ 2(u − w₀)² + 2D²` for `0 ≤ κ ≤ u` and `w₀ ≤ D`. -/
theorem sq_sub_le_two_mul_sq_add {u κ w₀ D : ℝ} (hu : κ ≤ u) (hκ : 0 ≤ κ) (hw : w₀ ≤ D) :
    (u - κ) ^ 2 ≤ 2 * (u - w₀) ^ 2 + 2 * D ^ 2 := by
  rcases le_total w₀ κ with hd | hd
  · have h1 : (u - κ) ^ 2 ≤ (u - w₀) ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.2 hu) (by linarith) 2
    linarith [sq_nonneg (u - w₀), sq_nonneg D]
  · have h1 : (w₀ - κ) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (sub_nonneg.2 hd) (by linarith) 2
    linarith [sq_nonneg ((u - w₀) - (w₀ - κ))]

/-- `(y + 2T₀N)/(2N²) ≤ v/(2N²) + 1/4` for `y ≤ v` and `4T₀ ≤ N`. -/
theorem add_div_two_sq_le {N T₀ v y : ℝ} (hN : 0 < N) (h4T : 4 * T₀ ≤ N) (hy : y ≤ v) :
    (y + 2 * T₀ * N) / (2 * N ^ 2) ≤ v / (2 * N ^ 2) + 1 / 4 := by
  have hN2pos : 0 < 2 * N ^ 2 := by positivity
  rw [div_le_iff₀ hN2pos, add_mul, div_mul_cancel₀ _ hN2pos.ne']
  linarith [mul_nonneg hN.le (sub_nonneg.2 h4T)]

/-- The real arithmetic of the ray: with `v = u − κ` the distance from the corner and
`x = u − w₀` the distance from the centre of the Gaussian,
`(1 + v/(2N²)) (v + 2T₀N) ≤ (λ/2) x² + (9/2) T₀N + 4T₀² + 2/λ`. -/
theorem slope_mul_dist_le {lam N T₀ κ w₀ u : ℝ} (hlam : 0 < lam) (hN5 : 5 ≤ N)
    (h4T : 4 * T₀ ≤ N) (hlamN2 : 4 ≤ lam * N ^ 2) (hκ : 0 ≤ κ) (hw₀le : w₀ ≤ 2 * T₀ * N)
    (hu : κ ≤ u) :
    (1 + (u - κ) / (2 * N ^ 2)) * ((u - κ) + 2 * T₀ * N) ≤
      lam / 2 * (u - w₀) ^ 2 + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam := by
  have hN0 : 0 < N := by linarith
  have hN2pos : 0 < 2 * N ^ 2 := by positivity
  have hv0 : 0 ≤ u - κ := sub_nonneg.2 hu
  have hv2 := sq_sub_le_two_mul_sq_add hu hκ hw₀le
  have hquad : (u - κ) ^ 2 / (2 * N ^ 2) ≤ lam / 4 * (u - w₀) ^ 2 + 4 * T₀ ^ 2 := by
    rw [div_le_iff₀ hN2pos]
    linarith [mul_nonneg (sub_nonneg.2 hlamN2) (sq_nonneg (u - w₀))]
  have hlin : 5 / 4 * (u - w₀) ≤ lam / 4 * (u - w₀) ^ 2 + 2 / lam := by
    have h1 := mul_le_quarter_sq_add_div hlam (5 / 4) (u - w₀)
    have h2 : (5 / 4 : ℝ) ^ 2 / lam ≤ 2 / lam :=
      div_le_div_of_nonneg_right (by norm_num) hlam.le
    linarith
  have hcross : (u - κ) / (2 * N ^ 2) * (2 * T₀ * N) ≤ (u - κ) / 4 := by
    have h1 : 2 * T₀ * N ≤ N ^ 2 / 2 := by linarith [mul_nonneg hN0.le (sub_nonneg.2 h4T)]
    have h2 := mul_le_mul_of_nonneg_left h1 (div_nonneg hv0 hN2pos.le)
    have e : (u - κ) / (2 * N ^ 2) * (N ^ 2 / 2) = (u - κ) / 4 := by
      rw [div_mul_div_comm, div_eq_div_iff (mul_pos hN2pos two_pos).ne' (by norm_num)]
      ring
    linarith
  have e : (1 + (u - κ) / (2 * N ^ 2)) * ((u - κ) + 2 * T₀ * N) =
      (u - κ) + 2 * T₀ * N + (u - κ) ^ 2 / (2 * N ^ 2) +
        (u - κ) / (2 * N ^ 2) * (2 * T₀ * N) := by ring
  rw [e]
  linarith

/-- The real arithmetic of the reflected tail: the decay `e^{−(α' − 1)y}` between the two base
points pays for the linear terms once `y ≥ 12 + 21T₀`. -/
theorem reflected_tail_exponent_le {T₀ α α' y R mQ L : ℝ} (hT0 : 0 < T₀)
    (hα' : 4 + 4 * T₀ ≤ α') (hαα : α ≤ α' + y / 11) (hy : 12 + 21 * T₀ ≤ y)
    (hQR : mQ - R ≤ 2 * T₀ * α' + 2 * T₀ * α + T₀) :
    (-R + (5 + 2 * T₀) * α + (5 + 2 * T₀)) + -(α' - 1) * y +
        (mQ + 9 / 2 * T₀ * (1 + α') + 4 * T₀ ^ 2 + L) ≤
      (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + L) + -α' := by
  have hy0 : 0 ≤ y := by linarith
  have p1 : α' / 2 ≤ α' - 1 - (5 + 4 * T₀) / 11 := by linarith
  have p2 := mul_le_mul_of_nonneg_left p1 hy0
  have p3 : (12 + 21 * T₀) * (α' / 2) ≤ y * (α' / 2) :=
    mul_le_mul_of_nonneg_right hy (by linarith)
  have p4 : (5 + 4 * T₀) * α ≤ (5 + 4 * T₀) * (α' + y / 11) :=
    mul_le_mul_of_nonneg_left hαα (by linarith)
  linarith

/-- Assembly of the reflected tail from its three comparisons. -/
theorem reflected_tail_assembly {n b m g S P A E C x : ℝ} (hn : n ≤ b * (g * S * Real.exp E))
    (hb : b ≤ m * Real.exp A) (hm : 0 ≤ m) (hg : 0 ≤ g) (hS : 0 ≤ S)
    (hexp : A + E ≤ C + -x) (hpre : S * Real.exp (-(x / 2)) ≤ P) :
    n ≤ m * (g * P * Real.exp C * Real.exp (-(x / 2))) := by
  have hgS : 0 ≤ g * S := mul_nonneg hg hS
  have hsplit : Real.exp (C + -x) =
      Real.exp C * Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc n ≤ b * (g * S * Real.exp E) := hn
    _ ≤ m * Real.exp A * (g * S * Real.exp E) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg hgS (Real.exp_pos _).le)
    _ = m * (g * S * Real.exp (A + E)) := by
        rw [Real.exp_add A E]
        ring
    _ ≤ m * (g * S * Real.exp (C + -x)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hgS) hm
    _ = m * (g * Real.exp C * Real.exp (-(x / 2)) * (S * Real.exp (-(x / 2)))) := by
        rw [hsplit]
        ring
    _ ≤ m * (g * Real.exp C * Real.exp (-(x / 2)) * P) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpre
            (mul_nonneg (mul_nonneg hg (Real.exp_pos _).le) (Real.exp_pos _).le)) hm
    _ = _ := by ring

/-- At the height of the saddle `2τa = w₀ + ic` the exponent of the Gaussian is
`Re((U + ic)²/(4τ)) = Re(τa²) + (U − w₀) Re a + (Re τ/(4‖τ‖²)) (U − w₀)²`. -/
theorem re_sq_div_of_saddle {τ a : ℂ} (hτ : 0 < τ.re) {w₀ c : ℝ}
    (hsad : 2 * τ * a = w₀ + c * I) (U : ℝ) :
    (((U : ℂ) + c * I) ^ 2 / (4 * τ)).re =
      (τ * a ^ 2).re + (U - w₀) * a.re + τ.re / (4 * ‖τ‖ ^ 2) * (U - w₀) ^ 2 := by
  have hτ0 := ne_zero_of_re_pos hτ
  have e0 : (U : ℂ) + c * I = ((U - w₀ : ℝ) : ℂ) + 2 * τ * a := by
    rw [hsad]
    push_cast
    ring
  have e : ((U : ℂ) + c * I) ^ 2 / (4 * τ) =
      ((U - w₀ : ℝ) : ℂ) ^ 2 / (4 * τ) + ((U - w₀ : ℝ) : ℂ) * a + τ * a ^ 2 := by
    rw [e0]
    field_simp
    ring
  rw [e, Complex.add_re, Complex.add_re, re_ofReal_sq_div hτ, Complex.re_ofReal_mul]
  ring

/-- `Re(2τa · a) = 2 Re(τa²)` in the coordinates `2τa = w₀ + ic`. -/
theorem re_saddle_mul {τ a : ℂ} {w₀ c : ℝ} (hsad : 2 * τ * a = w₀ + c * I) :
    w₀ * a.re - c * a.im = 2 * (τ * a ^ 2).re := by
  have e : ((2 : ℝ) : ℂ) * (τ * a ^ 2) = ((w₀ : ℂ) + c * I) * a := by
    rw [← hsad]
    push_cast
    ring
  have h := congrArg Complex.re e
  rw [Complex.re_ofReal_mul] at h
  rw [h]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- **The exponent of the Gaussian is concave along a vertical segment from the real axis.** -/
theorem re_sq_div_concave_of_real {τ : ℂ} (hτ : 0 < τ.re) (x c θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) * ((x : ℂ) ^ 2 / (4 * τ)).re + θ * (((x : ℂ) + (c : ℂ) * I) ^ 2 / (4 * τ)).re ≤
      (((x : ℂ) + ((θ * c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re := by
  have hn : 0 < ‖τ‖ := norm_pos_iff.2 (ne_zero_of_re_pos hτ)
  rw [re_sq_div_four_mul hτ, re_sq_div_four_mul hτ, re_sq_div_four_mul hτ]
  have e1 : ((x : ℂ) + (c : ℂ) * I).re = x := by simp
  have e2 : ((x : ℂ) + (c : ℂ) * I).im = c := by simp
  have e3 : ((x : ℂ) + ((θ * c : ℝ) : ℂ) * I).re = x := by simp
  have e4 : ((x : ℂ) + ((θ * c : ℝ) : ℂ) * I).im = θ * c := by simp
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_im, ← sub_nonneg]
  have key : ((x ^ 2 - (θ * c) ^ 2) * τ.re + 2 * x * (θ * c) * τ.im) / (4 * ‖τ‖ ^ 2) -
      ((1 - θ) * (((x ^ 2 - 0 ^ 2) * τ.re + 2 * x * 0 * τ.im) / (4 * ‖τ‖ ^ 2)) +
        θ * (((x ^ 2 - c ^ 2) * τ.re + 2 * x * c * τ.im) / (4 * ‖τ‖ ^ 2))) =
      τ.re * c ^ 2 * θ * (1 - θ) / (4 * ‖τ‖ ^ 2) := by
    field_simp
    ring
  rw [key]
  have h1 : 0 ≤ 1 - θ := by linarith
  have h2 : 0 ≤ τ.re * c ^ 2 * θ * (1 - θ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hτ.le (sq_nonneg c)) hθ0) h1
  exact div_nonneg h2 (by positivity)

/-! ## Ray and side against the base point -/

namespace SlopeConfig

variable {t₀ T₀ κ : ℝ} {τ s a : ℂ}

/-- `Re(τa²) ≤ Re τ (Re a)² + 2T₀ Re a`. -/
theorem re_mul_sq_le (h : SlopeConfig t₀ T₀ κ τ s a) :
    (τ * a ^ 2).re ≤ τ.re * a.re ^ 2 + 2 * T₀ * a.re := by
  rw [re_mul_sq]
  have hα0 : 0 ≤ a.re := by linarith [h.four_le_re]
  have h2 : 0 ≤ τ.re * a.im ^ 2 := mul_nonneg h.τ_re_pos.le (sq_nonneg _)
  have h4 : -T₀ * a.re ≤ τ.im * a.im * a.re :=
    mul_le_mul_of_nonneg_right (abs_le.1 h.abs_im_mul_im_le).1 hα0
  linarith

/-- `Re(τa²) ≥ Re τ (Re a)² − 2T₀ Re a − T₀`. -/
theorem re_mul_sq_ge (h : SlopeConfig t₀ T₀ κ τ s a) :
    τ.re * a.re ^ 2 - 2 * T₀ * a.re - T₀ ≤ (τ * a ^ 2).re := by
  rw [re_mul_sq]
  have hα0 : 0 ≤ a.re := by linarith [h.four_le_re]
  have hφ2 : a.im ^ 2 ≤ 1 := by
    have h1 := h.abs_im_le
    rw [← sq_abs]
    nlinarith [abs_nonneg a.im]
  have hτre : τ.re ≤ T₀ := (Complex.re_le_norm τ).trans h.hτT
  have h2 : τ.re * a.im ^ 2 ≤ T₀ * 1 := mul_le_mul hτre hφ2 (sq_nonneg _) h.T₀_pos.le
  have h4 : τ.im * a.im * a.re ≤ T₀ * a.re :=
    mul_le_mul_of_nonneg_right (abs_le.1 h.abs_im_mul_im_le).2 hα0
  linarith

theorem five_le_one_add (h : SlopeConfig t₀ T₀ κ τ s a) : 5 ≤ 1 + a.re := by
  linarith [h.four_le_re]

theorem four_mul_le_one_add (h : SlopeConfig t₀ T₀ κ τ s a) : 4 * T₀ ≤ 1 + a.re := by
  have h1 := h.four_le
  have h3 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 h.rate_pos
  linarith

theorem four_le_rate_mul_sq (h : SlopeConfig t₀ T₀ κ τ s a) :
    4 ≤ gaussRate t₀ T₀ * (1 + a.re) ^ 2 := by
  have hlamN := h.one_le_rate_mul
  have hN5 := h.five_le_one_add
  nlinarith [mul_nonneg (sub_nonneg.2 hlamN) (by linarith : (0 : ℝ) ≤ 1 + a.re)]

/-- **The vertical side against the base point.** On the side at the corner, up to the height of
the saddle, the integrand is at most
`κ₀ ‖ξ(s + κ)‖ e^{max(Re(τa²) − κ Re a, 0) + 2T₀(1 + Re a)}`: the exponent of the Gaussian is
concave between the two ends, and at the upper end it is `Re(τa²) − κ Re a` at most. -/
theorem norm_side_le_base (h : SlopeConfig t₀ T₀ κ τ s a) :
    ‖∫ v in (0 : ℝ)..(2 * τ * a).im, complexGauss τ (κ + v * I) * xi (s + (κ + v * I))‖ ≤
      ‖xi (s + κ)‖ * (gaussHeight t₀ * (2 * T₀ * (1 + a.re)) *
        Real.exp (max ((τ * a ^ 2).re - κ * a.re) 0 + 2 * T₀ * (1 + a.re))) := by
  set w₀ : ℝ := (2 * τ * a).re with hw₀
  set c : ℝ := (2 * τ * a).im with hc
  have hsad : 2 * τ * a = w₀ + c * I := (Complex.re_add_im _).symm
  have hτ := h.τ_re_pos
  have hα4 := h.four_le_re
  have hT0 := h.T₀_pos
  have hkap0 := gaussHeight_pos h.ht₀
  have hcle : |c| ≤ 2 * T₀ * (1 + a.re) := (Complex.abs_im_le_norm _).trans h.norm_two_mul_le
  have hTN : 0 ≤ 2 * T₀ * (1 + a.re) := (abs_nonneg _).trans hcle
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  have hQ := re_saddle_mul hsad
  have hpt : ∀ v ∈ Set.uIoc (0 : ℝ) c,
      ‖complexGauss τ (κ + v * I) * xi (s + (κ + v * I))‖ ≤
        ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp (max ((τ * a ^ 2).re - κ * a.re) 0 + 2 * T₀ * (1 + a.re))) := by
    intro v hv
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := exists_mul_of_mem_uIoc hv
    -- the slope on the vertical segment from the base point
    have hseg : ∀ w' ∈ segment ℝ (s + (κ : ℂ)) (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)),
        1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 := by
      intro w' hw'
      obtain ⟨θ', hθ'0, hθ'1, hre, him⟩ := re_im_of_mem_segment hw'
      have e3 : (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)).re = s.re + κ := by simp
      have e4 : (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)).im = s.im + θ * c := by simp
      rw [e5, e3] at hre
      rw [e6, e4] at him
      have hre1 : w'.re = (s + (κ : ℂ)).re := by
        rw [e5, hre]
        ring
      have him1 : |w'.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re) := by
        have e : w'.im - (s + (κ : ℂ)).im = θ' * θ * c := by
          rw [e6, him]
          ring
        have hθθ : θ' * θ ≤ 1 := by nlinarith [mul_nonneg hθ'0 (sub_nonneg.2 hθ1)]
        rw [e, abs_mul, abs_of_nonneg (mul_nonneg hθ'0 hθ0)]
        exact (mul_le_of_le_one_left (abs_nonneg _) hθθ).trans hcle
      refine ⟨by linarith, h.norm_logDeriv_xi_sub_le_one hre1.ge ?_ him1⟩
      rw [hre1, sub_self]
      exact hTN
    have hmain := norm_xi_le_mul_exp (p := s + (κ : ℂ))
      (q := s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)) (a := a) one_pos hseg
    have hd : s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I) - (s + (κ : ℂ)) = ((θ * c : ℝ) : ℂ) * I := by
      ring
    rw [hd] at hmain
    have hre : (((θ * c : ℝ) : ℂ) * I * a).re = -(θ * c * a.im) := by
      rw [mul_assoc, Complex.re_ofReal_mul, Complex.I_mul_re]
      ring
    have hn : ‖((θ * c : ℝ) : ℂ) * I‖ ≤ 2 * T₀ * (1 + a.re) := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hθ0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hθ1).trans hcle
    -- the Gaussian: concavity between the real point and the height of the saddle
    have hg : ‖complexGauss τ ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)‖ ≤
        gaussHeight t₀ * Real.exp (-(θ * ((τ * a ^ 2).re + (κ - w₀) * a.re))) := by
      rw [norm_complexGauss hτ]
      have hconc := re_sq_div_concave_of_real hτ κ c θ hθ0 hθ1
      have hR0 : 0 ≤ ((κ : ℂ) ^ 2 / (4 * τ)).re := by
        rw [re_ofReal_sq_div hτ]
        exact mul_nonneg (div_nonneg hτ.le (by positivity)) (sq_nonneg _)
      have hR1 : (τ * a ^ 2).re + (κ - w₀) * a.re ≤
          (((κ : ℂ) + (c : ℂ) * I) ^ 2 / (4 * τ)).re := by
        rw [re_sq_div_of_saddle hτ hsad κ]
        have : 0 ≤ τ.re / (4 * ‖τ‖ ^ 2) * (κ - w₀) ^ 2 :=
          mul_nonneg (div_nonneg hτ.le (by positivity)) (sq_nonneg _)
        linarith
      have h1 := mul_le_mul_of_nonneg_left hR1 hθ0
      have h2 := mul_nonneg (sub_nonneg.2 hθ1) hR0
      calc Real.exp (-(((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re) /
            Real.sqrt (4 * Real.pi * ‖τ‖)
          = 1 / Real.sqrt (4 * Real.pi * ‖τ‖) *
              Real.exp (-(((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I) ^ 2 / (4 * τ)).re) := by ring
        _ ≤ _ := mul_le_mul (one_div_sqrt_le_gaussHeight h.ht₀ h.hτt)
            (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le hkap0.le
    have hθQ : θ * ((τ * a ^ 2).re - κ * a.re) ≤ max ((τ * a ^ 2).re - κ * a.re) 0 := by
      rcases le_total 0 ((τ * a ^ 2).re - κ * a.re) with hq | hq
      · exact (mul_le_of_le_one_left hq hθ1).trans (le_max_left _ _)
      · exact (mul_nonpos_of_nonneg_of_nonpos hθ0 hq).trans (le_max_right _ _)
    have hexp : -(θ * ((τ * a ^ 2).re + (κ - w₀) * a.re)) +
        ((((θ * c : ℝ) : ℂ) * I * a).re + 1 * ‖((θ * c : ℝ) : ℂ) * I‖) ≤
        max ((τ * a ^ 2).re - κ * a.re) 0 + 2 * T₀ * (1 + a.re) := by
      rw [hre]
      have e : -(θ * ((τ * a ^ 2).re + (κ - w₀) * a.re)) + -(θ * c * a.im) =
          θ * ((τ * a ^ 2).re - κ * a.re) := by
        linear_combination θ * hQ
      linarith
    calc ‖complexGauss τ ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I) *
          xi (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I))‖
        = ‖complexGauss τ ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I)‖ *
            ‖xi (s + ((κ : ℂ) + ((θ * c : ℝ) : ℂ) * I))‖ := norm_mul _ _
      _ ≤ gaussHeight t₀ * Real.exp (-(θ * ((τ * a ^ 2).re + (κ - w₀) * a.re))) *
            (‖xi (s + (κ : ℂ))‖ * Real.exp ((((θ * c : ℝ) : ℂ) * I * a).re +
              1 * ‖((θ * c : ℝ) : ℂ) * I‖)) :=
          mul_le_mul hg hmain (norm_nonneg _) (mul_nonneg hkap0.le (Real.exp_pos _).le)
      _ = ‖xi (s + (κ : ℂ))‖ * (gaussHeight t₀ *
            Real.exp (-(θ * ((τ * a ^ 2).re + (κ - w₀) * a.re)) +
              ((((θ * c : ℝ) : ℂ) * I * a).re + 1 * ‖((θ * c : ℝ) : ℂ) * I‖))) :=
          mul_exp_mul_mul_exp _ _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hkap0.le) (norm_nonneg _)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine hint.trans ?_
  rw [sub_zero]
  calc ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp (max ((τ * a ^ 2).re - κ * a.re) 0 + 2 * T₀ * (1 + a.re))) * |c|
      ≤ ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp (max ((τ * a ^ 2).re - κ * a.re) 0 + 2 * T₀ * (1 + a.re))) *
          (2 * T₀ * (1 + a.re)) :=
        mul_le_mul_of_nonneg_left hcle
          (mul_nonneg (norm_nonneg _) (mul_nonneg hkap0.le (Real.exp_pos _).le))
    _ = _ := by ring

/-- **The ray against the base point.** At the height of the saddle the ray from the corner is at
most `κ₀ ‖ξ(s + κ)‖ e^{Re(τa²) − κ Re a + O(1 + Re a)} ∫ e^{−λv²/2} dv`, wherever the saddle lies:
the Gaussian is centred at `Re(2τa)`, and the slope of `ξ` is `a` up to
`1 + (u − κ)/(2(1 + Re a)²)` between the base point and the point of the ray above `u`. -/
theorem norm_ray_le_base (h : SlopeConfig t₀ T₀ κ τ s a) :
    ‖∫ u in Ioi κ, complexGauss τ (u + (2 * τ * a).im * I) *
        xi (s + (u + (2 * τ * a).im * I))‖ ≤
      ‖xi (s + κ)‖ * (gaussHeight t₀ *
        Real.exp ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * (1 + a.re) + 4 * T₀ ^ 2 +
          2 / gaussRate t₀ T₀) * ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 2) * v ^ 2)) := by
  set w₀ : ℝ := (2 * τ * a).re with hw₀
  set c : ℝ := (2 * τ * a).im with hc
  have hsad : 2 * τ * a = w₀ + c * I := (Complex.re_add_im _).symm
  have hτ := h.τ_re_pos
  have hT0 := h.T₀_pos
  have hκ := h.hκ
  have hkap0 := gaussHeight_pos h.ht₀
  have hnorm := h.norm_two_mul_le
  have hw₀le : w₀ ≤ 2 * T₀ * (1 + a.re) := (Complex.re_le_norm _).trans hnorm
  have hcle : |c| ≤ 2 * T₀ * (1 + a.re) := (Complex.abs_im_le_norm _).trans hnorm
  have e5 : (s + (κ : ℂ)).re = s.re + κ := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + (κ : ℂ)).im = s.im := by rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hbre := h.base_re
  have hQ := re_saddle_mul hsad
  have hN5 := h.five_le_one_add
  have h4T := h.four_mul_le_one_add
  have hlamN2 := h.four_le_rate_mul_sq
  have hq1 := gaussRate_le h.ht₀ h.hτt h.hτT
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = gaussRate t₀ T₀ := ⟨_, rfl⟩
  have hlam : 0 < lam := by
    rw [hlamdef]
    exact h.rate_pos
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 1 + a.re := ⟨_, rfl⟩
  rw [← hlamdef, ← hNdef] at hlamN2
  rw [← hNdef] at hw₀le hcle hN5 h4T
  rw [← hlamdef] at hq1
  rw [← hlamdef, ← hNdef]
  have hN0 : 0 < N := by linarith
  have hNne : N ≠ 0 := hN0.ne'
  have hN2 : 25 ≤ N ^ 2 := by nlinarith
  have hN2pos : 0 < 2 * N ^ 2 := by positivity
  have hpt : ∀ u : ℝ, κ < u →
      ‖complexGauss τ (u + c * I) * xi (s + (u + c * I))‖ ≤
        ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) *
            Real.exp (-(lam / 2) * (u - w₀) ^ 2)) := by
    intro u hu
    have hv0 : 0 < u - κ := sub_pos.2 hu
    have hη : 0 < 1 + (u - κ) / (2 * N ^ 2) :=
      add_pos_of_pos_of_nonneg one_pos (div_nonneg hv0.le hN2pos.le)
    -- the slope between the base point and the point of the ray
    have hseg : ∀ w' ∈ segment ℝ (s + (κ : ℂ)) (s + ((u : ℂ) + c * I)),
        1 < w'.re ∧ ‖logDeriv xi w' - a‖ ≤ 1 + (u - κ) / (2 * N ^ 2) := by
      intro w' hw'
      obtain ⟨θ, hθ0, hθ1, hre, him⟩ := re_im_of_mem_segment hw'
      have e3 : (s + ((u : ℂ) + c * I)).re = s.re + u := by simp
      have e4 : (s + ((u : ℂ) + c * I)).im = s.im + c := by simp
      rw [e5, e3] at hre
      rw [e6, e4] at him
      have hre0 : w'.re - (s + (κ : ℂ)).re = θ * (u - κ) := by
        rw [e5, hre]
        ring
      have hθv0 : 0 ≤ θ * (u - κ) := mul_nonneg hθ0 hv0.le
      have hθv : θ * (u - κ) ≤ u - κ := mul_le_of_le_one_left hv0.le hθ1
      have him1 : |w'.im - (s + (κ : ℂ)).im| ≤ 2 * T₀ * (1 + a.re) := by
        have e : w'.im - (s + (κ : ℂ)).im = θ * c := by
          rw [e6, him]
          ring
        rw [e, abs_mul, abs_of_nonneg hθ0, ← hNdef]
        exact (mul_le_of_le_one_left (abs_nonneg _) hθ1).trans hcle
      have hre1 : (s + (κ : ℂ)).re ≤ w'.re := by linarith
      refine ⟨by linarith, ?_⟩
      have hS := h.norm_logDeriv_xi_sub_le hre1 him1
      rw [hre0, ← hNdef] at hS
      have b1 : 4 / N ^ 2 ≤ 4 / 25 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN2
      have b2 : (2 : ℝ) ^ (5 - w'.re) / 12 ≤ 1 / 12 := by
        have : (2 : ℝ) ^ (5 - w'.re) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
        linarith
      have b3 : (θ * (u - κ) + 2 * T₀ * N) / (2 * N ^ 2) ≤ (u - κ) / (2 * N ^ 2) + 1 / 4 := by
        have hnum : θ * (u - κ) + 2 * T₀ * N ≤ (u - κ) + N ^ 2 / 2 := by
          nlinarith [mul_nonneg hN0.le (sub_nonneg.2 h4T)]
        have e : ((u - κ) + N ^ 2 / 2) / (2 * N ^ 2) = (u - κ) / (2 * N ^ 2) + 1 / 4 := by
          field_simp
          ring
        rw [← e]
        exact div_le_div_of_nonneg_right hnum hN2pos.le
      linarith
    have hmain := norm_xi_le_mul_exp (p := s + (κ : ℂ)) (q := s + ((u : ℂ) + c * I)) (a := a)
      hη hseg
    have hd : s + ((u : ℂ) + c * I) - (s + (κ : ℂ)) = ((u - κ : ℝ) : ℂ) + c * I := by
      push_cast
      ring
    rw [hd] at hmain
    have hre : ((((u - κ : ℝ) : ℂ) + c * I) * a).re = (u - κ) * a.re - c * a.im := by
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hn : ‖((u - κ : ℝ) : ℂ) + c * I‖ ≤ (u - κ) + 2 * T₀ * N := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv0, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      linarith
    -- the Gaussian at the height of the saddle
    have hg : ‖complexGauss τ ((u : ℂ) + c * I)‖ ≤ gaussHeight t₀ *
        Real.exp (-((τ * a ^ 2).re + (u - w₀) * a.re + lam * (u - w₀) ^ 2)) := by
      rw [norm_complexGauss hτ, re_sq_div_of_saddle hτ hsad u]
      have q2 : lam * (u - w₀) ^ 2 ≤ τ.re / (4 * ‖τ‖ ^ 2) * (u - w₀) ^ 2 :=
        mul_le_mul_of_nonneg_right hq1 (sq_nonneg _)
      calc Real.exp (-((τ * a ^ 2).re + (u - w₀) * a.re +
              τ.re / (4 * ‖τ‖ ^ 2) * (u - w₀) ^ 2)) / Real.sqrt (4 * Real.pi * ‖τ‖)
          = 1 / Real.sqrt (4 * Real.pi * ‖τ‖) *
              Real.exp (-((τ * a ^ 2).re + (u - w₀) * a.re +
                τ.re / (4 * ‖τ‖ ^ 2) * (u - w₀) ^ 2)) := by ring
        _ ≤ _ := mul_le_mul (one_div_sqrt_le_gaussHeight h.ht₀ h.hτt)
            (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le hkap0.le
    -- the exponents
    have hvx : u - κ ≤ (u - w₀) + 2 * T₀ * N := by linarith
    have hv2 : (u - κ) ^ 2 ≤ 2 * (u - w₀) ^ 2 + 8 * T₀ ^ 2 * N ^ 2 := by
      have hT2 : 0 ≤ 8 * T₀ ^ 2 * N ^ 2 := by positivity
      rcases le_total w₀ κ with hd0 | hd0
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (u - w₀) - (u - κ))
          (by linarith : (0 : ℝ) ≤ (u - w₀) + (u - κ)), sq_nonneg (u - w₀)]
      · nlinarith [sq_nonneg ((u - w₀) - (w₀ - κ)),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T₀ * N - (w₀ - κ))
            (by linarith : (0 : ℝ) ≤ 2 * T₀ * N + (w₀ - κ))]
    have hquad : (u - κ) ^ 2 / (2 * N ^ 2) ≤ lam / 4 * (u - w₀) ^ 2 + 4 * T₀ ^ 2 := by
      rw [div_le_iff₀ hN2pos]
      nlinarith [mul_nonneg (sub_nonneg.2 hlamN2) (sq_nonneg (u - w₀))]
    have hlin : 5 / 4 * (u - w₀) ≤ lam / 4 * (u - w₀) ^ 2 + 2 / lam := by
      have h1 := mul_le_quarter_sq_add_div hlam (5 / 4) (u - w₀)
      have h2 : (5 / 4 : ℝ) ^ 2 / lam ≤ 2 / lam :=
        div_le_div_of_nonneg_right (by norm_num) hlam.le
      linarith
    have hcross : (u - κ) / (2 * N ^ 2) * (2 * T₀ * N) ≤ (u - κ) / 4 := by
      have e : (u - κ) / (2 * N ^ 2) * (2 * T₀ * N) = (u - κ) * T₀ / N := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hN2pos.ne' hNne]
        ring
      rw [e, div_le_iff₀ hN0]
      nlinarith [mul_nonneg hv0.le (sub_nonneg.2 h4T)]
    have hηn : (1 + (u - κ) / (2 * N ^ 2)) * ‖((u - κ : ℝ) : ℂ) + c * I‖ ≤
        5 / 4 * (u - κ) + 2 * T₀ * N + (u - κ) ^ 2 / (2 * N ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hn hη.le
      have e : (1 + (u - κ) / (2 * N ^ 2)) * ((u - κ) + 2 * T₀ * N) =
          (u - κ) + 2 * T₀ * N + (u - κ) ^ 2 / (2 * N ^ 2) +
            (u - κ) / (2 * N ^ 2) * (2 * T₀ * N) := by ring
      linarith
    have hexp : -((τ * a ^ 2).re + (u - w₀) * a.re + lam * (u - w₀) ^ 2) +
        (((((u - κ : ℝ) : ℂ) + c * I) * a).re +
          (1 + (u - κ) / (2 * N ^ 2)) * ‖((u - κ : ℝ) : ℂ) + c * I‖) ≤
        ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) +
          -(lam / 2) * (u - w₀) ^ 2 := by
      rw [hre]
      linarith
    calc ‖complexGauss τ ((u : ℂ) + c * I) * xi (s + ((u : ℂ) + c * I))‖
        = ‖complexGauss τ ((u : ℂ) + c * I)‖ * ‖xi (s + ((u : ℂ) + c * I))‖ := norm_mul _ _
      _ ≤ gaussHeight t₀ *
            Real.exp (-((τ * a ^ 2).re + (u - w₀) * a.re + lam * (u - w₀) ^ 2)) *
            (‖xi (s + (κ : ℂ))‖ * Real.exp (((((u - κ : ℝ) : ℂ) + c * I) * a).re +
              (1 + (u - κ) / (2 * N ^ 2)) * ‖((u - κ : ℝ) : ℂ) + c * I‖)) :=
          mul_le_mul hg hmain (norm_nonneg _) (mul_nonneg hkap0.le (Real.exp_pos _).le)
      _ = ‖xi (s + (κ : ℂ))‖ * (gaussHeight t₀ *
            Real.exp (-((τ * a ^ 2).re + (u - w₀) * a.re + lam * (u - w₀) ^ 2) +
              (((((u - κ : ℝ) : ℂ) + c * I) * a).re +
                (1 + (u - κ) / (2 * N ^ 2)) * ‖((u - κ : ℝ) : ℂ) + c * I‖))) :=
          mul_exp_mul_mul_exp _ _ _ _
      _ ≤ ‖xi (s + (κ : ℂ))‖ * (gaussHeight t₀ *
            Real.exp (((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) +
              -(lam / 2) * (u - w₀) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hkap0.le) (norm_nonneg _)
      _ = _ := mul_mul_exp_add _ _ _ _
  -- integration over the ray
  have hI : Integrable fun u : ℝ => Real.exp (-(lam / 2) * (u - w₀) ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < lam / 2)).comp_sub_right w₀
  have hint : ∫ u : ℝ, Real.exp (-(lam / 2) * (u - w₀) ^ 2) =
      ∫ v : ℝ, Real.exp (-(lam / 2) * v ^ 2) :=
    integral_sub_right_eq_self (fun v : ℝ => Real.exp (-(lam / 2) * v ^ 2)) w₀
  have hbi : Integrable fun u : ℝ => ‖xi (s + κ)‖ * (gaussHeight t₀ *
      Real.exp ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) *
        Real.exp (-(lam / 2) * (u - w₀) ^ 2)) := (hI.const_mul _).const_mul _
  calc ‖∫ u in Ioi κ, complexGauss τ (u + c * I) * xi (s + (u + c * I))‖
      ≤ ∫ u in Ioi κ, ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) *
            Real.exp (-(lam / 2) * (u - w₀) ^ 2)) :=
        norm_integral_le_of_norm_le hbi.integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => hpt u hu))
    _ ≤ ∫ u, ‖xi (s + κ)‖ * (gaussHeight t₀ *
          Real.exp ((τ * a ^ 2).re - κ * a.re + 9 / 2 * T₀ * N + 4 * T₀ ^ 2 + 2 / lam) *
            Real.exp (-(lam / 2) * (u - w₀) ^ 2)) :=
        setIntegral_le_integral hbi (Eventually.of_forall fun u =>
          mul_nonneg (norm_nonneg _)
            (mul_nonneg (mul_nonneg hkap0.le (Real.exp_pos _).le) (Real.exp_pos _).le))
    _ = _ := by rw [integral_const_mul, integral_const_mul, hint]

end SlopeConfig

/-! ## The reflected base point -/

/-- The corner of the reflected half line, the reflected base point
`1 − s + (Re s + 9/2) = 11/2 − i Im s`. -/
def reflectedBase (s : ℂ) : ℂ := 1 - s + ((s.re + 9 / 2 : ℝ) : ℂ)

theorem reflectedBase_re (s : ℂ) : (reflectedBase s).re = 11 / 2 := by
  rw [reflectedBase, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  ring

theorem reflectedBase_im (s : ℂ) : (reflectedBase s).im = -s.im := by
  rw [reflectedBase, Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im]
  ring

/-- The conjugate of the reflected base point lies on the horizontal line through `s + 5`,
to its left by `Re s − 1/2`. -/
theorem conj_reflectedBase (s : ℂ) :
    starRingEnd ℂ (reflectedBase s) = s + ((5 : ℝ) : ℂ) - ((s.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.conj_re, reflectedBase_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_re]
    ring
  · rw [Complex.conj_im, reflectedBase_im, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.ofReal_im]
    ring

theorem le_norm_reflectedBase (s : ℂ) : 11 / 2 ≤ ‖reflectedBase s‖ := by
  have := Complex.re_le_norm (reflectedBase s)
  rwa [reflectedBase_re] at this

theorem norm_reflectedBase_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖reflectedBase s‖ ≤ ‖s + ((5 : ℝ) : ℂ)‖ := by
  refine norm_le_norm_of_abs_le ?_ ?_
  · rw [reflectedBase_re, Complex.add_re, Complex.ofReal_re, abs_of_pos (by norm_num),
      abs_of_nonneg (by linarith)]
    linarith
  · rw [reflectedBase_im, abs_neg, Complex.add_im, Complex.ofReal_im, add_zero]

theorem norm_base_le_reflectedBase {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖s + ((5 : ℝ) : ℂ)‖ ≤ ‖reflectedBase s‖ + (s.re - 1 / 2) := by
  have e : s + ((5 : ℝ) : ℂ) =
      starRingEnd ℂ (reflectedBase s) + ((s.re - 1 / 2 : ℝ) : ℂ) := by
    rw [conj_reflectedBase]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- The slope at the reflected base point is at most the slope at `s + 5`. -/
theorem xiSlope_reflectedBase_re_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (xiSlope (reflectedBase s)).re ≤ (xiSlope (s + ((5 : ℝ) : ℂ))).re := by
  rw [xiSlope_re, xiSlope_re]
  have hpos : 0 < ‖reflectedBase s‖ := lt_of_lt_of_le (by norm_num) (le_norm_reflectedBase s)
  have := Real.log_le_log hpos (norm_reflectedBase_le hs)
  linarith

/-- The slope at `s + 5` exceeds the slope at the reflected base point by `(Re s − 1/2)/11` at
most. -/
theorem xiSlope_base_re_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (xiSlope (s + ((5 : ℝ) : ℂ))).re ≤ (xiSlope (reflectedBase s)).re + (s.re - 1 / 2) / 11 := by
  rw [xiSlope_re, xiSlope_re]
  have h11 := le_norm_reflectedBase s
  have hB : 0 < ‖reflectedBase s‖ := by linarith
  have hy : 0 ≤ s.re - 1 / 2 := by linarith
  have hpos : 0 < ‖s + ((5 : ℝ) : ℂ)‖ :=
    lt_of_lt_of_le hB (norm_reflectedBase_le hs)
  have h1 := Real.log_le_log hpos (norm_base_le_reflectedBase hs)
  have h2 : Real.log (‖reflectedBase s‖ + (s.re - 1 / 2)) ≤
      Real.log ‖reflectedBase s‖ + (s.re - 1 / 2) / ‖reflectedBase s‖ := by
    have hsum : 0 < ‖reflectedBase s‖ + (s.re - 1 / 2) := by linarith
    have h3 := Real.log_le_sub_one_of_pos (div_pos hsum hB)
    rw [Real.log_div hsum.ne' hB.ne', add_div, div_self hB.ne'] at h3
    linarith
  have h3 : (s.re - 1 / 2) / ‖reflectedBase s‖ ≤ (s.re - 1 / 2) / (11 / 2) :=
    div_le_div_of_nonneg_left hy (by norm_num) h11
  have e : (s.re - 1 / 2) / (11 / 2) = 2 * ((s.re - 1 / 2) / 11) := by ring
  linarith

/-- `ξ` at the reflected base point against the base point `s + 5`: growth to the left by at
most `e^{4(Re s − 1/2)}`. -/
theorem norm_xi_reflectedBase_le_four {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖xi (reflectedBase s)‖ ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (s.re - 1 / 2)) := by
  have e : ‖xi (reflectedBase s)‖ = ‖xi (s + ((5 : ℝ) : ℂ) - ((s.re - 1 / 2 : ℝ) : ℂ))‖ := by
    rw [← conj_reflectedBase, xi_conj, Complex.norm_conj]
  rw [e]
  exact norm_xi_sub_le_mul_exp (by linarith) (by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith)

/-- `ξ` at the reflected base point against the base point `s + 5`: from the conjugate of the
reflected base point to `s + 5` the slope is at least that of the reflected base point less
one. -/
theorem norm_xi_reflectedBase_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖xi (reflectedBase s)‖ ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ *
      Real.exp (-((xiSlope (reflectedBase s)).re - 1) * (s.re - 1 / 2)) := by
  have e : ‖xi (reflectedBase s)‖ = ‖xi (s + ((5 : ℝ) : ℂ) - ((s.re - 1 / 2 : ℝ) : ℂ))‖ := by
    rw [← conj_reflectedBase, xi_conj, Complex.norm_conj]
  rw [e]
  refine norm_xi_sub_le_mul_exp_of_le (by linarith) (by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith) fun x hx => ?_
  have hwre : (s + ((5 : ℝ) : ℂ) - (x : ℂ)).re = s.re + 5 - x := by
    rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  have hwim : (s + ((5 : ℝ) : ℂ) - (x : ℂ)).im = s.im := by
    rw [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_im, add_zero, sub_zero]
  have hw5 : 11 / 2 ≤ (s + ((5 : ℝ) : ℂ) - (x : ℂ)).re := by
    rw [hwre]
    linarith [hx.2]
  have h1 := norm_logDeriv_xi_sub_xiSlope_le_one (s := s + ((5 : ℝ) : ℂ) - (x : ℂ)) (by linarith)
  have h2 : -1 ≤ (logDeriv xi (s + ((5 : ℝ) : ℂ) - (x : ℂ)) -
      xiSlope (s + ((5 : ℝ) : ℂ) - (x : ℂ))).re :=
    (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
  rw [Complex.sub_re] at h2
  have h3 : (xiSlope (reflectedBase s)).re ≤ (xiSlope (s + ((5 : ℝ) : ℂ) - (x : ℂ))).re := by
    rw [xiSlope_re, xiSlope_re]
    have hn : ‖reflectedBase s‖ ≤ ‖s + ((5 : ℝ) : ℂ) - (x : ℂ)‖ := by
      refine norm_le_norm_of_abs_le ?_ ?_
      · rw [reflectedBase_re, abs_of_pos (by norm_num), abs_of_nonneg (by linarith)]
        exact hw5
      · rw [reflectedBase_im, abs_neg, hwim]
    have hpos : 0 < ‖reflectedBase s‖ := lt_of_lt_of_le (by norm_num) (le_norm_reflectedBase s)
    have := Real.log_le_log hpos hn
    linarith
  linarith

/-! ## The reflected half line before the corner -/

namespace SlopeConfig

variable {t₀ T₀ : ℝ} {τ s a : ℂ}

/-- Before the corner, `ξ(1 − s + u) = ξ(s − u)` is at most `ξ(s + 5) e^{4(5 + u) + O(Re a)}`:
growth to the left in `Re ≥ 5`, the strip to the left of it. -/
theorem norm_xi_reflected_le {C : ℝ} (hC : 0 < C)
    (hstrip : ∀ Y σ X : ℝ, 4 ≤ Y → -Y ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤
        C * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) *
          ‖xi ((5 : ℝ) + X * I)‖)
    (h : SlopeConfig t₀ T₀ 5 τ s a) (hs : 1 / 2 ≤ s.re) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ s.re + 9 / 2) :
    ‖xi (1 - s + u)‖ ≤
      (1 + 8 * C) * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
        Real.exp (4 * (5 + u)) * ‖xi (s + ((5 : ℝ) : ℂ))‖ := by
  have hα4 := h.four_le_re
  have e0 : xi (1 - s + u) = xi (s - u) := by
    rw [← xi_one_sub (s - u)]
    congr 1
    ring
  rw [e0]
  have e5 : (s + ((5 : ℝ) : ℂ)).re = s.re + 5 := by rw [Complex.add_re, Complex.ofReal_re]
  have e6 : (s + ((5 : ℝ) : ℂ)).im = s.im := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
  have hb0 : 0 ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ := norm_nonneg _
  have hlog : 0 ≤ Real.log (35 / 2) := Real.log_nonneg (by norm_num)
  have hD0 : 0 ≤ 13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5) := by linarith
  have hexp1 : 1 ≤ Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) :=
    Real.one_le_exp hD0
  have hfac : 1 ≤ (1 + 8 * C) * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) :=
    one_le_mul_of_one_le_of_one_le (by linarith) hexp1
  rcases le_or_gt 5 (s.re - u) with hσ | hσ
  · -- growth to the left from the base point
    have hg := norm_xi_sub_le_mul_exp (s := s + ((5 : ℝ) : ℂ)) (v := 5 + u) (by linarith)
      (by rw [e5]; linarith)
    have e : s + ((5 : ℝ) : ℂ) - ((5 + u : ℝ) : ℂ) = s - u := by
      push_cast
      ring
    rw [e] at hg
    calc ‖xi (s - (u : ℂ))‖ ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (5 + u)) := hg
      _ = 1 * Real.exp (4 * (5 + u)) * ‖xi (s + ((5 : ℝ) : ℂ))‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le) hb0
  · -- the strip, then growth to the left from the base point
    have hsu : s - (u : ℂ) = ((s.re - u : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        ring
      · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re]
        ring
    have h1 := hstrip (9 / 2) (s.re - u) s.im (by norm_num) (by linarith) hσ.le
    rw [← hsu] at h1
    have hg := norm_xi_sub_le_mul_exp (s := s + ((5 : ℝ) : ℂ)) (v := s.re) (by linarith)
      (by rw [e5]; linarith)
    have e : s + ((5 : ℝ) : ℂ) - ((s.re : ℝ) : ℂ) = ((5 : ℝ) : ℂ) + (s.im : ℂ) * I := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        ring
      · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re]
        ring
    rw [e] at hg
    have hg' : ‖xi (((5 : ℝ) : ℂ) + (s.im : ℂ) * I)‖ ≤
        ‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (5 + u)) :=
      hg.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hb0)
    -- the height against `Re a`
    have hE1 : 1 ≤ Real.exp (2 * a.re) := Real.one_le_exp (by linarith)
    have hXn : |s.im| ≤ 2 * Real.pi * Real.exp (2 * a.re) := by
      have h2 := Complex.abs_im_le_norm (s + ((5 : ℝ) : ℂ))
      rw [e6, h.norm_base] at h2
      exact h2
    have hpi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have hpiE := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * a.re)).le
    have hX1 : 1 + |s.im| ≤ 8 * Real.exp (2 * a.re) := by linarith
    have hX2 : |s.im| + 9 / 2 + 6 ≤ 35 / 2 * Real.exp (2 * a.re) := by linarith
    have habs := abs_nonneg s.im
    have hlogle : Real.log (|s.im| + 9 / 2 + 6) ≤ 2 * a.re + Real.log (35 / 2) := by
      have h2 := Real.log_le_log (by linarith) hX2
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
      linarith
    have hstr : C * (1 + |s.im|) * Real.exp (9 / 2 * (Real.log (|s.im| + 9 / 2 + 6) / 2 + 5)) ≤
        8 * C * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) := by
      have k1 : Real.exp (9 / 2 * (Real.log (|s.im| + 9 / 2 + 6) / 2 + 5)) ≤
          Real.exp (9 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) :=
        Real.exp_le_exp.2 (by linarith)
      have k2 : Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) =
          Real.exp (2 * a.re) * Real.exp (9 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [k2]
      calc C * (1 + |s.im|) * Real.exp (9 / 2 * (Real.log (|s.im| + 9 / 2 + 6) / 2 + 5))
          ≤ C * (8 * Real.exp (2 * a.re)) *
              Real.exp (9 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hX1 hC.le) k1 (Real.exp_pos _).le
              (mul_nonneg hC.le (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        _ = _ := by ring
    calc ‖xi (s - (u : ℂ))‖
        ≤ C * (1 + |s.im|) * Real.exp (9 / 2 * (Real.log (|s.im| + 9 / 2 + 6) / 2 + 5)) *
            ‖xi (((5 : ℝ) : ℂ) + (s.im : ℂ) * I)‖ := h1
      _ ≤ 8 * C * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
            (‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (5 + u))) :=
          mul_le_mul hstr hg' (norm_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hC.le) (Real.exp_pos _).le)
      _ ≤ (1 + 8 * C) * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
            (‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (5 + u))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
            (mul_nonneg hb0 (Real.exp_pos _).le)
      _ = _ := by ring

/-- **The reflected half line before the corner is smaller than the saddle value by
`e^{−t₀ (Re a)²}`.** -/
theorem norm_reflected_unshifted_le {C : ℝ} (hC : 0 < C)
    (hstrip : ∀ Y σ X : ℝ, 4 ≤ Y → -Y ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤
        C * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) *
          ‖xi ((5 : ℝ) + X * I)‖)
    (h : SlopeConfig t₀ T₀ 5 τ s a) (hκα : 2 * T₀ + 5 ≤ t₀ * a.re) (hs : 1 / 2 ≤ s.re) :
    ‖∫ u in (0 : ℝ)..(s.re + 9 / 2), complexGauss τ u * xi (1 - s + u)‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (7 * gaussHeight t₀ * (1 + 8 * C) *
        Real.exp (-t₀ * a.re ^ 2 + (27 / 2 + 4 * T₀) * a.re +
          (25 + 16 / gaussRate t₀ T₀ + 9 / 2 * (Real.log (35 / 2) / 2 + 5) + 3 * T₀))) := by
  have hlam := h.rate_pos
  have hkap0 := gaussHeight_pos h.ht₀
  have hC8 : 0 ≤ 1 + 8 * C := by linarith
  have hk0 : 0 ≤ s.re + 9 / 2 := by linarith
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) (s.re + 9 / 2), ‖complexGauss τ u * xi (1 - s + u)‖ ≤
      gaussHeight t₀ * Real.exp (20 + 16 / gaussRate t₀ T₀) * ((1 + 8 * C) *
        Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
          ‖xi (s + ((5 : ℝ) : ℂ))‖) := by
    intro u hu
    rw [uIoc_of_le hk0] at hu
    rw [norm_mul]
    have hg := norm_complexGauss_ofReal_le h.ht₀ h.hτt h.hτT u
    have hx := h.norm_xi_reflected_le hC hstrip hs hu.1.le hu.2
    have hq := mul_le_quarter_sq_add_div hlam 4 u
    have hq' : (4 : ℝ) ^ 2 / gaussRate t₀ T₀ = 16 / gaussRate t₀ T₀ := by norm_num
    have hE : Real.exp (-gaussRate t₀ T₀ * u ^ 2) * Real.exp (4 * (5 + u)) ≤
        Real.exp (20 + 16 / gaussRate t₀ T₀) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hlam.le (sq_nonneg u)]
    calc ‖complexGauss τ u‖ * ‖xi (1 - s + u)‖
        ≤ gaussHeight t₀ * Real.exp (-gaussRate t₀ T₀ * u ^ 2) * ((1 + 8 * C) *
            Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
            Real.exp (4 * (5 + u)) * ‖xi (s + ((5 : ℝ) : ℂ))‖) :=
          mul_le_mul hg hx (norm_nonneg _) (mul_nonneg hkap0.le (Real.exp_pos _).le)
      _ = gaussHeight t₀ * (Real.exp (-gaussRate t₀ T₀ * u ^ 2) * Real.exp (4 * (5 + u))) *
            ((1 + 8 * C) * Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
              ‖xi (s + ((5 : ℝ) : ℂ))‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hkap0.le)
          (mul_nonneg (mul_nonneg hC8 (Real.exp_pos _).le) (norm_nonneg _))
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [sub_zero, abs_of_nonneg hk0] at hint
  -- the length of the piece against `Re a`
  have hlen : s.re + 9 / 2 ≤ 7 * Real.exp (2 * a.re) := by
    have h1 := Complex.re_le_norm (s + ((5 : ℝ) : ℂ))
    rw [Complex.add_re, Complex.ofReal_re, h.norm_base] at h1
    have hpi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have := mul_le_mul_of_nonneg_right hpi (Real.exp_pos (2 * a.re)).le
    linarith
  have hbase := h.norm_xi_base_le hκα
  have hM0 := norm_nonneg (xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)))
  have hE : Real.exp (-t₀ * a.re ^ 2 + (27 / 2 + 4 * T₀) * a.re +
      (25 + 16 / gaussRate t₀ T₀ + 9 / 2 * (Real.log (35 / 2) / 2 + 5) + 3 * T₀)) =
      Real.exp (20 + 16 / gaussRate t₀ T₀) *
        Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
        Real.exp (-t₀ * a.re ^ 2 + (5 + 4 * T₀) * a.re + (5 + 3 * T₀)) *
        Real.exp (2 * a.re) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  refine hint.trans ?_
  rw [hE]
  calc gaussHeight t₀ * Real.exp (20 + 16 / gaussRate t₀ T₀) * ((1 + 8 * C) *
          Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
            ‖xi (s + ((5 : ℝ) : ℂ))‖) * (s.re + 9 / 2)
      ≤ gaussHeight t₀ * Real.exp (20 + 16 / gaussRate t₀ T₀) * ((1 + 8 * C) *
          Real.exp (13 / 2 * a.re + 9 / 2 * (Real.log (35 / 2) / 2 + 5)) *
            (‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ *
              Real.exp (-t₀ * a.re ^ 2 + (5 + 4 * T₀) * a.re + (5 + 3 * T₀)))) *
          (7 * Real.exp (2 * a.re)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hbase (mul_nonneg hC8 (Real.exp_pos _).le))
            (mul_nonneg hkap0.le (Real.exp_pos _).le)) hlen hk0
          (mul_nonneg (mul_nonneg hkap0.le (Real.exp_pos _).le)
            (mul_nonneg (mul_nonneg hC8 (Real.exp_pos _).le)
              (mul_nonneg hM0 (Real.exp_pos _).le)))
    _ = _ := by ring

end SlopeConfig

/-! ## The reflected tail at bounded heights -/

/-- The rate at which `ξ` may grow to the right of a base point of modulus at most `B`, once the
logarithm of the distance is absorbed into the Gaussian. -/
def tailGrowth (t₀ T₀ B : ℝ) : ℝ :=
  (Real.log B + gaussRate t₀ T₀ - 1 - Real.log (gaussRate t₀ T₀)) / 2 + 5

/-- **The reflected tail at bounded heights.** If the reflected base point has modulus at most
`B`, the tail beyond the corner is at most `κ₀ ‖ξ(s + 5)‖ e^{(16 + G²)/λ} ∫ e^{−λv²/4} dv`,
`G` the growth rate: no shift is needed. -/
theorem norm_reflected_tail_le_of_norm_le {t₀ T₀ B : ℝ} {τ s : ℂ} (ht₀ : 0 < t₀)
    (hτt : t₀ ≤ τ.re) (hτT : ‖τ‖ ≤ T₀) (hs : 1 / 2 ≤ s.re) (hB1 : 1 ≤ B)
    (hB : ‖reflectedBase s‖ ≤ B) :
    ‖∫ u in Ioi (s.re + 9 / 2), complexGauss τ u * xi (1 - s + u)‖ ≤
      ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
        Real.exp ((16 + tailGrowth t₀ T₀ B ^ 2) / gaussRate t₀ T₀) *
          ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 4) * v ^ 2)) := by
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  have hT : 0 < T₀ := (norm_pos_iff.2 (ne_zero_of_re_pos hτ)).trans_le hτT
  have hkap0 := gaussHeight_pos ht₀
  have hbase := norm_xi_reflectedBase_le_four hs
  have hb0 : 0 ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ := norm_nonneg _
  have hnpos : 0 < ‖reflectedBase s‖ :=
    lt_of_lt_of_le (by norm_num) (le_norm_reflectedBase s)
  have hgauss : ∀ u : ℝ, ‖complexGauss τ u‖ ≤
      gaussHeight t₀ * Real.exp (-gaussRate t₀ T₀ * u ^ 2) :=
    norm_complexGauss_ofReal_le ht₀ hτt hτT
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = tailGrowth t₀ T₀ B := ⟨_, rfl⟩
  have hG : G = (Real.log B + gaussRate t₀ T₀ - 1 - Real.log (gaussRate t₀ T₀)) / 2 + 5 := by
    rw [hGdef, tailGrowth]
  rw [← hGdef]
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = gaussRate t₀ T₀ := ⟨_, rfl⟩
  have hlam : 0 < lam := by
    rw [hlamdef, gaussRate]
    positivity
  rw [← hlamdef] at hG hgauss ⊢
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = s.re + 9 / 2 := ⟨_, rfl⟩
  rw [← hkdef]
  have hk5 : 5 ≤ k := by
    rw [hkdef]
    linarith
  have hky : s.re - 1 / 2 ≤ k := by
    rw [hkdef]
    linarith
  have hpt : ∀ u : ℝ, k < u → ‖complexGauss τ u * xi (1 - s + u)‖ ≤
      ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ * Real.exp ((16 + G ^ 2) / lam) *
        Real.exp (-(lam / 4) * (u - k) ^ 2)) := by
    intro u hu
    have hv0 : 0 < u - k := sub_pos.2 hu
    have e : 1 - s + (u : ℂ) = reflectedBase s + ((u - k : ℝ) : ℂ) := by
      rw [reflectedBase, hkdef]
      push_cast
      ring
    have hgrow := norm_xi_add_le_mul_exp (s := reflectedBase s) (v := u - k)
      (by rw [reflectedBase_re]; norm_num) hv0.le
    rw [← e] at hgrow
    -- the logarithm against the Gaussian rate
    have hlog : Real.log (‖reflectedBase s‖ + (u - k)) ≤
        Real.log B + lam * (u - k) + (lam - 1 - Real.log lam) := by
      have h1 : ‖reflectedBase s‖ + (u - k) ≤ B * (1 + (u - k)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hB1) hv0.le]
      have h2 := Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by linarith) (by linarith)] at h2
      have h3 := log_le_mul_sub_one_sub_log hlam (by linarith : (0 : ℝ) < 1 + (u - k))
      linarith
    have hexp : (u - k) * (Real.log (‖reflectedBase s‖ + (u - k)) / 2 + 5) ≤
        G * (u - k) + lam / 2 * (u - k) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hlog hv0.le
      rw [hG]
      linarith
    have hq1 := mul_le_quarter_sq_add_div hlam 4 k
    have hq2 := mul_le_quarter_sq_add_div hlam G (u - k)
    have hq' : (4 : ℝ) ^ 2 / lam = 16 / lam := by norm_num
    have hsum : -lam * u ^ 2 + (4 * (s.re - 1 / 2) +
        (u - k) * (Real.log (‖reflectedBase s‖ + (u - k)) / 2 + 5)) ≤
        (16 + G ^ 2) / lam + -(lam / 4) * (u - k) ^ 2 := by
      have hu2 : k ^ 2 + (u - k) ^ 2 ≤ u ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) hv0.le]
      have h1 := mul_le_mul_of_nonneg_left hu2 hlam.le
      have h2 := mul_nonneg hlam.le (sq_nonneg k)
      rw [add_div]
      linarith
    calc ‖complexGauss τ u * xi (1 - s + u)‖
        = ‖complexGauss τ u‖ * ‖xi (1 - s + u)‖ := norm_mul _ _
      _ ≤ gaussHeight t₀ * Real.exp (-lam * u ^ 2) *
            (‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (4 * (s.re - 1 / 2)) *
              Real.exp ((u - k) * (Real.log (‖reflectedBase s‖ + (u - k)) / 2 + 5))) :=
          mul_le_mul (hgauss u)
            (hgrow.trans (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le))
            (norm_nonneg _) (mul_nonneg hkap0.le (Real.exp_pos _).le)
      _ = ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
            Real.exp (-lam * u ^ 2 + (4 * (s.re - 1 / 2) +
              (u - k) * (Real.log (‖reflectedBase s‖ + (u - k)) / 2 + 5)))) := by
          rw [mul_assoc ‖xi (s + ((5 : ℝ) : ℂ))‖, ← Real.exp_add]
          exact mul_exp_mul_mul_exp _ _ _ _
      _ ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
            Real.exp ((16 + G ^ 2) / lam + -(lam / 4) * (u - k) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsum) hkap0.le) hb0
      _ = _ := mul_mul_exp_add _ _ _ _
  have hI : Integrable fun u : ℝ => Real.exp (-(lam / 4) * (u - k) ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < lam / 4)).comp_sub_right k
  have hint : ∫ u : ℝ, Real.exp (-(lam / 4) * (u - k) ^ 2) =
      ∫ v : ℝ, Real.exp (-(lam / 4) * v ^ 2) :=
    integral_sub_right_eq_self (fun v : ℝ => Real.exp (-(lam / 4) * v ^ 2)) k
  have hbi : Integrable fun u : ℝ => ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
      Real.exp ((16 + G ^ 2) / lam) * Real.exp (-(lam / 4) * (u - k) ^ 2)) :=
    (hI.const_mul _).const_mul _
  calc ‖∫ u in Ioi k, complexGauss τ u * xi (1 - s + u)‖
      ≤ ∫ u in Ioi k, ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
          Real.exp ((16 + G ^ 2) / lam) * Real.exp (-(lam / 4) * (u - k) ^ 2)) :=
        norm_integral_le_of_norm_le hbi.integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => hpt u hu))
    _ ≤ ∫ u, ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
          Real.exp ((16 + G ^ 2) / lam) * Real.exp (-(lam / 4) * (u - k) ^ 2)) :=
        setIntegral_le_integral hbi (Eventually.of_forall fun u =>
          mul_nonneg hb0
            (mul_nonneg (mul_nonneg hkap0.le (Real.exp_pos _).le) (Real.exp_pos _).le))
    _ = _ := by rw [integral_const_mul, integral_const_mul, hint]

/-! ## The reflected tail at large heights -/

/-- **The reflected tail at large heights.** With the slope `a'` at the reflected base point
under control, the side and the ray at the height of its saddle are at most
`M e^{−Re a'/2}` up to a constant, once `Re s − 1/2 ≥ 12 + 21T₀`. -/
theorem SlopeConfig.norm_reflected_tail_le {t₀ T₀ : ℝ} {τ s a a' : ℂ}
    (h : SlopeConfig t₀ T₀ 5 τ s a) (hκα : 2 * T₀ + 5 ≤ t₀ * a.re)
    (h' : SlopeConfig t₀ T₀ (s.re + 9 / 2) τ (1 - s) a') (hs : 25 / 2 + 21 * T₀ ≤ s.re) :
    ‖I * (∫ v in (0 : ℝ)..(2 * τ * a').im,
          complexGauss τ (((s.re + 9 / 2 : ℝ) : ℂ) + v * I) *
            xi (1 - s + (((s.re + 9 / 2 : ℝ) : ℂ) + v * I))) +
        ∫ u in Ioi (s.re + 9 / 2), complexGauss τ (u + (2 * τ * a').im * I) *
          xi (1 - s + (u + (2 * τ * a').im * I))‖ ≤
      ‖xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2))‖ * (2 * gaussHeight t₀ *
        (2 * T₀ + ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 2) * v ^ 2)) *
        Real.exp (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) *
        Real.exp (-(a'.re / 2))) := by
  have hT0 := h.T₀_pos
  have hlam := h.rate_pos
  have hkap0 := gaussHeight_pos h.ht₀
  have hτ := h.τ_re_pos
  have hs' : 1 / 2 ≤ s.re := by linarith
  have ha' : a' = xiSlope (reflectedBase s) := h'.ha
  have hside := h'.norm_side_le_base
  have hray := h'.norm_ray_le_base
  have hb' : ‖xi (1 - s + ((s.re + 9 / 2 : ℝ) : ℂ))‖ ≤
      ‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (-(a'.re - 1) * (s.re - 1 / 2)) := by
    have := norm_xi_reflectedBase_le hs'
    rw [← ha'] at this
    exact this
  have hbase := h.norm_xi_base_le_of_re hκα
  have hαα' : a'.re ≤ a.re := by
    rw [ha', h.ha]
    exact xiSlope_reflectedBase_re_le hs'
  have hα'α : a.re ≤ a'.re + (s.re - 1 / 2) / 11 := by
    rw [ha', h.ha]
    exact xiSlope_base_re_le hs'
  have hα'4 := h'.four_le_re
  have hα'thr := h'.four_le
  have hup := h'.re_mul_sq_le
  have hlow := h.re_mul_sq_ge
  have hl0 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 hlam
  have hsq : τ.re * a'.re ^ 2 ≤ τ.re * a.re ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
  have hI0 : 0 ≤ ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 2) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  obtain ⟨I₂, hI₂⟩ : ∃ I₂ : ℝ, I₂ = ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 2) * v ^ 2) :=
    ⟨_, rfl⟩
  rw [← hI₂] at hI0 hray ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (τ * a' ^ 2).re - (s.re + 9 / 2) * a'.re := ⟨_, rfl⟩
  rw [← hQ] at hside hray
  have hmax : max Q 0 ≤ τ.re * a'.re ^ 2 + 2 * T₀ * a'.re := by
    have h1 : 0 ≤ (s.re + 9 / 2) * a'.re := mul_nonneg (by linarith) (by linarith)
    have h2 := mul_nonneg hτ.le (sq_nonneg a'.re)
    have h3 := mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ a'.re)
    refine max_le ?_ (by linarith)
    rw [hQ]
    linarith
  obtain ⟨M, hM⟩ : ∃ M : ℂ, M = xi (s + 2 * τ * a) * cexp (-(τ * a ^ 2)) := ⟨_, rfl⟩
  rw [← hM] at hbase ⊢
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ‖xi (1 - s + ((s.re + 9 / 2 : ℝ) : ℂ))‖ := ⟨_, rfl⟩
  rw [← hb] at hside hray hb'
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact norm_nonneg _
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = max Q 0 + 9 / 2 * T₀ * (1 + a'.re) + 4 * T₀ ^ 2 +
      2 / gaussRate t₀ T₀ := ⟨_, rfl⟩
  have hTN : 0 ≤ T₀ * (1 + a'.re) := mul_nonneg hT0.le (by linarith)
  have hE1 : max Q 0 + 2 * T₀ * (1 + a'.re) ≤ E := by
    rw [hE]
    have := sq_nonneg T₀
    have : 2 / gaussRate t₀ T₀ = 2 * (1 / gaussRate t₀ T₀) := by ring
    linarith
  have hE2 : Q + 9 / 2 * T₀ * (1 + a'.re) + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀ ≤ E := by
    rw [hE]
    linarith [le_max_left Q 0]
  -- side and ray against the reflected base point
  have hside' : ‖∫ v in (0 : ℝ)..(2 * τ * a').im,
      complexGauss τ (((s.re + 9 / 2 : ℝ) : ℂ) + v * I) *
        xi (1 - s + (((s.re + 9 / 2 : ℝ) : ℂ) + v * I))‖ ≤
      b * (gaussHeight t₀ * (2 * T₀ * (1 + a'.re)) * Real.exp E) :=
    hside.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE1)
        (mul_nonneg hkap0.le (by linarith))) hb0)
  have hray' : ‖∫ u in Ioi (s.re + 9 / 2), complexGauss τ (u + (2 * τ * a').im * I) *
      xi (1 - s + (u + (2 * τ * a').im * I))‖ ≤ b * (gaussHeight t₀ * Real.exp E * I₂) :=
    hray.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hE2) hkap0.le) hI0) hb0)
  have hsum : ‖I * (∫ v in (0 : ℝ)..(2 * τ * a').im,
        complexGauss τ (((s.re + 9 / 2 : ℝ) : ℂ) + v * I) *
          xi (1 - s + (((s.re + 9 / 2 : ℝ) : ℂ) + v * I))) +
      ∫ u in Ioi (s.re + 9 / 2), complexGauss τ (u + (2 * τ * a').im * I) *
        xi (1 - s + (u + (2 * τ * a').im * I))‖ ≤
      b * (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) * Real.exp E) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    linarith
  -- the reflected base point against the saddle value
  have hbM : b ≤ ‖M‖ * Real.exp ((-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) +
      -(a'.re - 1) * (s.re - 1 / 2)) := by
    calc b ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ * Real.exp (-(a'.re - 1) * (s.re - 1 / 2)) := hb'
      _ ≤ ‖M‖ * Real.exp (-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) *
            Real.exp (-(a'.re - 1) * (s.re - 1 / 2)) :=
          mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]
  -- the exponents
  have hexp : ((-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) +
      -(a'.re - 1) * (s.re - 1 / 2)) + E ≤
      (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) + -a'.re := by
    rw [hE]
    have hy0 : 0 ≤ s.re - 1 / 2 := by linarith
    have p1 : a'.re / 2 ≤ a'.re - 1 - (5 + 4 * T₀) / 11 := by linarith
    have p2 := mul_le_mul_of_nonneg_left p1 hy0
    have p3 : (12 + 21 * T₀) * (a'.re / 2) ≤ (s.re - 1 / 2) * (a'.re / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have p4 : (5 + 4 * T₀) * a.re ≤ (5 + 4 * T₀) * (a'.re + (s.re - 1 / 2) / 11) :=
      mul_le_mul_of_nonneg_left hα'α (by linarith)
    linarith
  have hN'exp : (1 + a'.re) * Real.exp (-(a'.re / 2)) ≤ 2 := by
    have h1 := Real.add_one_le_exp (a'.re / 2)
    have h2 : Real.exp (a'.re / 2) * Real.exp (-(a'.re / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := Real.exp_pos (-(a'.re / 2))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp (a'.re / 2) - (1 + a'.re)) h3.le]
  have hsplit : Real.exp ((5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) + -a'.re) =
      Real.exp (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) *
        Real.exp (-(a'.re / 2)) * Real.exp (-(a'.re / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpre : (2 * T₀ * (1 + a'.re) + I₂) * Real.exp (-(a'.re / 2)) ≤ 2 * (2 * T₀ + I₂) := by
    have h1 : 2 * T₀ * (1 + a'.re) + I₂ ≤ (2 * T₀ + I₂) * (1 + a'.re) := by
      nlinarith [mul_nonneg hI0 (by linarith : (0 : ℝ) ≤ a'.re)]
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(a'.re / 2))).le
    have h3 := mul_le_mul_of_nonneg_left hN'exp (by linarith : (0 : ℝ) ≤ 2 * T₀ + I₂)
    linarith
  have hC0 := Real.exp_pos (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀)
  have he0 := Real.exp_pos (-(a'.re / 2))
  calc ‖I * (∫ v in (0 : ℝ)..(2 * τ * a').im,
          complexGauss τ (((s.re + 9 / 2 : ℝ) : ℂ) + v * I) *
            xi (1 - s + (((s.re + 9 / 2 : ℝ) : ℂ) + v * I))) +
        ∫ u in Ioi (s.re + 9 / 2), complexGauss τ (u + (2 * τ * a').im * I) *
          xi (1 - s + (u + (2 * τ * a').im * I))‖
      ≤ b * (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) * Real.exp E) := hsum
    _ ≤ ‖M‖ * Real.exp ((-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) +
          -(a'.re - 1) * (s.re - 1 / 2)) *
          (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) * Real.exp E) :=
        mul_le_mul_of_nonneg_right hbM
          (mul_nonneg (mul_nonneg hkap0.le (by linarith)) (Real.exp_pos _).le)
    _ = ‖M‖ * (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) *
          Real.exp (((-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) +
            -(a'.re - 1) * (s.re - 1 / 2)) + E)) := by
        rw [mul_comm ‖M‖ (Real.exp _)]
        rw [mul_comm ‖M‖ (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) * Real.exp _)]
        rw [Real.exp_add ((-(τ * a ^ 2).re + (5 + 2 * T₀) * a.re + (5 + 2 * T₀)) +
          -(a'.re - 1) * (s.re - 1 / 2)) E]
        ring
    _ ≤ ‖M‖ * (gaussHeight t₀ * (2 * T₀ * (1 + a'.re) + I₂) *
          Real.exp ((5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) + -a'.re)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp)
            (mul_nonneg hkap0.le (by linarith))) (norm_nonneg _)
    _ = ‖M‖ * (gaussHeight t₀ *
          Real.exp (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) *
          Real.exp (-(a'.re / 2)) *
          ((2 * T₀ * (1 + a'.re) + I₂) * Real.exp (-(a'.re / 2)))) := by
        rw [hsplit]
        ring
    _ ≤ ‖M‖ * (gaussHeight t₀ *
          Real.exp (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) *
          Real.exp (-(a'.re / 2)) * (2 * (2 * T₀ + I₂))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpre
            (mul_nonneg (mul_nonneg hkap0.le hC0.le) he0.le)) (norm_nonneg _)
    _ = _ := by ring

/-! ## The reflected half line -/

/-- **The reflected half line is dominated by the saddle value.** For `τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `Re s ≥ 25/2 + 21T₀`, the integral `∫_0^∞ g_τ(u) ξ(1 − s + u) du`
is at most `ε` times the saddle value of `∫_0^∞ g_τ(u) ξ(s + u) du`, once the slope at `s + 5`
is large. -/
theorem exists_norm_reflected_le {t₀ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ τ s : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → 25 / 2 + 21 * T₀ ≤ s.re →
      A ≤ (saddleSlope 5 s).re →
      ‖∫ u in Ioi (0 : ℝ), complexGauss τ u * xi (1 - s + u)‖ ≤ ε * ‖saddleValue 5 τ s‖ := by
  by_cases hT : t₀ ≤ T₀
  swap
  · exact ⟨0, fun τ s h1 h2 _ _ => absurd (h1.trans ((Complex.re_le_norm τ).trans h2)) hT⟩
  have hT0 : 0 < T₀ := ht₀.trans_le hT
  obtain ⟨C, hC, hstrip⟩ := exists_norm_xi_le_strip
  have hlam : 0 < gaussRate t₀ T₀ := by
    rw [gaussRate]
    positivity
  have hkap0 := gaussHeight_pos ht₀
  obtain ⟨I₂, hI₂⟩ : ∃ I₂ : ℝ, I₂ = ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 2) * v ^ 2) :=
    ⟨_, rfl⟩
  have hI₂0 : 0 ≤ I₂ := by
    rw [hI₂]
    exact integral_nonneg fun v => (Real.exp_pos _).le
  obtain ⟨I₄, hI₄⟩ : ∃ I₄ : ℝ, I₄ = ∫ v : ℝ, Real.exp (-(gaussRate t₀ T₀ / 4) * v ^ 2) :=
    ⟨_, rfl⟩
  have hI₄0 : 0 ≤ I₄ := by
    rw [hI₄]
    exact integral_nonneg fun v => (Real.exp_pos _).le
  -- large heights of the reflected base point
  obtain ⟨KA, hKA⟩ : ∃ KA : ℝ, KA = 2 * gaussHeight t₀ * (2 * T₀ + I₂) *
      Real.exp (5 + 15 / 2 * T₀ + 4 * T₀ ^ 2 + 2 / gaussRate t₀ T₀) := ⟨_, rfl⟩
  have hKA0 : 0 < KA := by
    rw [hKA]
    exact mul_pos (mul_pos (mul_pos two_pos hkap0) (by linarith)) (Real.exp_pos _)
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ,
      A₀ = max (slopeThreshold t₀ T₀) (2 * Real.log (3 * KA / ε)) := ⟨_, rfl⟩
  have hA₀thr : slopeThreshold t₀ T₀ ≤ A₀ := by
    rw [hA₀]
    exact le_max_left _ _
  have hA₀log : 2 * Real.log (3 * KA / ε) ≤ A₀ := by
    rw [hA₀]
    exact le_max_right _ _
  have hl0 : 0 < 1 / gaussRate t₀ T₀ := one_div_pos.2 hlam
  have hA₀0 : 0 ≤ A₀ := by
    rw [slopeThreshold] at hA₀thr
    linarith
  -- bounded heights of the reflected base point
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = 2 * Real.pi * Real.exp (2 * A₀) := ⟨_, rfl⟩
  have hB₀1 : 1 ≤ B₀ := by
    have h1 : 1 ≤ Real.exp (2 * A₀) := Real.one_le_exp (by linarith)
    have h2 := Real.pi_gt_three
    rw [hB₀]
    nlinarith
  obtain ⟨KB, hKB⟩ : ∃ KB : ℝ, KB = gaussHeight t₀ *
      Real.exp ((16 + tailGrowth t₀ T₀ B₀ ^ 2) / gaussRate t₀ T₀) * (I₄ + 1) := ⟨_, rfl⟩
  have hKB0 : 0 < KB := by
    rw [hKB]
    exact mul_pos (mul_pos hkap0 (Real.exp_pos _)) (by linarith)
  obtain ⟨AB, -, hAB⟩ := exists_forall_exp_neg_quadratic_le (a := t₀) (ε := ε / (3 * KB)) ht₀
    (div_pos hε (by linarith)) (5 + 4 * T₀) (5 + 3 * T₀)
  -- before the corner
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 7 * gaussHeight t₀ * (1 + 8 * C) := ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by
    rw [hK₁]
    exact mul_pos (mul_pos (by norm_num) hkap0) (by linarith)
  obtain ⟨A₁, -, hA₁⟩ := exists_forall_exp_neg_quadratic_le (a := t₀) (ε := ε / (3 * K₁)) ht₀
    (div_pos hε (by linarith)) (27 / 2 + 4 * T₀)
    (25 + 16 / gaussRate t₀ T₀ + 9 / 2 * (Real.log (35 / 2) / 2 + 5) + 3 * T₀)
  refine ⟨max (farThreshold t₀ T₀ 5) (max AB A₁), fun τ s hτt hτT hs hA => ?_⟩
  have hfar := (le_max_left _ _).trans hA
  rw [farThreshold, slopeThreshold] at hfar
  have hdiv : 0 ≤ (2 * T₀ + 5) / t₀ := div_nonneg (by linarith) ht₀.le
  have hκα : 2 * T₀ + 5 ≤ t₀ * (saddleSlope 5 s).re := by
    have h1 : (2 * T₀ + 5) / t₀ ≤ (saddleSlope 5 s).re := by linarith
    rw [div_le_iff₀ ht₀] at h1
    linarith
  have h : SlopeConfig t₀ T₀ 5 τ s (saddleSlope 5 s) :=
    ⟨ht₀, hτt, hτT, le_rfl, by linarith, rfl, by rw [slopeThreshold]; linarith⟩
  have hτ := h.τ_re_pos
  have hs' : 1 / 2 ≤ s.re := by linarith
  have hαB := (le_max_left _ _).trans ((le_max_right _ _).trans hA)
  have hα1 := (le_max_right _ _).trans ((le_max_right _ _).trans hA)
  have hMv : saddleValue 5 τ s =
      xi (s + 2 * τ * saddleSlope 5 s) * cexp (-(τ * saddleSlope 5 s ^ 2)) := rfl
  rw [hMv]
  obtain ⟨M, hM⟩ : ∃ M : ℂ,
      M = xi (s + 2 * τ * saddleSlope 5 s) * cexp (-(τ * saddleSlope 5 s ^ 2)) := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 ≤ ‖M‖ := norm_nonneg _
  have hεM : 0 ≤ ε * ‖M‖ := mul_nonneg hε.le hM0
  -- the piece before the corner
  have h1 : ‖∫ u in (0 : ℝ)..(s.re + 9 / 2), complexGauss τ u * xi (1 - s + u)‖ ≤
      ε / 3 * ‖M‖ := by
    have hu := h.norm_reflected_unshifted_le hC hstrip hκα hs'
    rw [← hM, ← hK₁] at hu
    refine hu.trans ?_
    rw [mul_comm (ε / 3)]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    calc K₁ * Real.exp (-t₀ * (saddleSlope 5 s).re ^ 2 +
            (27 / 2 + 4 * T₀) * (saddleSlope 5 s).re +
            (25 + 16 / gaussRate t₀ T₀ + 9 / 2 * (Real.log (35 / 2) / 2 + 5) + 3 * T₀))
        ≤ K₁ * (ε / (3 * K₁)) := mul_le_mul_of_nonneg_left (hA₁ _ hα1) hK₁0.le
      _ = ε / 3 := by
          rw [← mul_div_assoc, mul_comm K₁ ε, mul_div_mul_right _ _ hK₁0.ne']
  by_cases hα' : A₀ ≤ (xiSlope (reflectedBase s)).re
  · -- the reflected base point is far: shift to the height of its saddle
    have h' : SlopeConfig t₀ T₀ (s.re + 9 / 2) τ (1 - s) (xiSlope (reflectedBase s)) :=
      ⟨ht₀, hτt, hτT, by linarith, by rw [Complex.sub_re, Complex.one_re]; linarith, rfl,
        hA₀thr.trans hα'⟩
    have htail := h.norm_reflected_tail_le hκα h' hs
    rw [← hM, ← hI₂, ← hKA] at htail
    have hexp : Real.exp (-((xiSlope (reflectedBase s)).re / 2)) ≤ ε / (3 * KA) := by
      have hpos : 0 < 3 * KA / ε := div_pos (by linarith) hε
      have h2 : Real.exp (-((xiSlope (reflectedBase s)).re / 2)) ≤
          Real.exp (-Real.log (3 * KA / ε)) := Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_neg, Real.exp_log hpos, inv_div] at h2
      exact h2
    have h2 : ‖I * (∫ v in (0 : ℝ)..(2 * τ * xiSlope (reflectedBase s)).im,
          complexGauss τ (((s.re + 9 / 2 : ℝ) : ℂ) + v * I) *
            xi (1 - s + (((s.re + 9 / 2 : ℝ) : ℂ) + v * I))) +
        ∫ u in Ioi (s.re + 9 / 2),
          complexGauss τ (u + (2 * τ * xiSlope (reflectedBase s)).im * I) *
            xi (1 - s + (u + (2 * τ * xiSlope (reflectedBase s)).im * I))‖ ≤ ε / 3 * ‖M‖ := by
      refine htail.trans ?_
      rw [mul_comm (ε / 3)]
      refine mul_le_mul_of_nonneg_left ?_ hM0
      calc KA * Real.exp (-((xiSlope (reflectedBase s)).re / 2))
          ≤ KA * (ε / (3 * KA)) := mul_le_mul_of_nonneg_left hexp hKA0.le
        _ = ε / 3 := by
            rw [← mul_div_assoc, mul_comm KA ε, mul_div_mul_right _ _ hKA0.ne']
    rw [integral_Ioi_zero_complexGauss_mul_xi_eq_corner hτ (1 - s) (s.re + 9 / 2)
      (2 * τ * xiSlope (reflectedBase s)).im, add_assoc]
    refine (norm_add_le _ _).trans ?_
    linarith
  · -- the reflected base point is near the origin: no shift
    have hα'lt : (xiSlope (reflectedBase s)).re < A₀ := lt_of_not_ge hα'
    have hBle : ‖reflectedBase s‖ ≤ B₀ := by
      have hpos : 0 < ‖reflectedBase s‖ :=
        lt_of_lt_of_le (by norm_num) (le_norm_reflectedBase s)
      rw [xiSlope_re] at hα'lt
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      have h3 : Real.log ‖reflectedBase s‖ ≤ Real.log (2 * Real.pi * Real.exp (2 * A₀)) := by
        rw [Real.log_mul h2pi.ne' (Real.exp_pos _).ne', Real.log_exp]
        linarith
      rw [hB₀]
      exact (Real.log_le_log_iff hpos (mul_pos h2pi (Real.exp_pos _))).1 h3
    have htail := norm_reflected_tail_le_of_norm_le ht₀ hτt hτT hs' hB₀1 hBle
    rw [← hI₄] at htail
    have hbase := h.norm_xi_base_le hκα
    rw [← hM] at hbase
    have hfi : Integrable fun u : ℝ => complexGauss τ u * xi (1 - s + u) := by
      have := integrable_complexGauss_mul_xi_line hτ (1 - s) 0
      simpa using this
    have h2 : ‖∫ u in Ioi (s.re + 9 / 2), complexGauss τ u * xi (1 - s + u)‖ ≤
        ε / 3 * ‖M‖ := by
      have hKle : gaussHeight t₀ *
          Real.exp ((16 + tailGrowth t₀ T₀ B₀ ^ 2) / gaussRate t₀ T₀) * I₄ ≤ KB := by
        rw [hKB]
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg hkap0.le (Real.exp_pos _).le)
      calc ‖∫ u in Ioi (s.re + 9 / 2), complexGauss τ u * xi (1 - s + u)‖
          ≤ ‖xi (s + ((5 : ℝ) : ℂ))‖ * (gaussHeight t₀ *
              Real.exp ((16 + tailGrowth t₀ T₀ B₀ ^ 2) / gaussRate t₀ T₀) * I₄) := htail
        _ ≤ ‖M‖ * Real.exp (-t₀ * (saddleSlope 5 s).re ^ 2 +
              (5 + 4 * T₀) * (saddleSlope 5 s).re + (5 + 3 * T₀)) * KB :=
            mul_le_mul hbase hKle
              (mul_nonneg (mul_nonneg hkap0.le (Real.exp_pos _).le) hI₄0)
              (mul_nonneg hM0 (Real.exp_pos _).le)
        _ = ‖M‖ * (KB * Real.exp (-t₀ * (saddleSlope 5 s).re ^ 2 +
              (5 + 4 * T₀) * (saddleSlope 5 s).re + (5 + 3 * T₀))) := by ring
        _ ≤ ‖M‖ * (KB * (ε / (3 * KB))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hAB _ hαB) hKB0.le) hM0
        _ = ε / 3 * ‖M‖ := by
            rw [← mul_div_assoc, mul_comm KB ε, mul_div_mul_right _ _ hKB0.ne', mul_comm]
    rw [← intervalIntegral.integral_interval_add_Ioi (a := 0) (b := s.re + 9 / 2)
      hfi.integrableOn hfi.integrableOn]
    refine (norm_add_le _ _).trans ?_
    linarith

/-- **The reflected half transform is dominated.** For `τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `z` with `Im z ≤ −(12 + 21T₀)`, `‖z‖ ≥ R`, the half transform
`𝒜(τ, −z)` is at most `ε` times the saddle value of `𝒜(τ, z)`. -/
theorem exists_norm_halfHeat_neg_le {t₀ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → z.im ≤ -(12 + 21 * T₀) → R ≤ ‖z‖ →
      ‖halfHeat τ (-z)‖ ≤ ε * ‖saddleValue 5 τ (1 / 2 + I * z)‖ := by
  obtain ⟨A, hA⟩ := exists_norm_reflected_le T₀ ht₀ hε
  refine ⟨2 * Real.pi * Real.exp (2 * A) + 11 / 2, fun τ z hτt hτT hz hR => ?_⟩
  have hre : (1 / 2 + I * z : ℂ).re = 1 / 2 - z.im := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have hs : 25 / 2 + 21 * T₀ ≤ (1 / 2 + I * z : ℂ).re := by
    rw [hre]
    linarith
  have hb : 2 * Real.pi * Real.exp (2 * A) ≤ ‖(1 / 2 + I * z : ℂ) + ((5 : ℝ) : ℂ)‖ := by
    have e : (1 / 2 + I * z : ℂ) + ((5 : ℝ) : ℂ) = I * z - (-((11 / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    have h1 := norm_sub_norm_le (I * z) (-((11 / 2 : ℝ) : ℂ))
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num)] at h1
    rw [e]
    linarith
  have e : halfHeat τ (-z) =
      ∫ u in Ioi (0 : ℝ), complexGauss τ u * xi (1 - (1 / 2 + I * z) + u) := by
    rw [halfHeat]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    show complexGauss τ u * xi (1 / 2 + I * -z + u) =
      complexGauss τ u * xi (1 - (1 / 2 + I * z) + u)
    congr 2
    ring
  rw [e]
  exact hA τ (1 / 2 + I * z) hτt hτT hs (le_saddleSlope_re hb)

/-- **Below the strip the heat family is `ξ` at the saddle point.** For `τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and `z` with `Im z ≤ −(12 + 21T₀)`, `‖z‖ ≥ R`, the heat family `H_τ(z)`
is the saddle value `ξ(1/2 + iz + 2τa) e^{−τa²}`, `a = ½ log((11/2 + iz)/2π)`, up to the relative
error `ε`; the saddle value does not vanish. -/
theorem exists_norm_complexHeat_sub_saddleValue_le {t₀ ε : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → z.im ≤ -(12 + 21 * T₀) → R ≤ ‖z‖ →
      saddleValue 5 τ (1 / 2 + I * z) ≠ 0 ∧
        ‖complexHeat τ z - saddleValue 5 τ (1 / 2 + I * z)‖ ≤
          ε * ‖saddleValue 5 τ (1 / 2 + I * z)‖ := by
  obtain ⟨R₁, hR₁⟩ := exists_halfHeat_sub_saddleValue_le (Y := 0) T₀ ht₀ le_rfl (half_pos hε)
  obtain ⟨R₂, hR₂⟩ := exists_norm_halfHeat_neg_le T₀ ht₀ (half_pos hε)
  refine ⟨max R₁ R₂, fun τ z hτt hτT hz hR => ?_⟩
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  have hT0 : 0 < T₀ := hτ.trans_le ((Complex.re_le_norm τ).trans hτT)
  obtain ⟨h0, h1⟩ := hR₁ τ z hτt hτT (by linarith) ((le_max_left _ _).trans hR)
  rw [zero_add] at h0 h1
  have h2 := hR₂ τ z hτt hτT hz ((le_max_right _ _).trans hR)
  refine ⟨h0, ?_⟩
  rw [complexHeat_eq_halfHeat_add hτ z, add_sub_right_comm]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **Far zeros at forward times lie in a horizontal strip.** For `τ` in the box
`{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` the heat family `H_τ` has no zero `z` with `|Im z| ≥ 12 + 21T₀` and
`‖z‖ ≥ R`. -/
theorem exists_complexHeat_ne_zero_of_le_abs_im {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ R : ℝ, ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → 12 + 21 * T₀ ≤ |z.im| → R ≤ ‖z‖ →
      complexHeat τ z ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_norm_complexHeat_sub_saddleValue_le (ε := 1 / 2) T₀ ht₀ (by norm_num)
  have key : ∀ τ z : ℂ, t₀ ≤ τ.re → ‖τ‖ ≤ T₀ → z.im ≤ -(12 + 21 * T₀) → R ≤ ‖z‖ →
      complexHeat τ z ≠ 0 := by
    intro τ z hτt hτT hz hRz hH
    obtain ⟨h0, h1⟩ := hR τ z hτt hτT hz hRz
    rw [hH, zero_sub, norm_neg] at h1
    have := norm_pos_iff.2 h0
    linarith
  refine ⟨R, fun τ z hτt hτT hz hRz => ?_⟩
  have hτ : 0 < τ.re := ht₀.trans_le hτt
  rcases le_total 0 z.im with h | h
  · rw [abs_of_nonneg h] at hz
    have e : complexHeat τ z = complexHeat τ (-z) := by
      rw [complexHeat_eq_halfHeat_add hτ z, complexHeat_eq_halfHeat_add hτ (-z), neg_neg,
        add_comm]
    rw [e]
    exact key τ (-z) hτt hτT (by rw [Complex.neg_im]; linarith) (by rwa [norm_neg])
  · rw [abs_of_nonpos h] at hz
    exact key τ z hτt hτT (by linarith) hRz

end

end GaloisForLFunctions.GaloisTheoryOfZeros
