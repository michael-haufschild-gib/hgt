import GaloisForLFunctions.RHTower.PrimeDeletionLogDerivativeCeiling

/-!
# Gaussian-window mean squares of the continued `L(e)`

Let `F` be the continuation of `L(e)(s) = Σ e(n) n^{-s}` to `Re s > η` (`pertLogDeriv`), for an
integer-supported perturbation `e` with `|e n| ≤ log n`.  On a line `Re s = σ` below the abscissa of
convergence the Dirichlet series diverges, but its pairings with a Gaussian window
`K(t) = e^{-(t-T)²/W²}` against `n^{it}` are still diagonal: shifting the rectangle
`[σ, 3] × [T/2, 3T/2]` to `Re s = 3`, where the series converges absolutely, gives

`∫_{T/2}^{3T/2} K(t) n^{it} F(σ+it) dt = √π W e(n) n^{-σ} + (Gaussian errors)`

(`norm_windowed_line_integral_sub_le`).  Linearizing `|F|² ≥ 2 Re(F B̄) - |B|²` against the head
`B = Σ_{n≤N} b_n n^{-it}` with real coefficients of either sign gives
`∫ K |F|² ≥ √π W Σ b_n² - 2ε Σ |b_n| - (off-diagonal)` (`windowed_meanSquare_ge`); the off-diagonal
Gaussians are small because distinct integers are `1/N`-separated in logarithmic scale.
-/

open Filter Topology Complex Asymptotics MeasureTheory Set Metric
open scoped Interval

namespace RHTower

noncomputable section

namespace IntegerBeurling

/-- Shifting a vertical segment integral across a rectangle costs at most the horizontal edges. -/
theorem norm_sub_intervalIntegral_vertical_le {h : ℂ → ℂ} {c d y₁ y₂ M : ℝ} (hcd : c ≤ d)
    (hh : DifferentiableOn ℂ h ([[c, d]] ×ℂ [[y₁, y₂]]))
    (hM : ∀ x ∈ uIcc c d, ‖h (x + y₁ * I)‖ ≤ M ∧ ‖h (x + y₂ * I)‖ ≤ M) :
    ‖(∫ y in y₁..y₂, h (c + y * I)) - ∫ y in y₁..y₂, h (d + y * I)‖ ≤ 2 * (d - c) * M := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h
    ((c : ℂ) + (y₁ : ℂ) * I) ((d : ℂ) + (y₂ : ℂ) * I) (by simpa using hh)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, zero_add] at hrect
  have hbot : ‖∫ x in c..d, h (x + y₁ * I)‖ ≤ M * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      (hM x (uIoc_subset_uIcc hx)).1
  have htop : ‖∫ x in c..d, h (x + y₂ * I)‖ ≤ M * |d - c| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      (hM x (uIoc_subset_uIcc hx)).2
  have hkey : (∫ y in y₁..y₂, h (c + y * I)) - ∫ y in y₁..y₂, h (d + y * I) =
      -I * ((∫ x in c..d, h (x + y₁ * I)) - ∫ x in c..d, h (x + y₂ * I)) := by
    have := hrect
    rw [smul_eq_mul, smul_eq_mul] at this
    linear_combination I * this + ((∫ y in y₁..y₂, h (c + y * I)) -
      ∫ y in y₁..y₂, h (d + y * I)) * Complex.I_sq
  rw [hkey, norm_mul, norm_neg, Complex.norm_I, one_mul, abs_of_nonneg (by linarith)] at *
  calc ‖(∫ x in c..d, h (x + y₁ * I)) - ∫ x in c..d, h (x + y₂ * I)‖
      ≤ ‖∫ x in c..d, h (x + y₁ * I)‖ + ‖∫ x in c..d, h (x + y₂ * I)‖ := norm_sub_le _ _
    _ ≤ M * (d - c) + M * (d - c) := add_le_add hbot htop
    _ = 2 * (d - c) * M := by ring

/-- The Gaussian window `exp((s - σ - iT)²/W²)`; on `Re s = σ` it is `e^{-(t-T)²/W²}`. -/
def deletionGaussWindow (σ T W : ℝ) (s : ℂ) : ℂ := cexp ((s - σ - T * I) ^ 2 / (W : ℂ) ^ 2)

theorem gaussWindow_line (σ T W t : ℝ) :
    deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) = (Real.exp (-(t - T) ^ 2 / W ^ 2) : ℂ) := by
  unfold deletionGaussWindow
  rw [Complex.ofReal_exp]
  congr 1
  have : (σ : ℂ) + (t : ℂ) * I - σ - T * I = ((t - T : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, mul_pow, Complex.I_sq]
  push_cast
  ring

theorem norm_gaussWindow (σ T W x y : ℝ) :
    ‖deletionGaussWindow σ T W ((x : ℂ) + (y : ℂ) * I)‖ = Real.exp (((x - σ) ^ 2 - (y - T) ^ 2) / W ^ 2) := by
  unfold deletionGaussWindow
  rw [Complex.norm_exp]
  congr 1
  have : (x : ℂ) + (y : ℂ) * I - σ - T * I = ((x - σ : ℝ) : ℂ) + ((y - T : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, show (W : ℂ) ^ 2 = ((W ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
  congr 1
  simp [sq]

theorem differentiable_gaussWindow (σ T W : ℝ) : Differentiable ℂ (deletionGaussWindow σ T W) := by
  unfold deletionGaussWindow
  fun_prop

/-- The Fourier transform of the shifted Gaussian window. -/
theorem integral_gaussian_window_fourier (a T u : ℝ) {W : ℝ} (hW : 0 < W) :
    ∫ y : ℝ, cexp (((a : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 + (u : ℂ) * (y : ℂ) * I) =
      ((Real.sqrt Real.pi * W : ℝ) : ℂ) *
        cexp ((u * T : ℝ) * I - ((a * u + W ^ 2 * u ^ 2 / 4 : ℝ) : ℂ)) := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  set b : ℂ := -1 / (W : ℂ) ^ 2 with hb
  set c : ℂ := (2 * T + 2 * a * I) / (W : ℂ) ^ 2 + u * I with hc
  set d : ℂ := ((a : ℂ) ^ 2 - T ^ 2 - 2 * a * T * I) / (W : ℂ) ^ 2 with hd
  have hbre : b.re < 0 := by
    have : b = ((-1 / W ^ 2 : ℝ) : ℂ) := by rw [hb]; push_cast; ring
    rw [this, Complex.ofReal_re]
    have : 0 < W ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by norm_num) this
  have hfun : (fun y : ℝ => cexp (((a : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 +
      (u : ℂ) * (y : ℂ) * I)) = fun y : ℝ => cexp (b * y ^ 2 + c * y + d) := by
    funext y
    congr 1
    rw [hb, hc, hd]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfun, integral_cexp_quadratic hbre c d]
  have hpi : (↑Real.pi / -b) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi * W : ℝ) : ℂ) := by
    have h1 : (↑Real.pi / -b) = ((Real.pi * W ^ 2 : ℝ) : ℂ) := by
      rw [hb]; push_cast; field_simp
    rw [h1, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.mul_rpow Real.pi_pos.le (by positivity), ← Real.sqrt_eq_rpow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; norm_num
  rw [hpi]
  congr 1
  congr 1
  rw [hb, hc, hd]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem natCast_cpow_eq_cexp_log {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (n : ℂ) ^ z = cexp (z * (Real.log n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, mul_comm]
  congr 2
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (Nat.cast_nonneg n)]

/-- **One Dirichlet term against the window on `Re s = 3`.** -/
theorem integral_gaussWindow_three_term (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    ∫ y : ℝ, deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹) =
      ((Real.sqrt Real.pi * W : ℝ) : ℂ) *
        cexp (((-σ * Real.log m - W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4 : ℝ) : ℂ) +
          (((Real.log n - Real.log m) * T : ℝ) : ℂ) * I) := by
  set u : ℝ := Real.log n - Real.log m with hu
  set κ : ℂ := (((3 - σ) * Real.log n - 3 * Real.log m : ℝ) : ℂ) with hκ
  have hpt : ∀ y : ℝ, deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
      ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹) =
      cexp ((((3 - σ : ℝ) : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 +
        (u : ℂ) * (y : ℂ) * I) * cexp κ := by
    intro y
    rw [natCast_cpow_eq_cexp_log hn, natCast_cpow_eq_cexp_log hm, ← Complex.exp_neg, deletionGaussWindow,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hκ, hu]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_gaussian_window_fourier (3 - σ) T u hW, mul_assoc,
    ← Complex.exp_add]
  congr 2
  rw [hκ, hu]
  push_cast
  ring

theorem integrable_gaussian_window_fourier (a T u : ℝ) {W : ℝ} (hW : 0 < W) :
    Integrable fun y : ℝ =>
      cexp (((a : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 + (u : ℂ) * (y : ℂ) * I) := by
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  set b : ℂ := -1 / (W : ℂ) ^ 2 with hb
  set c : ℂ := (2 * T + 2 * a * I) / (W : ℂ) ^ 2 + u * I with hc
  set d : ℂ := ((a : ℂ) ^ 2 - T ^ 2 - 2 * a * T * I) / (W : ℂ) ^ 2 with hd
  have hbre : b.re < 0 := by
    have : b = ((-1 / W ^ 2 : ℝ) : ℂ) := by rw [hb]; push_cast; ring
    rw [this, Complex.ofReal_re]
    have : 0 < W ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by norm_num) this
  have hfun : (fun y : ℝ => cexp (((a : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 +
      (u : ℂ) * (y : ℂ) * I)) = fun y : ℝ => cexp (b * y ^ 2 + c * y + d) := by
    funext y
    congr 1
    rw [hb, hc, hd]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfun]
  exact integrable_cexp_quadratic' hbre c d

theorem gaussWindow_three_term_eq (σ T W : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (y : ℝ) :
    deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹) =
      cexp ((((3 - σ : ℝ) : ℂ) + ((y - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 +
        ((Real.log n - Real.log m : ℝ) : ℂ) * (y : ℂ) * I) *
        cexp ((((3 - σ) * Real.log n - 3 * Real.log m : ℝ) : ℂ)) := by
  rw [natCast_cpow_eq_cexp_log hn, natCast_cpow_eq_cexp_log hm, ← Complex.exp_neg, deletionGaussWindow,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem integrable_gaussWindow_three_term (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    Integrable fun y : ℝ => deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹) := by
  simp_rw [gaussWindow_three_term_eq σ T W hn hm]
  exact (integrable_gaussian_window_fourier (3 - σ) T _ hW).mul_const _

theorem norm_gaussWindow_three_term (σ T W : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (y : ℝ) :
    ‖deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹)‖ =
      Real.exp (((3 - σ) ^ 2 - (y - T) ^ 2) / W ^ 2) * ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [norm_mul, norm_mul, norm_inv,
    show ((3 : ℂ) + (y : ℂ) * I) = (((3 : ℝ) : ℂ) + (y : ℂ) * I) by push_cast; ring,
    norm_gaussWindow]
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, show (m : ℂ) = ((m : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
    Complex.norm_cpow_eq_rpow_re_of_pos hm0]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
  rw [Real.rpow_neg hm0.le]

variable (e : ℕ → ℝ)

theorem integral_exp_gauss_shift (T : ℝ) {W : ℝ} (hW : 0 < W) :
    ∫ y : ℝ, Real.exp (-(y - T) ^ 2 / W ^ 2) = Real.sqrt Real.pi * W := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun y : ℝ => Real.exp (-(1 / W ^ 2) * y ^ 2)) T
  rw [integral_gaussian, div_div_eq_mul_div, div_one, Real.sqrt_mul' _ (by positivity),
    Real.sqrt_sq hW.le] at h
  rw [← h]
  congr 1
  funext y
  ring_nf

theorem integrable_exp_gauss_shift (T : ℝ) {W : ℝ} (hW : 0 < W) :
    Integrable fun y : ℝ => Real.exp (-(y - T) ^ 2 / W ^ 2) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / W ^ 2) (by positivity)).comp_sub_right T
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  ring_nf

/-- The right-edge integrand, term by term. -/
def rightTerm (σ T W : ℝ) (n m : ℕ) (y : ℝ) : ℂ :=
  deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
    ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) *
      LSeries.term (pertSeq e) ((3 : ℂ) + (y : ℂ) * I) m)

theorem rightTerm_eq (σ T W : ℝ) {n m : ℕ} (hm : 1 ≤ m) (y : ℝ) :
    rightTerm e σ T W n m y = pertSeq e m *
      (deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹)) := by
  unfold rightTerm
  rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv]
  ring

theorem integrable_rightTerm (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    Integrable (rightTerm e σ T W n m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : rightTerm e σ T W n 0 = fun _ => 0 := by
      funext y; simp [rightTerm, LSeries.term_zero]
    rw [this]; exact integrable_zero _ _ _
  · have : rightTerm e σ T W n m = fun y : ℝ => pertSeq e m *
        (deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
          ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * ((m : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I))⁻¹)) :=
      funext (rightTerm_eq e σ T W hm)
    rw [this]
    exact (integrable_gaussWindow_three_term σ T hW hn hm).const_mul _

theorem integral_norm_rightTerm_le (he : ∀ n, |e n| ≤ Real.log n) (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 1 ≤ n)
    (m : ℕ) :
    ∫ y, ‖rightTerm e σ T W n m y‖ ≤
      Real.exp ((3 - σ) ^ 2 / W ^ 2) * (Real.sqrt Real.pi * W) * (n : ℝ) ^ (3 - σ) *
        (m : ℝ) ^ (-2 : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : (fun y => ‖rightTerm e σ T W n 0 y‖) = fun _ => 0 := by
      funext y; simp [rightTerm, LSeries.term_zero]
    rw [this, integral_zero]
    simp only [CharP.cast_eq_zero]
    positivity
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hpt : ∀ y, ‖rightTerm e σ T W n m y‖ ≤ (m : ℝ) * (Real.exp ((3 - σ) ^ 2 / W ^ 2) *
        ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ))) * Real.exp (-(y - T) ^ 2 / W ^ 2) := by
      intro y
      rw [rightTerm_eq e σ T W hm, norm_mul, norm_gaussWindow_three_term σ T W hn hm]
      have ha : ‖pertSeq e m‖ ≤ m := by
        rw [pertSeq, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le_self_of_abs_le_log he m
      have hexp : Real.exp (((3 - σ) ^ 2 - (y - T) ^ 2) / W ^ 2) =
          Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [hexp]
      have h0 : 0 ≤ Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
          ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ)) := by positivity
      calc ‖pertSeq e m‖ * (Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
            ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ)))
          ≤ (m : ℝ) * (Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
            ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ))) := mul_le_mul_of_nonneg_right ha h0
        _ = _ := by ring
    have hint := (integrable_exp_gauss_shift T hW).const_mul ((m : ℝ) *
      (Real.exp ((3 - σ) ^ 2 / W ^ 2) * ((n : ℝ) ^ (3 - σ) * (m : ℝ) ^ (-3 : ℝ))))
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_gauss_shift T hW]
    have hmm : (m : ℝ) * (m : ℝ) ^ (-3 : ℝ) = (m : ℝ) ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hm0, Real.rpow_one]
    rw [← hmm]
    ring

theorem summable_integral_norm_rightTerm (he : ∀ n, |e n| ≤ Real.log n) (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun m => ∫ y, ‖rightTerm e σ T W n m y‖ := by
  refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _)
    (integral_norm_rightTerm_le e he σ T hW hn) ?_
  exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _

/-- **The right edge.**  On `Re s = 3` the windowed integral is a convergent sum of Gaussians in
`log(n/m)`. -/
theorem integral_right_eq_tsum (he : ∀ n, |e n| ≤ Real.log n) (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y : ℝ, deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I)) =
      ∑' m : ℕ, ∫ y : ℝ, rightTerm e σ T W n m y := by
  rw [integral_tsum_of_summable_integral_norm (integrable_rightTerm e σ T hW hn)
    (summable_integral_norm_rightTerm e he σ T hW hn)]
  congr 1
  funext y
  unfold rightTerm
  rw [LSeries, ← tsum_mul_left, ← tsum_mul_left]

theorem integral_rightTerm (σ T : ℝ) {W : ℝ} (hW : 0 < W) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∫ y : ℝ, rightTerm e σ T W n m y = pertSeq e m * (((Real.sqrt Real.pi * W : ℝ) : ℂ) *
        cexp (((-σ * Real.log m - W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4 : ℝ) : ℂ) +
          (((Real.log n - Real.log m) * T : ℝ) : ℂ) * I)) := by
  simp_rw [rightTerm_eq e σ T W hm]
  rw [integral_const_mul, integral_gaussWindow_three_term σ T hW hn hm]

/-- **Gaussian separation of distinct integers.**  For `m ≠ n ≤ X`,
`exp(-W² log²(n/m)/4) ≤ 4 (X/m)² exp(-W²/(32X²))` once `W² ≥ 24`. -/
theorem exp_neg_sq_log_sub_le {n m : ℕ} {X W : ℝ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m)
    (hnX : (n : ℝ) ≤ X) (hW : 24 ≤ W ^ 2) :
    Real.exp (-(W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4)) ≤
      4 * (X / m) ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hX1 : 1 ≤ X := le_trans (by exact_mod_cast hn) hnX
  have hX0 : 0 < X := by linarith
  set u : ℝ := Real.log n - Real.log m with hu
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  -- `|u| ≥ 1/(2X)`
  have hgap : 1 / (2 * X) ≤ |u| := by
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · -- `n < m`
      have hmn : (n : ℝ) < m := by exact_mod_cast hlt
      have hlog : 1 - (n : ℝ) / m ≤ Real.log m - Real.log n := by
        rw [← Real.log_div hm0.ne' hn0.ne']
        have := Real.add_one_le_exp (Real.log ((m : ℝ) / n))
        rw [Real.exp_log (by positivity)] at this
        have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < m / n by positivity)
        rw [inv_div] at h1
        exact h1
      rw [abs_of_neg (by rw [hu]; linarith [Real.log_lt_log hn0 hmn])]
      rcases le_or_gt (m : ℝ) (2 * X) with hm2 | hm2
      · have : 1 / (2 * X) ≤ 1 - (n : ℝ) / m := by
          have h1 : (1 : ℝ) ≤ m - n := by
            have : n + 1 ≤ m := hlt
            have : (n : ℝ) + 1 ≤ m := by exact_mod_cast this
            linarith
          rw [sub_div' (by positivity), le_div_iff₀ hm0]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      · have : Real.log 2 ≤ Real.log m - Real.log n := by
          rw [← Real.log_div hm0.ne' hn0.ne']
          apply Real.log_le_log (by norm_num)
          rw [le_div_iff₀ hn0]; linarith
        have : 1 / (2 * X) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        linarith
    · -- `m < n`
      have hmn : (m : ℝ) < n := by exact_mod_cast hgt
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / m by positivity)
      rw [inv_div, Real.log_div hn0.ne' hm0.ne'] at h1
      rw [abs_of_pos (by rw [hu]; linarith [Real.log_lt_log hm0 hmn])]
      have : 1 / (2 * X) ≤ 1 - (m : ℝ) / n := by
        have h2 : (1 : ℝ) ≤ n - m := by
          have : m + 1 ≤ n := hgt
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast this
          linarith
        rw [sub_div' (by positivity), le_div_iff₀ hn0]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
  have hu2 : 1 / (4 * X ^ 2) ≤ u ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hgap 2
    rw [sq_abs, div_pow] at h
    calc 1 / (4 * X ^ 2) = 1 ^ 2 / (2 * X) ^ 2 := by ring
      _ ≤ u ^ 2 := h
  -- split the Gaussian
  have hsplit : Real.exp (-(W ^ 2 * u ^ 2 / 4)) =
      Real.exp (-(W ^ 2 * u ^ 2 / 8)) * Real.exp (-(W ^ 2 * u ^ 2 / 8)) := by
    rw [← Real.exp_add]; ring_nf
  have hfirst : Real.exp (-(W ^ 2 * u ^ 2 / 8)) ≤ Real.exp (-(W ^ 2 / (32 * X ^ 2))) := by
    apply Real.exp_le_exp.mpr
    have : W ^ 2 / (32 * X ^ 2) ≤ W ^ 2 * u ^ 2 / 8 := by
      have hW0 : 0 ≤ W ^ 2 := by positivity
      calc W ^ 2 / (32 * X ^ 2) = W ^ 2 * (1 / (4 * X ^ 2)) / 8 := by field_simp; ring
        _ ≤ W ^ 2 * u ^ 2 / 8 := by gcongr
    linarith
  have hsecond : Real.exp (-(W ^ 2 * u ^ 2 / 8)) ≤ 4 * (X / m) ^ 2 := by
    rcases le_or_gt (m : ℝ) (2 * X) with hm2 | hm2
    · have : 1 ≤ 4 * (X / m) ^ 2 := by
        rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith
      have : Real.exp (-(W ^ 2 * u ^ 2 / 8)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ W ^ 2 * u ^ 2 / 8 := by positivity
        linarith)
      linarith
    · have hmn : (n : ℝ) < m := by linarith
      have hlogmn : Real.log 2 ≤ Real.log m - Real.log n := by
        rw [← Real.log_div hm0.ne' hn0.ne']
        apply Real.log_le_log (by norm_num)
        rw [le_div_iff₀ hn0]; linarith
      have hneg : u = -(Real.log m - Real.log n) := by rw [hu]; ring
      set v : ℝ := Real.log m - Real.log n with hv
      have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hv0 : (0.69 : ℝ) ≤ v := le_trans hl2 hlogmn
      have hkey : 2 * v ≤ W ^ 2 * u ^ 2 / 8 := by
        rw [hneg, neg_sq]
        have h1 : 16 ≤ W ^ 2 * v := by nlinarith
        have h2 : 2 * v * 8 ≤ W ^ 2 * v * v := by nlinarith
        linarith
      have hev : Real.exp (-(2 * v)) = ((n : ℝ) / m) ^ 2 := by
        have : -(2 * v) = Real.log (((n : ℝ) / m) ^ 2) := by
          rw [Real.log_pow, Real.log_div hn0.ne' hm0.ne', hv]; push_cast; ring
        rw [this, Real.exp_log (by positivity)]
      have hnmX : ((n : ℝ) / m) ^ 2 ≤ (X / m) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right hnX hm0.le
      calc Real.exp (-(W ^ 2 * u ^ 2 / 8)) ≤ Real.exp (-(2 * v)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = ((n : ℝ) / m) ^ 2 := hev
        _ ≤ (X / m) ^ 2 := hnmX
        _ ≤ 4 * (X / m) ^ 2 := by nlinarith [sq_nonneg (X / m)]
  rw [hsplit]
  calc Real.exp (-(W ^ 2 * u ^ 2 / 8)) * Real.exp (-(W ^ 2 * u ^ 2 / 8))
      ≤ Real.exp (-(W ^ 2 / (32 * X ^ 2))) * (4 * (X / m) ^ 2) :=
        mul_le_mul hfirst hsecond (Real.exp_pos _).le (Real.exp_pos _).le
    _ = 4 * (X / m) ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2))) := by ring

theorem integral_rightTerm_zero (σ T W : ℝ) (n : ℕ) :
    ∫ y : ℝ, rightTerm e σ T W n 0 y = 0 := by
  have : rightTerm e σ T W n 0 = fun _ => 0 := by
    funext y; simp [rightTerm, LSeries.term_zero]
  rw [this, integral_zero]

/-- **The right edge is diagonal up to a Gaussian error.** -/
theorem norm_tsum_integral_rightTerm_sub_le (he : ∀ n, |e n| ≤ Real.log n) (σ T : ℝ) (hσ0 : 0 < σ) {W X : ℝ} (hW : 0 < W)
    (hW24 : 24 ≤ W ^ 2) {n : ℕ} (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ X) :
    ‖(∑' m : ℕ, ∫ y : ℝ, rightTerm e σ T W n m y) -
        ((Real.sqrt Real.pi * W : ℝ) : ℂ) * ((e n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)‖
      ≤ Real.sqrt Real.pi * W * (4 * X ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2)))) *
        ∑' m : ℕ, (m : ℝ) ^ (-1 - σ) := by
  set v : ℕ → ℂ := fun m => ∫ y : ℝ, rightTerm e σ T W n m y with hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hvsum : Summable v :=
    (summable_integral_norm_rightTerm e he σ T hW hn).of_norm_bounded
      (fun m => norm_integral_le_integral_norm _)
  have hvn : v n = ((Real.sqrt Real.pi * W : ℝ) : ℂ) *
      ((e n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [hv]
    simp only
    rw [integral_rightTerm e σ T hW hn hn, sub_self]
    have : cexp ((((-σ * Real.log n - W ^ 2 * 0 ^ 2 / 4 : ℝ)) : ℂ) + (((0 : ℝ) * T : ℝ) : ℂ) * I) =
        (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Real.rpow_def_of_pos hn0, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [this, pertSeq]
    push_cast
    ring
  have hX1 : 1 ≤ X := le_trans (by exact_mod_cast hn) hnX
  set E : ℝ := Real.sqrt Real.pi * W * (4 * X ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2)))) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hbsum : Summable fun m : ℕ => E * (m : ℝ) ^ (-1 - σ) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left E
  have hpt : ∀ m : ℕ, ‖if m = n then (0 : ℂ) else v m‖ ≤ E * (m : ℝ) ^ (-1 - σ) := by
    intro m
    have hrpow0 : 0 ≤ (m : ℝ) ^ (-1 - σ) := Real.rpow_nonneg (Nat.cast_nonneg m) _
    split_ifs with hmn
    · rw [norm_zero]; exact mul_nonneg hE0 hrpow0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hv]; simp only; rw [integral_rightTerm_zero, norm_zero]
      exact mul_nonneg hE0 hrpow0
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [hv]
    simp only
    rw [integral_rightTerm e σ T hW hn hm, norm_mul, norm_mul, Complex.norm_exp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ha : ‖pertSeq e m‖ ≤ m := by
      rw [pertSeq, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le_self_of_abs_le_log he m
    have hgap := exp_neg_sq_log_sub_le hn hm (Ne.symm hmn) hnX hW24
    have hexp : Real.exp (-σ * Real.log m - W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4) =
        (m : ℝ) ^ (-σ) * Real.exp (-(W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4)) := by
      rw [Real.rpow_def_of_pos hm0, ← Real.exp_add]; ring_nf
    rw [hexp]
    have hmσ : (m : ℝ) * (m : ℝ) ^ (-σ) * (X / m) ^ 2 = X ^ 2 * (m : ℝ) ^ (-1 - σ) := by
      rw [div_pow, show (-1 - σ : ℝ) = (-σ) + (-1) by ring, Real.rpow_add hm0,
        Real.rpow_neg_one]
      field_simp
    calc ‖pertSeq e m‖ * (Real.sqrt Real.pi * W *
          ((m : ℝ) ^ (-σ) * Real.exp (-(W ^ 2 * (Real.log n - Real.log m) ^ 2 / 4))))
        ≤ (m : ℝ) * (Real.sqrt Real.pi * W * ((m : ℝ) ^ (-σ) *
          (4 * (X / m) ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2)))))) := by
          apply mul_le_mul ha _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hm0.le _)
      _ = E * (X ^ 2 * (m : ℝ) ^ (-1 - σ)) / X ^ 2 := by
          rw [hE, ← hmσ]; field_simp
      _ = E * (m : ℝ) ^ (-1 - σ) := by field_simp
  rw [hvsum.tsum_eq_add_tsum_ite n, hvn, add_sub_cancel_left]
  have hsumite : Summable fun m : ℕ => if m = n then (0 : ℂ) else v m :=
    Summable.of_norm_bounded hbsum hpt
  calc ‖∑' m : ℕ, if m = n then (0 : ℂ) else v m‖
      ≤ ∑' m : ℕ, ‖if m = n then (0 : ℂ) else v m‖ := norm_tsum_le_tsum_norm hsumite.norm
    _ ≤ ∑' m : ℕ, E * (m : ℝ) ^ (-1 - σ) := hsumite.norm.tsum_le_tsum hpt hbsum
    _ = E * ∑' m : ℕ, (m : ℝ) ^ (-1 - σ) := tsum_mul_left

theorem norm_LSeries_pertSeq_le (he : ∀ n, |e n| ≤ Real.log n) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖LSeries (pertSeq e) s‖ ≤ ∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ) := by
  have hbound : ∀ m : ℕ, ‖LSeries.term (pertSeq e) s m‖ ≤ (m : ℝ) ^ (-2 : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [LSeries.term_zero, Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [LSeries.term_of_ne_zero (by omega), norm_div,
      show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
    have ha : ‖pertSeq e m‖ ≤ m := by
      rw [pertSeq, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le_self_of_abs_le_log he m
    have hpow : (m : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hs
    calc ‖pertSeq e m‖ / (m : ℝ) ^ s.re ≤ (m : ℝ) / (m : ℝ) ^ (3 : ℝ) :=
          div_le_div₀ hm0.le ha (by positivity) hpow
      _ = (m : ℝ) ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = 1 - 3 by norm_num, Real.rpow_sub hm0, Real.rpow_one]
  have hsum : Summable fun m : ℕ => (m : ℝ) ^ (-2 : ℝ) := Real.summable_nat_rpow.mpr (by norm_num)
  have hsum' : Summable fun m => ‖LSeries.term (pertSeq e) s m‖ :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [LSeries]
  exact (norm_tsum_le_tsum_norm hsum').trans (hsum'.tsum_le_tsum hbound hsum)

theorem exp_gauss_tail_le {y T W : ℝ} (hW : 0 < W) (hT : 0 ≤ T) (hy : T / 2 ≤ |y - T|) :
    Real.exp (-(y - T) ^ 2 / W ^ 2) ≤
      Real.exp (-(T ^ 2 / (8 * W ^ 2))) * Real.exp (-(y - T) ^ 2 / (Real.sqrt 2 * W) ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hW2 : 0 < W ^ 2 := by positivity
  have hs2 : (Real.sqrt 2 * W) ^ 2 = 2 * W ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [hs2]
  have hsq : T ^ 2 / 4 ≤ (y - T) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hy 2
    rw [sq_abs] at this; nlinarith
  have e : -(y - T) ^ 2 / W ^ 2 = -(T ^ 2 / (8 * W ^ 2)) + -(y - T) ^ 2 / (2 * W ^ 2) -
      ((y - T) ^ 2 - T ^ 2 / 4) / (2 * W ^ 2) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ ((y - T) ^ 2 - T ^ 2 / 4) / (2 * W ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

theorem abscissa_pertSeq_le (he : ∀ n, |e n| ≤ Real.log n) : LSeries.abscissaOfAbsConv (pertSeq e) ≤ 2 := by
  have h := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (pertSeq_isBigO he)
  norm_num at h
  exact h

theorem continuous_LSeries_pertSeq_three (he : ∀ n, |e n| ≤ Real.log n) :
    Continuous fun y : ℝ => LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hre : LSeries.abscissaOfAbsConv (pertSeq e) < ((3 : ℂ) + (y : ℂ) * I).re := by
    have h := abscissa_pertSeq_le e he
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    refine lt_of_le_of_lt h ?_
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by rfl, EReal.coe_lt_coe_iff]
    norm_num
  exact ContinuousAt.comp (g := LSeries (pertSeq e)) (f := fun y : ℝ => (3 : ℂ) + (y : ℂ) * I)
    (LSeries_hasDerivAt hre).differentiableAt.continuousAt (by fun_prop)

theorem continuous_rightIntegrand (he : ∀ n, |e n| ≤ Real.log n) (σ T W : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Continuous fun y : ℝ => deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
      ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact ((differentiable_gaussWindow σ T W).continuous.comp (by fun_prop)).mul
    ((continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.ofReal_re]; exact hn0))).mul (continuous_LSeries_pertSeq_three e he))

theorem norm_rightIntegrand_le (he : ∀ n, |e n| ≤ Real.log n) (σ T W : ℝ) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ‖deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
      ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))‖ ≤
      Real.exp ((3 - σ) ^ 2 / W ^ 2) * (n : ℝ) ^ (3 - σ) * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) *
        Real.exp (-(y - T) ^ 2 / W ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_mul, norm_mul, show ((3 : ℂ) + (y : ℂ) * I) = (((3 : ℝ) : ℂ) + (y : ℂ) * I) by
    push_cast; ring, norm_gaussWindow, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  have hre : ((((3 : ℝ) : ℂ) + (y : ℂ) * I - σ)).re = 3 - σ := by simp
  rw [hre]
  have hL := norm_LSeries_pertSeq_le e he (s := ((3 : ℝ) : ℂ) + (y : ℂ) * I) (by simp)
  have hexp : Real.exp (((3 - σ) ^ 2 - (y - T) ^ 2) / W ^ 2) =
      Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have h0 : 0 ≤ Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
      (n : ℝ) ^ (3 - σ) := by positivity
  calc Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
        ((n : ℝ) ^ (3 - σ) * ‖LSeries (pertSeq e) (((3 : ℝ) : ℂ) + (y : ℂ) * I)‖)
      ≤ Real.exp ((3 - σ) ^ 2 / W ^ 2) * Real.exp (-(y - T) ^ 2 / W ^ 2) *
        ((n : ℝ) ^ (3 - σ) * ∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

/-- **Truncating the right edge.**  Outside `[T/2, 3T/2]` the right-edge integrand is
Gaussian-small. -/
theorem norm_integral_right_sub_interval_le (he : ∀ n, |e n| ≤ Real.log n) (σ T : ℝ) {W : ℝ} (hW : 0 < W) (hT : 0 ≤ T)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖(∫ y : ℝ, deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))) -
      ∫ y in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))‖ ≤
      Real.exp ((3 - σ) ^ 2 / W ^ 2) * (n : ℝ) ^ (3 - σ) * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) *
        Real.exp (-(T ^ 2 / (8 * W ^ 2))) * (Real.sqrt Real.pi * (Real.sqrt 2 * W)) := by
  set f : ℝ → ℂ := fun y => deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
    ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))
    with hf
  set C₀ : ℝ := Real.exp ((3 - σ) ^ 2 / W ^ 2) * (n : ℝ) ^ (3 - σ) *
    (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    have : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ) :=
      tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
    positivity
  have hpt : ∀ y, ‖f y‖ ≤ C₀ * Real.exp (-(y - T) ^ 2 / W ^ 2) := fun y =>
    norm_rightIntegrand_le e he σ T W hn y
  have hint : Integrable f :=
    ((integrable_exp_gauss_shift T hW).const_mul C₀).mono'
      (continuous_rightIntegrand e he σ T W hn).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  have hle : T / 2 ≤ 3 * T / 2 := by linarith
  set s : Set ℝ := Ioc (T / 2) (3 * T / 2) with hs
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Ioc (a := T / 2) (b := 3 * T / 2))
    hint
  rw [intervalIntegral.integral_of_le hle, ← hsplit, add_sub_cancel_left]
  have hW2 : 0 < Real.sqrt 2 * W := by positivity
  have hmaj : Integrable fun y : ℝ =>
      C₀ * (Real.exp (-(T ^ 2 / (8 * W ^ 2))) * Real.exp (-(y - T) ^ 2 / (Real.sqrt 2 * W) ^ 2)) :=
    ((integrable_exp_gauss_shift T hW2).const_mul _).const_mul _
  have hbound : ∀ y ∈ sᶜ, ‖f y‖ ≤
      C₀ * (Real.exp (-(T ^ 2 / (8 * W ^ 2))) * Real.exp (-(y - T) ^ 2 / (Real.sqrt 2 * W) ^ 2)) := by
    intro y hy
    rw [hs, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy
    have hyT : T / 2 ≤ |y - T| := by
      rcases hy with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact (hpt y).trans (mul_le_mul_of_nonneg_left (exp_gauss_tail_le hW hT hyT) hC₀0)
  calc ‖∫ y in sᶜ, f y‖ ≤ ∫ y in sᶜ, C₀ * (Real.exp (-(T ^ 2 / (8 * W ^ 2))) *
        Real.exp (-(y - T) ^ 2 / (Real.sqrt 2 * W) ^ 2)) :=
        norm_integral_le_of_norm_le hmaj.integrableOn
          ((ae_restrict_iff' measurableSet_Ioc.compl).mpr (Filter.Eventually.of_forall hbound))
    _ ≤ ∫ y, C₀ * (Real.exp (-(T ^ 2 / (8 * W ^ 2))) *
        Real.exp (-(y - T) ^ 2 / (Real.sqrt 2 * W) ^ 2)) :=
        setIntegral_le_integral hmaj (Filter.Eventually.of_forall fun y => by positivity)
    _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_exp_gauss_shift T hW2]
        ring

theorem abs_pertChebyshev_le_sq (he : ∀ n, |e n| ≤ Real.log n) {x : ℝ} (hx : 1 ≤ x) :
    |pertChebyshev e x| ≤ x ^ 2 := by
  unfold pertChebyshev
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  calc |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, e k| ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, |e k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊x⌋₊, x :=
        Finset.sum_le_sum fun k hk => (abs_le_self_of_abs_le_log he k).trans
          ((Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans hfl)
    _ = (⌊x⌋₊ : ℝ) * x := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ x * x := mul_le_mul_of_nonneg_right hfl (by linarith)
    _ = x ^ 2 := by ring

/-- The Chebyshev remainder is `O(x^η)` uniformly on `[1, ∞)`. -/
theorem exists_forall_norm_remainder_le (he : ∀ n, |e n| ≤ Real.log n) {J : Finset ℂ} {c : ℂ → ℂ} {η : ℝ}
    (hη : 0 ≤ η)
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖remainder e J c x‖ ≤ C * x ^ η := by
  obtain ⟨C₀, hC₀⟩ := hψ.bound
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hC₀
  set x₁ : ℝ := max x₀ 1 with hx₁
  set B : ℝ := x₁ ^ 2 + ∑ ρ ∈ J, ‖c ρ‖ * x₁ ^ |ρ.re| with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨max (max C₀ 0) B, le_max_of_le_left (le_max_right _ _), fun x hx => ?_⟩
  have hxη : 1 ≤ x ^ η := Real.one_le_rpow hx hη
  have hpos : 0 ≤ x ^ η := by linarith
  rcases le_or_gt x₀ x with h | h
  · have := hx₀ x h
    rw [Real.norm_eq_abs, abs_of_nonneg hpos] at this
    calc ‖remainder e J c x‖ ≤ C₀ * x ^ η := this
      _ ≤ max (max C₀ 0) B * x ^ η :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hpos
  · have hxx₁ : x ≤ x₁ := le_trans h.le (le_max_left _ _)
    have hbound : ‖remainder e J c x‖ ≤ B := by
      unfold remainder
      refine (norm_sub_le _ _).trans ?_
      rw [hB]
      apply add_le_add
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_pertChebyshev_le_sq e he hx).trans (pow_le_pow_left₀ (by linarith) hxx₁ 2)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc x ^ ρ.re ≤ x ^ |ρ.re| := Real.rpow_le_rpow_of_exponent_le hx (le_abs_self _)
          _ ≤ x₁ ^ |ρ.re| := Real.rpow_le_rpow (by linarith) hxx₁ (abs_nonneg _)
    calc ‖remainder e J c x‖ ≤ B := hbound
      _ ≤ max (max C₀ 0) B * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max (max C₀ 0) B * x ^ η :=
          mul_le_mul_of_nonneg_left hxη (le_max_of_le_left (le_max_right _ _))

/-- Above the exponents the continued `L(Λ_Q)` grows at most linearly. -/
theorem norm_pertLogDeriv_le {J : Finset ℂ} {c : ℂ → ℂ} {η CR B : ℝ}
    (hCR : ∀ x : ℝ, 1 ≤ x → ‖remainder e J c x‖ ≤ CR * x ^ η)
    (hJ : ∀ ρ ∈ J, |ρ.im| ≤ B) {s : ℂ} (hs : η < s.re) (him : B + 1 ≤ |s.im|) :
    ‖pertLogDeriv e J c s‖ ≤ ‖s‖ * (∑ ρ ∈ J, ‖c ρ‖ + CR / (s.re - η)) := by
  unfold pertLogDeriv
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [norm_div]
    have h1 : 1 ≤ ‖s - ρ‖ := by
      have := Complex.abs_im_le_norm (s - ρ)
      rw [Complex.sub_im] at this
      have := abs_sub_abs_le_abs_sub s.im ρ.im
      linarith [hJ ρ hρ]
    exact div_le_self (norm_nonneg _) h1
  · exact norm_integral_mul_cpow_le hCR hs

/-- **The windowed line integral against `n^{it}`.**  On `Re s = σ` the window picks out the
Dirichlet coefficient `Λ_Q(n) n^{-σ}` of the continued `L(Λ_Q)`, up to the horizontal edges of the
rectangle `[σ, 3] × [T/2, 3T/2]`, the Gaussian tail on `Re s = 3` and the off-diagonal Gaussians. -/
theorem norm_windowed_line_integral_sub_le (he : ∀ n, |e n| ≤ Real.log n) {J : Finset ℂ} {c : ℂ → ℂ} {η σ CR T W X B : ℝ}
    (hψ : (fun x : ℝ => (pertChebyshev e x : ℂ) - ∑ ρ ∈ J, c ρ * (x : ℂ) ^ ρ) =O[atTop]
      fun x : ℝ => x ^ η)
    (hCR : ∀ x : ℝ, 1 ≤ x → ‖remainder e J c x‖ ≤ CR * x ^ η)
    (hJ : ∀ ρ ∈ J, ρ.re < 2 ∧ |ρ.im| ≤ B) (hησ : η < σ) (hσ0 : 0 < σ) (hσ3 : σ ≤ 3)
    (hW : 0 < W) (hW24 : 24 ≤ W ^ 2) (hT : 2 ≤ T) (hTB : B + 1 ≤ T / 2) {n : ℕ} (hn : 1 ≤ n)
    (hnX : (n : ℝ) ≤ X) :
    ‖(∫ t in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I))) -
      ((Real.sqrt Real.pi * W : ℝ) : ℂ) * ((e n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ≤
      2 * (3 - σ) * (Real.exp ((9 - T ^ 2 / 4) / W ^ 2) * (n : ℝ) ^ (3 : ℝ) * ((3 + 2 * T) *
          (∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η)))) +
        Real.exp ((3 - σ) ^ 2 / W ^ 2) * (n : ℝ) ^ (3 - σ) * (∑' m : ℕ, (m : ℝ) ^ (-2 : ℝ)) *
          Real.exp (-(T ^ 2 / (8 * W ^ 2))) * (Real.sqrt Real.pi * (Real.sqrt 2 * W)) +
        Real.sqrt Real.pi * W * (4 * X ^ 2 * Real.exp (-(W ^ 2 / (32 * X ^ 2)))) *
          ∑' m : ℕ, (m : ℝ) ^ (-1 - σ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℂ → ℂ := fun s => deletionGaussWindow σ T W s * ((n : ℂ) ^ (s - σ) * pertLogDeriv e J c s)
    with hh
  set CF : ℝ := ∑ ρ ∈ J, ‖c ρ‖ + CR / (σ - η) with hCF
  have hCR0 : 0 ≤ CR := by
    have := hCR 1 le_rfl
    rw [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hCF0 : 0 ≤ CF := by
    rw [hCF]
    have : 0 ≤ CR / (σ - η) := div_nonneg hCR0 (by linarith)
    have : 0 ≤ ∑ ρ ∈ J, ‖c ρ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  -- differentiability on the rectangle
  have hdiff : DifferentiableOn ℂ h ([[σ, (3 : ℝ)]] ×ℂ [[T / 2, 3 * T / 2]]) := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le hσ3, uIcc_of_le (by linarith)] at hs
    have hsre : η < s.re := by linarith [hs.1.1]
    have hsJ : ∀ ρ ∈ J, s ≠ ρ := by
      intro ρ hρ hsρ
      have := (hJ ρ hρ).2
      rw [← hsρ] at this
      linarith [hs.2.1, le_abs_self s.im]
    have hcpow : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (s - σ)) s := by
      refine DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn0.ne'))
    exact (((differentiable_gaussWindow σ T W) s).mul (hcpow.mul
      (differentiableAt_pertLogDeriv hψ hsre hsJ))).differentiableWithinAt
  -- horizontal edges
  have hedge : ∀ x ∈ uIcc σ 3, ‖h (x + (T / 2 : ℝ) * I)‖ ≤
      Real.exp ((9 - T ^ 2 / 4) / W ^ 2) * (n : ℝ) ^ (3 : ℝ) * ((3 + 2 * T) * CF) ∧
      ‖h (x + (3 * T / 2 : ℝ) * I)‖ ≤
      Real.exp ((9 - T ^ 2 / 4) / W ^ 2) * (n : ℝ) ^ (3 : ℝ) * ((3 + 2 * T) * CF) := by
    intro x hx
    rw [uIcc_of_le hσ3] at hx
    have hone : ∀ y : ℝ, (y = T / 2 ∨ y = 3 * T / 2) → ‖h (x + y * I)‖ ≤
        Real.exp ((9 - T ^ 2 / 4) / W ^ 2) * (n : ℝ) ^ (3 : ℝ) * ((3 + 2 * T) * CF) := by
      intro y hy
      have hyT : (y - T) ^ 2 = T ^ 2 / 4 := by rcases hy with rfl | rfl <;> ring
      have hy1 : B + 1 ≤ |y| := by
        rcases hy with rfl | rfl
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hyle : |y| ≤ 3 * T / 2 := by
        rcases hy with rfl | rfl
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]
      rw [hh]
      simp only
      rw [norm_mul, norm_mul, norm_gaussWindow, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hsre : ((x : ℂ) + (y : ℂ) * I - σ).re = x - σ := by simp
      rw [hsre, hyT]
      have hF := norm_pertLogDeriv_le e hCR (fun ρ hρ => (hJ ρ hρ).2)
        (s := (x : ℂ) + (y : ℂ) * I) (by simp; linarith [hx.1]) (by simpa using hy1)
      have hsnorm : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ 3 + 2 * T := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        rw [abs_of_nonneg (by linarith [hx.1])]
        linarith [hx.2]
      have hsre' : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
      rw [hsre'] at hF
      have hCFx : ∑ ρ ∈ J, ‖c ρ‖ + CR / (x - η) ≤ CF := by
        rw [hCF]
        have : CR / (x - η) ≤ CR / (σ - η) :=
          div_le_div_of_nonneg_left hCR0 (by linarith) (by linarith [hx.1])
        linarith
      have hnn : 0 ≤ ∑ ρ ∈ J, ‖c ρ‖ + CR / (x - η) :=
        add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (div_nonneg hCR0 (by linarith [hx.1]))
      have hFb : ‖pertLogDeriv e J c ((x : ℂ) + (y : ℂ) * I)‖ ≤ (3 + 2 * T) * CF :=
        hF.trans (mul_le_mul hsnorm hCFx hnn (by linarith))
      have hge : Real.exp (((x - σ) ^ 2 - T ^ 2 / 4) / W ^ 2) ≤
          Real.exp ((9 - T ^ 2 / 4) / W ^ 2) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (x - σ) ^ 2 ≤ 9 := by nlinarith [hx.1, hx.2]
        linarith
      have hnp : (n : ℝ) ^ (x - σ) ≤ (n : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith [hx.2])
      calc Real.exp (((x - σ) ^ 2 - T ^ 2 / 4) / W ^ 2) *
            ((n : ℝ) ^ (x - σ) * ‖pertLogDeriv e J c ((x : ℂ) + (y : ℂ) * I)‖)
          ≤ Real.exp ((9 - T ^ 2 / 4) / W ^ 2) * ((n : ℝ) ^ (3 : ℝ) * ((3 + 2 * T) * CF)) :=
            mul_le_mul hge (mul_le_mul hnp hFb (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = _ := by ring
    exact ⟨hone _ (Or.inl rfl), hone _ (Or.inr rfl)⟩
  have hrect := norm_sub_intervalIntegral_vertical_le (h := h) hσ3 (by
    simpa using hdiff) hedge
  -- the right edge is the right integrand
  have hright : (∫ y in (T / 2)..(3 * T / 2), h ((3 : ℝ) + y * I)) =
      ∫ y in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
        ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hh]
    simp only
    have hL := LSeries_pertSeq_eq he hψ (s := (3 : ℂ) + (y : ℂ) * I) (by simp; norm_num)
      (by simp; linarith) (fun ρ hρ => by simp; linarith [(hJ ρ hρ).1])
    have hL' : pertLogDeriv e J c ((3 : ℂ) + (y : ℂ) * I) =
        LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I) := by rw [hL]; rfl
    push_cast
    rw [hL']
  have htail := norm_integral_right_sub_interval_le e he σ T hW (by linarith) hn
  have hoff := norm_tsum_integral_rightTerm_sub_le e he σ T hσ0 hW hW24 hn hnX
  rw [← integral_right_eq_tsum e he σ T hW hn] at hoff
  have hleft : (∫ t in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
      ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * pertLogDeriv e J c ((σ : ℂ) + (t : ℂ) * I))) =
      ∫ t in (T / 2)..(3 * T / 2), h (σ + t * I) := rfl
  rw [hleft]
  rw [hright] at hrect
  set A := ∫ t in (T / 2)..(3 * T / 2), h (σ + t * I)
  set Bi := ∫ y in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
    ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))
  set Bf := ∫ y : ℝ, deletionGaussWindow σ T W ((3 : ℂ) + (y : ℂ) * I) *
    ((n : ℂ) ^ ((3 : ℂ) + (y : ℂ) * I - σ) * LSeries (pertSeq e) ((3 : ℂ) + (y : ℂ) * I))
  set D := ((Real.sqrt Real.pi * W : ℝ) : ℂ) * ((e n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
  calc ‖A - D‖ = ‖(A - Bi) + (-(Bf - Bi)) + (Bf - D)‖ := by congr 1; ring
    _ ≤ ‖A - Bi‖ + ‖Bf - Bi‖ + ‖Bf - D‖ := by
        refine (norm_add₃_le).trans ?_
        rw [norm_neg]
    _ ≤ _ := by gcongr

/-- The real window on the critical-strip line. -/
theorem integral_exp_gauss_mul_cexp (T u : ℝ) {W : ℝ} (hW : 0 < W) :
    ∫ t : ℝ, (Real.exp (-(t - T) ^ 2 / W ^ 2) : ℂ) * cexp ((u : ℂ) * (t : ℂ) * I) =
      ((Real.sqrt Real.pi * W : ℝ) : ℂ) * cexp ((u * T : ℝ) * I - ((W ^ 2 * u ^ 2 / 4 : ℝ) : ℂ)) := by
  have h := integral_gaussian_window_fourier 0 T u hW
  have hfun : (fun t : ℝ => (Real.exp (-(t - T) ^ 2 / W ^ 2) : ℂ) * cexp ((u : ℂ) * (t : ℂ) * I)) =
      fun t : ℝ => cexp ((((0 : ℝ) : ℂ) + ((t - T : ℝ) : ℂ) * I) ^ 2 / (W : ℂ) ^ 2 +
        (u : ℂ) * (t : ℂ) * I) := by
    funext t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfun, h]
  congr 2
  push_cast
  ring

theorem integrable_exp_gauss_mul_cexp (T u : ℝ) {W : ℝ} (hW : 0 < W) :
    Integrable fun t : ℝ => (Real.exp (-(t - T) ^ 2 / W ^ 2) : ℂ) * cexp ((u : ℂ) * (t : ℂ) * I) := by
  have h := integrable_gaussian_window_fourier 0 T u hW
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem natCast_cpow_mul_I_eq_cexp {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * I) = cexp ((Real.log n : ℂ) * (t : ℂ) * I) := by
  rw [natCast_cpow_eq_cexp_log hn]; ring_nf

/-- For distinct `n, n' ≤ N`, `|log n - log n'| ≥ 1/N`. -/
theorem one_div_le_abs_log_sub {n n' N : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') (hnn : n ≠ n')
    (hnN : n ≤ N) (hn'N : n' ≤ N) : 1 / (N : ℝ) ≤ |Real.log n - Real.log n'| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'0 : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (le_trans hn hnN)
  rcases lt_or_gt_of_ne hnn with hlt | hgt
  · have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n' / n by positivity)
    rw [inv_div, Real.log_div hn'0.ne' hn0.ne'] at h1
    rw [abs_sub_comm, abs_of_pos (by linarith [Real.log_lt_log hn0 (by exact_mod_cast hlt :
      (n : ℝ) < n')])]
    have h2 : (1 : ℝ) ≤ n' - n := by
      have : n + 1 ≤ n' := hlt
      have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast this
      linarith
    have h3 : 1 / (N : ℝ) ≤ 1 - (n : ℝ) / n' := by
      rw [sub_div' (by positivity), div_le_div_iff₀ hN0 hn'0]
      have : (n' : ℝ) ≤ N := by exact_mod_cast hn'N
      nlinarith
    linarith
  · have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / n' by positivity)
    rw [inv_div, Real.log_div hn0.ne' hn'0.ne'] at h1
    rw [abs_of_pos (by linarith [Real.log_lt_log hn'0 (by exact_mod_cast hgt :
      (n' : ℝ) < n)])]
    have h2 : (1 : ℝ) ≤ n - n' := by
      have : n' + 1 ≤ n := hgt
      have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast this
      linarith
    have h3 : 1 / (N : ℝ) ≤ 1 - (n' : ℝ) / n := by
      rw [sub_div' (by positivity), div_le_div_iff₀ hN0 hn0]
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      nlinarith
    linarith

/-- The Dirichlet polynomial `Σ_{n ≤ N} b_n n^{-it}`. -/
def dirPolyLine (b : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (b n : ℂ) * cexp (-((Real.log n : ℂ) * (t : ℂ) * I))

theorem continuous_dirPolyLine (b : ℕ → ℝ) (N : ℕ) : Continuous (dirPolyLine b N) := by
  unfold dirPolyLine
  fun_prop

theorem normSq_dirPolyLine (b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ‖dirPolyLine b N t‖ ^ 2 = (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
      ((b n * b n' : ℝ) : ℂ) * cexp (((Real.log n' - Real.log n : ℝ) : ℂ) * (t : ℂ) * I)).re := by
  rw [← Complex.normSq_eq_norm_sq]
  have h : (Complex.normSq (dirPolyLine b N t) : ℝ) =
      (dirPolyLine b N t * (starRingEnd ℂ) (dirPolyLine b N t)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [h]
  congr 1
  unfold dirPolyLine
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (-((Real.log n' : ℂ) * (t : ℂ) * I)) =
      (Real.log n' : ℂ) * (t : ℂ) * I := by
    rw [map_neg, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc]
  have : (b n : ℂ) * cexp (-((Real.log n : ℂ) * (t : ℂ) * I)) *
      ((b n' : ℂ) * cexp ((Real.log n' : ℂ) * (t : ℂ) * I)) =
      ((b n : ℂ) * (b n' : ℂ)) * (cexp (-((Real.log n : ℂ) * (t : ℂ) * I)) *
        cexp ((Real.log n' : ℂ) * (t : ℂ) * I)) := by ring
  rw [this, ← Complex.exp_add]
  push_cast
  congr 2
  ring

theorem norm_dirPolyLine_le (b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ‖dirPolyLine b N t‖ ≤ ∑ n ∈ Finset.Icc 1 N, |b n| := by
  unfold dirPolyLine
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have : (-((Real.log n : ℂ) * (t : ℂ) * I)).re = 0 := by
    rw [show ((Real.log n : ℂ) * (t : ℂ) * I) = ((Real.log n * t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.neg_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, neg_zero]
  rw [this, Real.exp_zero, mul_one]

/-- **The windowed mean square of a Dirichlet polynomial is nearly diagonal.** -/
theorem integral_normSq_dirPolyLine_le (b : ℕ → ℝ) (N : ℕ) (T : ℝ)
    {W : ℝ} (hW : 0 < W) (hT : 0 ≤ T) :
    ∫ t in (T / 2)..(3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2) * ‖dirPolyLine b N t‖ ^ 2 ≤
      Real.sqrt Real.pi * W * (∑ n ∈ Finset.Icc 1 N, b n ^ 2 +
        Real.exp (-(W ^ 2 / (4 * (N : ℝ) ^ 2))) * (∑ n ∈ Finset.Icc 1 N, |b n|) ^ 2) := by
  set g : ℝ → ℝ := fun t => Real.exp (-(t - T) ^ 2 / W ^ 2) * ‖dirPolyLine b N t‖ ^ 2 with hg
  have hgint : Integrable g := by
    refine ((integrable_exp_gauss_shift T hW).mul_const ((∑ n ∈ Finset.Icc 1 N, |b n|) ^ 2)).mono'
      (((Real.continuous_exp.comp (by fun_prop)).mul
        ((continuous_norm.comp (continuous_dirPolyLine b N)).pow 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [hg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirPolyLine_le b N t) 2) (Real.exp_pos _).le
  have hle : T / 2 ≤ 3 * T / 2 := by linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (setIntegral_le_integral hgint (Filter.Eventually.of_forall fun t => by
    rw [hg]; positivity)).trans ?_
  -- expand and integrate term by term
  set z : ℕ → ℕ → ℝ → ℂ := fun n n' t => (Real.exp (-(t - T) ^ 2 / W ^ 2) : ℂ) *
    (((b n * b n' : ℝ) : ℂ) * cexp (((Real.log n' - Real.log n : ℝ) : ℂ) * (t : ℂ) * I)) with hz
  have hzint : ∀ n n', Integrable (z n n') := by
    intro n n'
    have h := (integrable_exp_gauss_mul_cexp T (Real.log n' - Real.log n) hW).const_mul
      ((b n * b n' : ℝ) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hz]
    ring
  have hgz : ∀ t, g t = (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, z n n' t).re := by
    intro t
    rw [hg]
    simp only
    rw [normSq_dirPolyLine, ← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
  have hint2 : Integrable fun t => ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, z n n' t :=
    integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ => hzint n n'
  have hre : (∫ t, (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, z n n' t).re) =
      (∫ t, ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, z n n' t).re := by
    have := integral_re hint2
    exact this
  rw [show (∫ t, g t) = ∫ t, (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, z n n' t).re from
    integral_congr_ae (Filter.Eventually.of_forall hgz), hre,
    integral_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ => hzint n n']
  have hval : ∀ n n', ∫ t, z n n' t = ((b n * b n' : ℝ) : ℂ) *
      (((Real.sqrt Real.pi * W : ℝ) : ℂ) *
        cexp (((Real.log n' - Real.log n) * T : ℝ) * I -
          ((W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 : ℝ) : ℂ))) := by
    intro n n'
    have h := integral_exp_gauss_mul_cexp T (Real.log n' - Real.log n) hW
    rw [← h, ← integral_const_mul]
    congr 1
    funext t
    simp only [hz]
    ring
  simp_rw [integral_finsetSum _ fun n' _ => hzint _ n', hval]
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  set E : ℝ := Real.exp (-(W ^ 2 / (4 * (N : ℝ) ^ 2))) with hE
  have hpt : ∀ n ∈ Finset.Icc 1 N, ∀ n' ∈ Finset.Icc 1 N,
      (((b n * b n' : ℝ) : ℂ) * (((Real.sqrt Real.pi * W : ℝ) : ℂ) *
        cexp (((Real.log n' - Real.log n) * T : ℝ) * I -
          ((W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 : ℝ) : ℂ)))).re ≤
      Real.sqrt Real.pi * W * ((if n = n' then b n ^ 2 else 0) + E * (|b n| * |b n'|)) := by
    intro n hn n' hn'
    have hsp : 0 ≤ Real.sqrt Real.pi * W := by positivity
    split_ifs with hnn
    · subst hnn
      simp only [sub_self, zero_mul, Complex.ofReal_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, zero_div, Complex.exp_zero, mul_one]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
      have : 0 ≤ E * (|b n| * |b n|) := by positivity
      nlinarith
    · refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hsp, Complex.norm_exp]
      have hre : (((((Real.log n' - Real.log n) * T : ℝ) : ℂ) * I -
          ((W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 : ℝ) : ℂ))).re =
          -(W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4) := by
        rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, zero_sub,
          Complex.ofReal_re]
      rw [hre]
      have hgap := one_div_le_abs_log_sub (Finset.mem_Icc.mp hn').1 (Finset.mem_Icc.mp hn).1
        (Ne.symm hnn) (Finset.mem_Icc.mp hn').2 (Finset.mem_Icc.mp hn).2
      have hN0 : (0 : ℝ) < N := by
        have := (Finset.mem_Icc.mp hn).1
        have := (Finset.mem_Icc.mp hn).2
        exact_mod_cast (by omega : 0 < N)
      have hsq : 1 / (N : ℝ) ^ 2 ≤ (Real.log n' - Real.log n) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hgap 2
        rw [sq_abs, div_pow, one_pow] at this
        exact this
      have hexp : Real.exp (-(W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4)) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.mpr
        have : W ^ 2 / (4 * (N : ℝ) ^ 2) ≤ W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 := by
          calc W ^ 2 / (4 * (N : ℝ) ^ 2) = W ^ 2 * (1 / (N : ℝ) ^ 2) / 4 := by field_simp
            _ ≤ W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 := by gcongr
        linarith
      calc |b n| * |b n'| * (Real.sqrt Real.pi * W *
            Real.exp (-(W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4)))
          ≤ |b n| * |b n'| * (Real.sqrt Real.pi * W * E) := by gcongr
        _ = Real.sqrt Real.pi * W * (0 + E * (|b n| * |b n'|)) := by ring
  calc ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
        (((b n * b n' : ℝ) : ℂ) * (((Real.sqrt Real.pi * W : ℝ) : ℂ) *
          cexp (((Real.log n' - Real.log n) * T : ℝ) * I -
            ((W ^ 2 * (Real.log n' - Real.log n) ^ 2 / 4 : ℝ) : ℂ)))).re
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
          Real.sqrt Real.pi * W * ((if n = n' then b n ^ 2 else 0) + E * (|b n| * |b n'|)) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = Real.sqrt Real.pi * W * (∑ n ∈ Finset.Icc 1 N, b n ^ 2 +
          E * (∑ n ∈ Finset.Icc 1 N, |b n|) ^ 2) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sq (∑ n ∈ Finset.Icc 1 N, |b n|), Finset.sum_mul_sum]
        congr 2
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.sum_ite_eq]
          simp [hn]
        · simp only [Finset.mul_sum]

theorem conj_dirPolyLine (b : ℕ → ℝ) (N : ℕ) (σ t : ℝ) :
    (starRingEnd ℂ) (dirPolyLine b N t) =
      ∑ n ∈ Finset.Icc 1 N, (b n : ℂ) * (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) := by
  unfold dirPolyLine
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    show (σ : ℂ) + (t : ℂ) * I - σ = (t : ℂ) * I by ring,
    natCast_cpow_eq_cexp_log (Finset.mem_Icc.mp hn).1]
  congr 2
  rw [map_neg, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **Linearized mean square on `Re s = σ`.**  For any values `I_n` of the windowed pairings
`∫ K(t) n^{it} F(σ+it) dt` within `ε` of `√π W b_n`, the windowed mean square of `F` is at least
`√π W Σ b_n² - 2 ε Σ b_n - √π W E (Σ b_n)²`, where `E` is the off-diagonal Gaussian factor. -/
theorem windowed_meanSquare_ge {F : ℂ → ℂ} {σ T W ε : ℝ} (hW : 0 < W) (hT : 0 ≤ T)
    (hFc : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I)) (uIcc (T / 2) (3 * T / 2)))
    (b : ℕ → ℝ) (N : ℕ)
    (hI : ∀ n ∈ Finset.Icc 1 N,
      ‖(∫ t in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I))) -
        ((Real.sqrt Real.pi * W : ℝ) : ℂ) * (b n : ℂ)‖ ≤ ε) :
    Real.sqrt Real.pi * W * ∑ n ∈ Finset.Icc 1 N, b n ^ 2 - 2 * ε * ∑ n ∈ Finset.Icc 1 N, |b n| -
        Real.sqrt Real.pi * W * (Real.exp (-(W ^ 2 / (4 * (N : ℝ) ^ 2))) *
          (∑ n ∈ Finset.Icc 1 N, |b n|) ^ 2) ≤
      ∫ t in (T / 2)..(3 * T / 2), Real.exp (-(t - T) ^ 2 / W ^ 2) *
        ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hle : T / 2 ≤ 3 * T / 2 := by linarith
  set K : ℝ → ℝ := fun t => Real.exp (-(t - T) ^ 2 / W ^ 2) with hK
  set G : ℝ → ℂ := fun t => F ((σ : ℂ) + (t : ℂ) * I) with hG
  set B : ℝ → ℂ := dirPolyLine b N with hB
  have hKc : Continuous K := Real.continuous_exp.comp (by fun_prop)
  have hBc : Continuous B := continuous_dirPolyLine b N
  -- pointwise `|G|² ≥ 2 Re(G conj B) - |B|²`
  have hpt : ∀ t, K t * (2 * (G t * (starRingEnd ℂ) (B t)).re - ‖B t‖ ^ 2) ≤ K t * ‖G t‖ ^ 2 := by
    intro t
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h := Complex.normSq_nonneg (G t - B t)
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
    linarith
  have hGc : ContinuousOn G (uIcc (T / 2) (3 * T / 2)) := hFc
  have hint1 : IntervalIntegrable (fun t => K t * ‖G t‖ ^ 2) volume (T / 2) (3 * T / 2) :=
    (hKc.continuousOn.mul ((continuous_norm.comp_continuousOn hGc).pow 2)).intervalIntegrable
  have hint2 : IntervalIntegrable
      (fun t => K t * (2 * (G t * (starRingEnd ℂ) (B t)).re - ‖B t‖ ^ 2)) volume
      (T / 2) (3 * T / 2) :=
    (hKc.continuousOn.mul (((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hGc.mul (Complex.continuous_conj.comp hBc).continuousOn))).sub
        ((continuous_norm.comp hBc).pow 2).continuousOn))).intervalIntegrable
  refine le_trans ?_ (intervalIntegral.integral_mono_on hle hint2 hint1 fun t _ => hpt t)
  -- split the linear and quadratic parts
  have hlin : IntervalIntegrable (fun t => K t * (2 * (G t * (starRingEnd ℂ) (B t)).re)) volume
      (T / 2) (3 * T / 2) :=
    (hKc.continuousOn.mul (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (hGc.mul (Complex.continuous_conj.comp hBc).continuousOn)))).intervalIntegrable
  have hquad : IntervalIntegrable (fun t => K t * ‖B t‖ ^ 2) volume (T / 2) (3 * T / 2) :=
    (hKc.mul ((continuous_norm.comp hBc).pow 2)).intervalIntegrable _ _
  have hsplit : (∫ t in (T / 2)..(3 * T / 2), K t * (2 * (G t * (starRingEnd ℂ) (B t)).re -
      ‖B t‖ ^ 2)) = (∫ t in (T / 2)..(3 * T / 2), K t * (2 * (G t * (starRingEnd ℂ) (B t)).re)) -
      ∫ t in (T / 2)..(3 * T / 2), K t * ‖B t‖ ^ 2 := by
    rw [← intervalIntegral.integral_sub hlin hquad]
    congr 1; funext t; ring
  rw [hsplit]
  have hquadb := integral_normSq_dirPolyLine_le b N T hW hT
  -- the linear part is `2 Re Σ b_n I_n`
  set In : ℕ → ℂ := fun n => ∫ t in (T / 2)..(3 * T / 2), deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I)) with hIn
  have hlinval : (∫ t in (T / 2)..(3 * T / 2), K t * (2 * (G t * (starRingEnd ℂ) (B t)).re)) =
      2 * (∑ n ∈ Finset.Icc 1 N, (b n : ℂ) * In n).re := by
    set H : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N, (b n : ℂ) *
      (deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
        ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I))) with hH
    have hfun : ∀ t, K t * (2 * (G t * (starRingEnd ℂ) (B t)).re) = 2 * (H t).re := by
      intro t
      rw [hB, conj_dirPolyLine b N σ t, hH]
      simp only
      rw [gaussWindow_line, hK]
      simp only
      rw [Finset.mul_sum, Complex.re_sum, Complex.re_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have : (b n : ℂ) * (((Real.exp (-(t - T) ^ 2 / W ^ 2) : ℝ) : ℂ) *
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I))) =
          ((Real.exp (-(t - T) ^ 2 / W ^ 2) : ℝ) : ℂ) *
            (G t * ((b n : ℂ) * (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ))) := by
        rw [hG]; ring
      rw [this, Complex.re_ofReal_mul]
      ring
    have hterm : ∀ n ∈ Finset.Icc 1 N, IntervalIntegrable (fun t : ℝ => (b n : ℂ) *
        (deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
          ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I)))) volume
          (T / 2) (3 * T / 2) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      refine (continuousOn_const.mul (((differentiable_gaussWindow σ T W).continuous.comp
        (by fun_prop)).continuousOn.mul (ContinuousOn.mul ?_ hFc))).intervalIntegrable
      refine (Continuous.continuousOn ?_)
      exact continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]; exact hn0))
    have hHint : IntervalIntegrable H volume (T / 2) (3 * T / 2) := by
      have hHeq : H = ∑ n ∈ Finset.Icc 1 N, fun t : ℝ => (b n : ℂ) *
          (deletionGaussWindow σ T W ((σ : ℂ) + (t : ℂ) * I) *
            ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I - σ) * F ((σ : ℂ) + (t : ℂ) * I))) := by
        funext t
        rw [hH, Finset.sum_apply]
      rw [hHeq]
      exact IntervalIntegrable.sum (Finset.Icc 1 N) hterm
    rw [intervalIntegral.integral_congr (fun t _ => hfun t), intervalIntegral.integral_const_mul]
    congr 1
    have := Complex.reCLM.intervalIntegral_comp_comm hHint
    simp only [Complex.reCLM_apply] at this
    rw [this, hH, intervalIntegral.integral_finsetSum hterm]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [hlinval]
  -- each pairing is close to `√π W b_n`
  have hre : ∀ n ∈ Finset.Icc 1 N,
      Real.sqrt Real.pi * W * b n ^ 2 - |b n| * ε ≤ ((b n : ℂ) * In n).re := by
    intro n hn
    have h := hI n hn
    have hc : (((Real.sqrt Real.pi * W : ℝ) : ℂ) * (b n : ℂ)).re = Real.sqrt Real.pi * W * b n := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h1 := (Complex.abs_re_le_norm _).trans h
    rw [Complex.sub_re, hc] at h1
    rw [Complex.re_ofReal_mul]
    have hlo : Real.sqrt Real.pi * W * b n - ε ≤ (In n).re := by
      have := neg_abs_le ((In n).re - Real.sqrt Real.pi * W * b n)
      linarith
    have hhi : (In n).re ≤ Real.sqrt Real.pi * W * b n + ε := by
      have := le_abs_self ((In n).re - Real.sqrt Real.pi * W * b n)
      linarith
    rcases le_total 0 (b n) with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · rw [abs_of_nonpos hb]; nlinarith
  have hsum : Real.sqrt Real.pi * W * ∑ n ∈ Finset.Icc 1 N, b n ^ 2 -
      ε * ∑ n ∈ Finset.Icc 1 N, |b n| ≤ (∑ n ∈ Finset.Icc 1 N, (b n : ℂ) * In n).re := by
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have := hre n hn
    linarith
  linarith

end IntegerBeurling

end

end RHTower
