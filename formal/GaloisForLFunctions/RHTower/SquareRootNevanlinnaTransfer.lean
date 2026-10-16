import GaloisForLFunctions.RHTower.HerglotzRieszUnsymmetrized

/-!
# From a Nevanlinna function of `a²` to a Carathéodory function of `a`

Let `F` be holomorphic on `Re a > 0` with the squared-variable sign law `Im(a F(a)) ≥ 0` on the
first quadrant, real coefficients `F(ā) = conj F(a)`, and `F ≥ 0` on the positive real axis.

**Theorem** (`re_nonneg_of_sqrt_sign_law`).  `Re F(a) ≥ 0` on `Re a > 0`.

Mechanism.  For `Re s > ½` put `z = i(s − ½)` (upper half plane) and `a = √z` (principal
branch, first quadrant).  The chart `Φ(s) = −i a F(a)` is holomorphic with `Re Φ = Im(a F(a)) ≥ 0`,
so it has an unsymmetrised Herglotz–Riesz representation `Φ = ∫ K(s, ζ) dν + ic`.  In the variable
`z` the kernel is `k(z, ζ) = i K(½ − iz, ζ) = (γz − 1)/(z + γ)`, `γ = circleOrd ζ`, and
`k(z, 1) = z`: the Nevanlinna representation of `g(z) = a F(a)`.  Since `g` is holomorphic and
real on `(0, ∞)`, the Poisson support law puts `ν` on `{γ ≥ 0} ∪ {ζ = 1}`.  There the kernel is
bounded near the boundary point `½ − ix₀`, `x₀ > 0`, so `g(x₀) = ∫ k(x₀, ζ) dν − c` by dominated
convergence.  Finally, for `0 < x₀ ≤ |a|²` and `γ ≥ 0`,
`Re[(k(a², ζ) − k(x₀, ζ))/a] = (1 + γ²)/(x₀ + γ) · Re[(a² − x₀) ā (ā² + γ)] / (|a|² |a² + γ|²) ≥ 0`
because `Re[(a² − x₀) ā (ā² + γ)] = x[(|a|² + γ)(|a|² − x₀) + 4 x₀ y²]`, and
`Re[g(x₀)/a] = g(x₀) x/|a|² ≥ 0`.  Hence `Re F(a) = Re[g(a²)/a] ≥ 0` on the first quadrant; the
fourth quadrant follows by conjugation and the real axis is the hypothesis.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry

/-! ## The principal square root and the chart -/

/-- The principal square root `z^{1/2}`. -/
def sqrtQ (z : ℂ) : ℂ := z ^ ((2 : ℕ) : ℂ)⁻¹

theorem sqrtQ_pow_two (z : ℂ) : sqrtQ z ^ 2 = z := by
  simp [sqrtQ]

theorem sqrtQ_sq {a : ℂ} (ha : 0 < a.re) : sqrtQ (a ^ 2) = a := by
  have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  rw [abs_lt] at this
  have h := @Complex.pow_cpow_ofNat_inv a 2 _ (by simpa using this.1) (by simpa using this.2.le)
  simpa [sqrtQ] using h

/-- The principal square root of a point of the upper half plane lies in the first quadrant. -/
theorem sqrtQ_mem_quadrant {z : ℂ} (hz : 0 < z.im) : 0 < (sqrtQ z).re ∧ 0 < (sqrtQ z).im := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  unfold sqrtQ
  rw [Complex.cpow_def_of_ne_zero hz0]
  have harg1 : 0 < z.arg := by
    rcases (Complex.arg_nonneg_iff.mpr hz.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
  have harg2 : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have him : (Complex.log z * ((2 : ℕ) : ℂ)⁻¹).im = z.arg / 2 := by
    simp [Complex.log_im]
    ring
  constructor
  · rw [Complex.exp_re, him]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  · rw [Complex.exp_im, him]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

/-- On the positive real axis the principal square root is the real square root. -/
theorem sqrtQ_ofReal {x : ℝ} (hx : 0 ≤ x) : sqrtQ x = (Real.sqrt x : ℂ) := by
  unfold sqrtQ
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  push_cast
  norm_num

theorem differentiableAt_sqrtQ {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ sqrtQ z :=
  differentiableAt_id.cpow_const hz

theorem mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr hz.ne')

theorem mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl hz)

/-- The upper-half-plane point `z = i(s − ½)` of `s`. -/
def zPt (s : ℂ) : ℂ := I * (s - 1 / 2)

theorem im_zPt (s : ℂ) : (zPt s).im = s.re - 1 / 2 := by
  simp [zPt]

theorem zPt_half_sub (z : ℂ) : zPt (1 / 2 - I * z) = z := by
  unfold zPt
  ring_nf
  simp

theorem re_half_sub_I_mul (z : ℂ) : (1 / 2 - I * z).re = 1 / 2 + z.im := by
  simp

theorem differentiable_zPt : Differentiable ℂ zPt := by
  unfold zPt; fun_prop

/-- The squared-variable function `g(z) = √z F(√z)`. -/
def sqNev (F : ℂ → ℂ) (z : ℂ) : ℂ := sqrtQ z * F (sqrtQ z)

/-- The Carathéodory chart `Φ(s) = −i g(i(s − ½))`. -/
def oddChart (F : ℂ → ℂ) (s : ℂ) : ℂ := -I * sqNev F (zPt s)

theorem re_oddChart (F : ℂ → ℂ) (s : ℂ) : (oddChart F s).re = (sqNev F (zPt s)).im := by
  simp [oddChart]

theorem sqNev_sq {F : ℂ → ℂ} {a : ℂ} (ha : 0 < a.re) : sqNev F (a ^ 2) = a * F a := by
  simp [sqNev, sqrtQ_sq ha]

theorem differentiableAt_sqNev {F : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hFd : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ slitPlane) (hmem : sqrtQ z ∈ D) :
    DifferentiableAt ℂ (sqNev F) z := by
  have h1 := differentiableAt_sqrtQ hz
  have h2 : DifferentiableAt ℂ F (sqrtQ z) := hFd.differentiableAt (hD.mem_nhds hmem)
  exact h1.mul (h2.comp z h1)

theorem differentiableOn_oddChart {F : ℂ → ℂ}
    (hFd : DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im}) :
    DifferentiableOn ℂ (oddChart F) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hz : 0 < (zPt s).im := by rw [im_zPt]; linarith [show (1 / 2 : ℝ) < s.re from hs]
  have hQ : IsOpen {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hg := differentiableAt_sqNev hQ hFd (mem_slitPlane_of_im_pos hz) (sqrtQ_mem_quadrant hz)
  exact ((hg.comp s (differentiable_zPt s)).const_mul (-I)).differentiableWithinAt

theorem re_oddChart_nonneg {F : ℂ → ℂ}
    (hsign : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im) :
    ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (oddChart F s).re := by
  intro s hs
  have hz : 0 < (zPt s).im := by rw [im_zPt]; linarith
  obtain ⟨h1, h2⟩ := sqrtQ_mem_quadrant hz
  rw [re_oddChart]
  exact hsign _ h1 h2

/-! ## The Nevanlinna kernel in the variable `z` -/

/-- `K(s, ζ) = (1 + γ²)/(s − ½ − iγ) − iγ` whenever both denominators are nonzero. -/
theorem hrKernel_eq_of_ne {s ζ : ℂ} (hs0 : 2 * s + 1 ≠ 0) (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hden : s - 1 / 2 - circleOrd ζ * I ≠ 0) :
    hrKernel s ζ = (1 + (circleOrd ζ : ℂ) ^ 2) / (s - 1 / 2 - circleOrd ζ * I) -
      circleOrd ζ * I := by
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hu := cayleyParam_eq hζ h1
  set γ : ℝ := circleOrd ζ
  have hd : (γ : ℂ) * I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hζeq : ζ = ((γ : ℂ) * I - 1) / ((γ : ℂ) * I + 1) := by
    rw [eq_div_iff hd, ← hu]
    field_simp
    ring
  have hN : ((γ : ℂ) * I - 1) * (2 * s + 1) - ((γ : ℂ) * I + 1) * (2 * s - 3) ≠ 0 := by
    have e : ((γ : ℂ) * I - 1) * (2 * s + 1) - ((γ : ℂ) * I + 1) * (2 * s - 3) =
        -4 * (s - 1 / 2 - γ * I) := by ring
    rw [e]
    exact mul_ne_zero (by norm_num) hden
  have hstep : hrKernel s ζ = (1 - γ * I * (s - 1 / 2)) / (s - 1 / 2 - γ * I) := by
    unfold hrKernel discPt
    rw [hζeq, div_add_div _ _ hd hs0, div_sub_div _ _ hd hs0,
      div_div_div_cancel_right₀ (mul_ne_zero hd hs0), div_eq_div_iff hN hden]
    ring_nf
  rw [hstep, eq_sub_iff_add_eq, div_add' _ _ _ hden]
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- The Nevanlinna kernel `k(z, ζ) = i K(½ − iz, ζ) = (γz − 1)/(z + γ)` for `ζ ≠ 1`. -/
theorem I_mul_hrKernel_eq {z ζ : ℂ} (hs0 : 2 * (1 / 2 - I * z) + 1 ≠ 0) (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) (hzγ : z + circleOrd ζ ≠ 0) :
    I * hrKernel (1 / 2 - I * z) ζ = ((circleOrd ζ : ℂ) * z - 1) / (z + circleOrd ζ) := by
  set γ : ℝ := circleOrd ζ
  have hden : (1 / 2 - I * z) - 1 / 2 - γ * I ≠ 0 := by
    have e : (1 / 2 - I * z) - 1 / 2 - γ * I = -I * (z + γ) := by ring
    rw [e]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hzγ
  rw [hrKernel_eq_of_ne hs0 hζ h1 hden]
  have e : (1 / 2 - I * z) - 1 / 2 - γ * I = -I * (z + γ) := by ring
  rw [e]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- At `ζ = 1` the kernel is the linear term `z`. -/
theorem I_mul_hrKernel_one {z : ℂ} (hs0 : 2 * (1 / 2 - I * z) + 1 ≠ 0) :
    I * hrKernel (1 / 2 - I * z) 1 = z := by
  rw [hrKernel_one hs0]
  ring_nf
  rw [I_sq]
  ring

theorem two_mul_half_sub_add_one_ne_zero {z : ℂ} (hz : 0 ≤ z.im) :
    2 * (1 / 2 - I * z) + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-! ## Kernel positivity -/

theorem sq_add_ofReal_ne_zero {a : ℂ} (ha : 0 < a.re) {γ : ℝ} (hγ : 0 ≤ γ) :
    a ^ 2 + (γ : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at h1 h2
  have hy0 : a.im = 0 := by
    rcases mul_eq_zero.mp (show a.re * a.im = 0 by nlinarith) with h | h
    · exact absurd h ha.ne'
    · exact h
  rw [hy0] at h1
  nlinarith

/-- `Re[((γa² − 1)/(a² + γ) − (γx₀ − 1)/(x₀ + γ))/a] ≥ 0` for `γ ≥ 0`, `Re a > 0`,
`0 < x₀ ≤ |a|²`. -/
theorem re_kernel_diff_div_nonneg {a : ℂ} (ha : 0 < a.re) {γ x₀ : ℝ} (hγ : 0 ≤ γ)
    (hx0 : 0 < x₀) (hx1 : x₀ ≤ a.re ^ 2 + a.im ^ 2) :
    0 ≤ ((((γ : ℂ) * a ^ 2 - 1) / (a ^ 2 + γ) - ((γ : ℂ) * x₀ - 1) / (x₀ + γ)) / a).re := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have hd1 : a ^ 2 + (γ : ℂ) ≠ 0 := sq_add_ofReal_ne_zero ha hγ
  have hd2 : (x₀ : ℂ) + γ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have key : (((γ : ℂ) * a ^ 2 - 1) / (a ^ 2 + γ) - ((γ : ℂ) * x₀ - 1) / (x₀ + γ)) / a =
      ((1 + (γ : ℂ) ^ 2) * (a ^ 2 - x₀)) / (a * (a ^ 2 + γ) * (x₀ + γ)) := by
    field_simp
    ring
  rw [key]
  have hv : a * (a ^ 2 + γ) * (x₀ + γ) ≠ 0 := mul_ne_zero (mul_ne_zero ha0 hd1) hd2
  have hns : 0 < Complex.normSq (a * (a ^ 2 + γ) * (x₀ + γ)) := Complex.normSq_pos.mpr hv
  rw [Complex.div_re, ← add_div]
  refine div_nonneg ?_ hns.le
  set x := a.re with hx
  set y := a.im with hy
  have hid : ((1 + (γ : ℂ) ^ 2) * (a ^ 2 - x₀)).re * (a * (a ^ 2 + γ) * (x₀ + γ)).re +
      ((1 + (γ : ℂ) ^ 2) * (a ^ 2 - x₀)).im * (a * (a ^ 2 + γ) * (x₀ + γ)).im =
      (1 + γ ^ 2) * (x₀ + γ) * x *
        ((x ^ 2 + y ^ 2 + γ) * (x ^ 2 + y ^ 2 - x₀) + 4 * x₀ * y ^ 2) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      pow_two]
    rw [← hx, ← hy]
    ring
  rw [hid]
  have h1 : 0 ≤ (x ^ 2 + y ^ 2 + γ) * (x ^ 2 + y ^ 2 - x₀) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ 4 * x₀ * y ^ 2 := by positivity
  have h3 : 0 ≤ (1 + γ ^ 2) * (x₀ + γ) * x := by positivity
  exact mul_nonneg h3 (by linarith)

/-- The `ζ = 1` term: `Re[(a² − x₀)/a] ≥ 0` for `0 < x₀ ≤ |a|²`. -/
theorem re_sq_sub_div_nonneg {a : ℂ} (ha : 0 < a.re) {x₀ : ℝ}
    (hx1 : x₀ ≤ a.re ^ 2 + a.im ^ 2) : 0 ≤ ((a ^ 2 - (x₀ : ℂ)) / a).re := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have hns : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  rw [Complex.div_re, ← add_div]
  refine div_nonneg ?_ hns.le
  have hid : (a ^ 2 - (x₀ : ℂ)).re * a.re + (a ^ 2 - (x₀ : ℂ)).im * a.im =
      a.re * (a.re ^ 2 + a.im ^ 2 - x₀) := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [hid]
  exact mul_nonneg ha.le (by linarith)

/-! ## The boundary bound on the support -/

/-- On `{γ ≥ 0}` the kernel is bounded near the boundary point `½ − ix₀`:
`‖K(½ + ε − ix₀, ζ)‖ ≤ x₀ + 1 + 1/x₀` for `0 ≤ ε ≤ 1`. -/
theorem norm_hrKernel_le_of_ordinate_nonneg {x₀ ε : ℝ} (hx0 : 0 < x₀) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) (hγ : 0 ≤ circleOrd ζ) :
    ‖hrKernel ((1 / 2 : ℂ) + ε - I * x₀) ζ‖ ≤ x₀ + 1 + 1 / x₀ := by
  set γ : ℝ := circleOrd ζ
  set s : ℂ := (1 / 2 : ℂ) + ε - I * x₀ with hsdef
  have hs0 : 2 * s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hsdef] at this
    linarith
  have hden : s - 1 / 2 - γ * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hsdef] at this
    linarith
  rw [hrKernel_eq_of_ne hs0 hζ h1 hden]
  have hpos : 0 < x₀ + γ := by positivity
  have e : (1 + (γ : ℂ) ^ 2) / (s - 1 / 2 - γ * I) - γ * I =
      (1 - γ * I * (s - 1 / 2)) / (s - 1 / 2 - γ * I) := by
    rw [eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
    linear_combination (γ : ℂ) ^ 2 * I_sq
  rw [e, norm_div]
  have hnum : ‖1 - (γ : ℂ) * I * (s - 1 / 2)‖ ≤ 1 + γ * x₀ + γ * ε := by
    have hv : (1 : ℂ) - γ * I * (s - 1 / 2) = ((1 - γ * x₀ : ℝ) : ℂ) + ((-(γ * ε) : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hsdef, Complex.mul_re, Complex.mul_im]
      · simp [hsdef, Complex.mul_re, Complex.mul_im]
    rw [hv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ γ * ε)]
    have : |1 - γ * x₀| ≤ 1 + γ * x₀ := by
      rw [abs_le]; constructor <;> nlinarith [mul_nonneg hγ hx0.le]
    linarith
  have hdenl : x₀ + γ ≤ ‖s - 1 / 2 - γ * I‖ := by
    have hv : s - 1 / 2 - γ * I = ((ε : ℝ) : ℂ) + ((-(x₀ + γ) : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hsdef]
      · simp [hsdef]; ring
    rw [hv]
    have h := Complex.abs_im_le_norm (((ε : ℝ) : ℂ) + ((-(x₀ + γ) : ℝ) : ℂ) * I)
    have him : (((ε : ℝ) : ℂ) + ((-(x₀ + γ) : ℝ) : ℂ) * I).im = -(x₀ + γ) := by simp
    rw [him, abs_neg, abs_of_pos hpos] at h
    exact h
  calc ‖1 - (γ : ℂ) * I * (s - 1 / 2)‖ / ‖s - 1 / 2 - γ * I‖
      ≤ (1 + γ * x₀ + γ * ε) / (x₀ + γ) :=
        div_le_div₀ (by positivity) hnum hpos hdenl
    _ ≤ x₀ + 1 + 1 / x₀ := by
        rw [div_le_iff₀ hpos]
        have : γ * ε ≤ γ := by nlinarith
        have h2 : (x₀ + 1 + 1 / x₀) * (x₀ + γ) = x₀ ^ 2 + x₀ + 1 + γ * x₀ + γ + γ / x₀ := by
          field_simp
          ring
        rw [h2]
        have : 0 ≤ γ / x₀ := by positivity
        nlinarith

theorem norm_hrKernel_one_le {x₀ ε : ℝ} (hx0 : 0 < x₀) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖hrKernel ((1 / 2 : ℂ) + ε - I * x₀) 1‖ ≤ x₀ + 1 + 1 / x₀ := by
  have hs0 : 2 * ((1 / 2 : ℂ) + ε - I * x₀) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [hrKernel_one hs0]
  have hv : (1 / 2 : ℂ) + ε - I * x₀ - 1 / 2 = ((ε : ℝ) : ℂ) + ((-x₀ : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
  rw [hv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hε0, abs_of_pos hx0]
  have : 0 ≤ 1 / x₀ := by positivity
  linarith

/-- The point `discPt(½ − ix₀)` has ordinate `−x₀`, so it differs from every circle point with
nonnegative ordinate and from `1`. -/
theorem ne_discPt_of_ordinate_nonneg {x₀ : ℝ} (hx0 : 0 < x₀) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h : ζ = 1 ∨ 0 ≤ circleOrd ζ) : ζ - discPt (1 / 2 - I * x₀) ≠ 0 := by
  have hs0 : 2 * (1 / 2 - I * (x₀ : ℂ)) + 1 ≠ 0 :=
    two_mul_half_sub_add_one_ne_zero (by simp)
  have hb : discPt (1 / 2 - I * (x₀ : ℂ)) = bdryPt (-x₀) := by
    unfold bdryPt
    congr 1
    push_cast
    ring
  intro hzero
  have hζd : ζ = discPt (1 / 2 - I * x₀) := sub_eq_zero.mp hzero
  have hnot1 : ζ ≠ 1 := by
    intro h1
    rw [h1] at hζd
    have := congrArg halfPt hζd
    rw [halfPt_discPt hs0] at this
    have him := congrArg Complex.im this
    simp [halfPt] at him
    linarith
  rcases h with h1 | hγ
  · exact hnot1 h1
  · have hbζ := eq_bdryPt_circleOrd hζ hnot1
    rw [hb] at hζd
    unfold bdryPt at hζd hbζ
    have hinj := congrArg halfPt (hbζ.symm.trans hζd)
    rw [halfPt_discPt (bdry_two_mul_add_one_ne_zero _),
      halfPt_discPt (bdry_two_mul_add_one_ne_zero _)] at hinj
    have := congrArg Complex.im hinj
    simp at this
    linarith

/-! ## The transfer theorem -/

/-- **Square-root transfer.**  Let `F` be holomorphic on `Re a > 0` with `Im(a F(a)) ≥ 0` on the
first quadrant, `F(ā) = conj F(a)`, and `Re F ≥ 0` on the positive real axis.  Then `Re F ≥ 0` on
the whole right half-plane. -/
theorem re_nonneg_of_sqrt_sign_law {F : ℂ → ℂ}
    (hFd : DifferentiableOn ℂ F {a : ℂ | 0 < a.re})
    (hsign : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im)
    (hconj : ∀ a : ℂ, 0 < a.re → F (conj a) = conj (F a))
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ (F x).re) :
    ∀ a : ℂ, 0 < a.re → 0 ≤ (F a).re := by
  have hH : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFQ : DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} :=
    hFd.mono fun a ha => ha.1
  have hreal : ∀ x : ℝ, 0 < x → (F x).im = 0 := by
    intro x hx
    have h := hconj x (by simpa using hx)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  -- the Herglotz–Riesz data of the chart
  obtain ⟨ν, hfin, hpois, c, hrep⟩ :=
    exists_hrKernel_representation (differentiableOn_oddChart hFQ) (re_oddChart_nonneg hsign)
  -- continuity of `g` on the positive real axis
  have hgcont : ∀ x : ℝ, 0 < x → ContinuousAt (sqNev F) (x : ℂ) := by
    intro x hx
    have hmem : sqrtQ (x : ℂ) ∈ {a : ℂ | 0 < a.re} := by
      rw [sqrtQ_ofReal hx.le]
      simpa using Real.sqrt_pos.mpr hx
    exact (differentiableAt_sqNev hH hFd (mem_slitPlane_of_re_pos (by simpa using hx))
      hmem).continuousAt
  have hgreal : ∀ x : ℝ, 0 < x → (sqNev F x).im = 0 := by
    intro x hx
    unfold sqNev
    rw [sqrtQ_ofReal hx.le, Complex.im_ofReal_mul, hreal _ (Real.sqrt_pos.mpr hx), mul_zero]
  -- Poisson support: no mass on negative ordinates
  have hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (0 : ℝ)} = 0 := by
    refine measure_ordinate_open_eq_zero_of_poisson hpois isOpen_Iio fun t ht => ?_
    have ht' : 0 < -t := by simpa using ht
    have hz : zPt ((1 / 2 : ℂ) + t * I) = ((-t : ℝ) : ℂ) := by
      unfold zPt
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hcont : ContinuousAt (fun s => (oddChart F s).re) ((1 / 2 : ℂ) + t * I) := by
      simp only [re_oddChart]
      have hg : ContinuousAt (sqNev F) (zPt ((1 / 2 : ℂ) + t * I)) := by
        rw [hz]
        exact hgcont _ ht'
      exact Complex.continuous_im.continuousAt.comp
        (hg.comp differentiable_zPt.continuous.continuousAt)
    have hval : (oddChart F ((1 / 2 : ℂ) + t * I)).re = 0 := by
      rw [re_oddChart, hz]
      exact hgreal _ ht'
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ 0 ≤ angleOrd θ := by
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) hsupp
    simp only [Set.mem_setOf_eq, not_or, not_le] at hθ
    exact ⟨hθ.1, hθ.2⟩
  -- interior representation of `g(a²)`
  have hint : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * F a = (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c := by
    intro a ha hai
    have hs : 1 / 2 < (1 / 2 - I * a ^ 2).re := by
      rw [re_half_sub_I_mul]
      have : 0 < (a ^ 2).im := by simp [pow_two, Complex.mul_im]; positivity
      linarith
    have h := hrep _ hs
    rw [oddChart, zPt_half_sub, sqNev_sq ha] at h
    rw [integral_const_mul]
    have : a * F a = I * (-I * (a * F a)) := by ring_nf; rw [I_sq]; ring
    rw [this, h]
    ring_nf
    rw [I_sq]
    ring
  -- boundary representation of `g(x₀)`
  have hbdry : ∀ x₀ : ℝ, 0 < x₀ →
      Integrable (fun θ => hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) ν ∧
      sqNev F x₀ = (∫ θ, I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ) ∂ν) - c := by
    intro x₀ hx0
    set s₀ : ℂ := 1 / 2 - I * x₀ with hs₀
    set sn : ℕ → ℂ := fun n => (1 / 2 : ℂ) + (1 / ((n : ℝ) + 1) : ℝ) - I * x₀ with hsn
    have hsn_re : ∀ n, 1 / 2 < (sn n).re := by
      intro n
      have h : (sn n).re = 1 / 2 + 1 / ((n : ℝ) + 1) := by
        simp only [hsn, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        norm_num
      rw [h]
      linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
    have hsn_lim : Tendsto sn atTop (𝓝 s₀) := by
      have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((tendsto_const_nhds (x := (1 / 2 : ℂ))).add h1).sub
        (tendsto_const_nhds (x := I * (x₀ : ℂ)))
      simp only [Complex.ofReal_zero, add_zero] at this
      exact this
    have hε : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
      ⟨by positivity, by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
    set B : ℝ := x₀ + 1 + 1 / x₀ with hB
    -- uniform bound on the support
    have hbound : ∀ n, ∀ᵐ θ ∂ν, ‖hrKernel (sn n) (circleMap 0 1 θ)‖ ≤ B := by
      intro n
      filter_upwards [hae] with θ hθ
      have hζ := norm_circleMap_one θ
      rcases hθ with h1 | hγ
      · rw [h1]
        exact norm_hrKernel_one_le hx0 (hε n).1 (hε n).2
      · by_cases h1 : circleMap 0 1 θ = 1
        · rw [h1]
          exact norm_hrKernel_one_le hx0 (hε n).1 (hε n).2
        · exact norm_hrKernel_le_of_ordinate_nonneg hx0 (hε n).1 (hε n).2 hζ h1 hγ
    -- pointwise convergence on the support
    have hlim : ∀ᵐ θ ∂ν, Tendsto (fun n => hrKernel (sn n) (circleMap 0 1 θ)) atTop
        (𝓝 (hrKernel s₀ (circleMap 0 1 θ))) := by
      filter_upwards [hae] with θ hθ
      have hζ := norm_circleMap_one θ
      have hne : circleMap 0 1 θ - discPt s₀ ≠ 0 := ne_discPt_of_ordinate_nonneg hx0 hζ hθ
      have hs0 : 2 * s₀ + 1 ≠ 0 := two_mul_half_sub_add_one_ne_zero (by simp)
      have hd : ContinuousAt discPt s₀ := by
        have heq : discPt = fun z : ℂ => (2 * z - 3) / (2 * z + 1) := rfl
        rw [heq]
        exact ((continuous_const.mul continuous_id).sub continuous_const).continuousAt.div
          ((continuous_const.mul continuous_id).add continuous_const).continuousAt hs0
      have hk : ContinuousAt (fun w => (circleMap 0 1 θ + w) / (circleMap 0 1 θ - w))
          (discPt s₀) :=
        (continuous_const.add continuous_id).continuousAt.div
          (continuous_const.sub continuous_id).continuousAt hne
      have := (hk.comp hd).tendsto.comp hsn_lim
      exact this
    have hmeas : ∀ n, AEStronglyMeasurable (fun θ => hrKernel (sn n) (circleMap 0 1 θ)) ν :=
      fun n => (integrable_hrDisk (ν := ν) (norm_discPt_lt_one (hsn_re n))).1
    have hlimint : Tendsto (fun n => ∫ θ, hrKernel (sn n) (circleMap 0 1 θ) ∂ν) atTop
        (𝓝 (∫ θ, hrKernel s₀ (circleMap 0 1 θ) ∂ν)) :=
      tendsto_integral_of_dominated_convergence (fun _ => B) hmeas (integrable_const B)
        hbound hlim
    have hintg : Integrable (fun θ => hrKernel s₀ (circleMap 0 1 θ)) ν := by
      refine Integrable.mono' (integrable_const B)
        (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) ?_
      filter_upwards [hae] with θ hθ
      have hζ := norm_circleMap_one θ
      have hs₀' : s₀ = (1 / 2 : ℂ) + ((0 : ℝ) : ℂ) - I * x₀ := by rw [hs₀]; simp
      rw [hs₀', hB]
      rcases hθ with h1 | hγ
      · rw [h1]
        exact norm_hrKernel_one_le hx0 (le_refl (0 : ℝ)) zero_le_one
      · by_cases h1 : circleMap 0 1 θ = 1
        · rw [h1]
          exact norm_hrKernel_one_le hx0 (le_refl (0 : ℝ)) zero_le_one
        · exact norm_hrKernel_le_of_ordinate_nonneg hx0 (le_refl (0 : ℝ)) zero_le_one hζ h1 hγ
    refine ⟨hintg, ?_⟩
    -- the chart values converge
    have hz₀ : zPt s₀ = (x₀ : ℂ) := zPt_half_sub _
    have hchart : Tendsto (fun n => oddChart F (sn n)) atTop (𝓝 (oddChart F s₀)) := by
      have hc : ContinuousAt (oddChart F) s₀ := by
        unfold oddChart
        have hg : ContinuousAt (sqNev F) (zPt s₀) := by
          rw [hz₀]
          exact hgcont x₀ hx0
        exact continuousAt_const.mul (hg.comp differentiable_zPt.continuous.continuousAt)
      exact hc.tendsto.comp hsn_lim
    have hchart' : Tendsto (fun n => oddChart F (sn n)) atTop
        (𝓝 ((∫ θ, hrKernel s₀ (circleMap 0 1 θ) ∂ν) + c * I)) := by
      refine (hlimint.add tendsto_const_nhds).congr fun n => ?_
      exact (hrep (sn n) (hsn_re n)).symm
    have heq := tendsto_nhds_unique hchart hchart'
    rw [oddChart, hz₀] at heq
    rw [integral_const_mul]
    have : sqNev F x₀ = I * (-I * sqNev F x₀) := by ring_nf; rw [I_sq]; ring
    rw [this, heq]
    ring_nf
    rw [I_sq]
    ring
  -- the main inequality on the first quadrant
  have hQ1 : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (F a).re := by
    intro a ha hai
    have ha0 : a ≠ 0 := by
      intro h; rw [h] at ha; simp at ha
    set x₀ : ℝ := a.re ^ 2 + a.im ^ 2 with hx₀
    have hx0 : 0 < x₀ := by positivity
    obtain ⟨hintg, hb⟩ := hbdry x₀ hx0
    have hi := hint a ha hai
    have hs1 : 1 / 2 < (1 / 2 - I * a ^ 2).re := by
      rw [re_half_sub_I_mul]
      have : 0 < (a ^ 2).im := by simp [pow_two, Complex.mul_im]; positivity
      linarith
    have hinta : Integrable (fun θ => hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ)) ν :=
      integrable_hrDisk (norm_discPt_lt_one hs1)
    -- `F a = g(a²)/a = g(x₀)/a + ∫ (k(a², ζ) − k(x₀, ζ))/a dν`
    have hFa : F a = sqNev F x₀ / a +
        ∫ θ, (I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) -
          I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) / a ∂ν := by
      rw [integral_div, integral_sub (hinta.const_mul I) (hintg.const_mul I)]
      have : F a = (a * F a) / a := by field_simp
      rw [this, hi, hb]
      ring
    have hg0 : 0 ≤ (sqNev F x₀ / a).re := by
      have hgr : (sqNev F x₀).im = 0 := hgreal x₀ hx0
      have hgn : 0 ≤ (sqNev F x₀).re := by
        unfold sqNev
        rw [sqrtQ_ofReal hx0.le, Complex.re_ofReal_mul]
        exact mul_nonneg (Real.sqrt_nonneg _) (hpos _ (Real.sqrt_pos.mpr hx0))
      rw [Complex.div_re, hgr, zero_mul, zero_div, add_zero]
      exact div_nonneg (mul_nonneg hgn ha.le) (Complex.normSq_nonneg a)
    have hker : 0 ≤ (∫ θ, (I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) -
          I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) / a ∂ν).re := by
      have hI : Integrable (fun θ => (I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) -
          I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) / a) ν :=
        ((hinta.const_mul I).sub (hintg.const_mul I)).div_const a
      have hre : (∫ θ, (I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) -
          I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) / a ∂ν).re =
          ∫ θ, ((I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) -
          I * hrKernel (1 / 2 - I * x₀) (circleMap 0 1 θ)) / a).re ∂ν :=
        (integral_re hI).symm
      rw [hre]
      refine integral_nonneg_of_ae ?_
      filter_upwards [hae] with θ hθ
      have hζ := norm_circleMap_one θ
      have hs0a : 2 * (1 / 2 - I * a ^ 2) + 1 ≠ 0 :=
        two_mul_half_sub_add_one_ne_zero (by simp [pow_two, Complex.mul_im]; positivity)
      have hs0x : 2 * (1 / 2 - I * (x₀ : ℂ)) + 1 ≠ 0 :=
        two_mul_half_sub_add_one_ne_zero (by simp)
      by_cases h1 : circleMap 0 1 θ = 1
      · rw [h1, I_mul_hrKernel_one hs0a, I_mul_hrKernel_one hs0x]
        exact re_sq_sub_div_nonneg ha (le_of_eq hx₀)
      · have hγ : 0 ≤ circleOrd (circleMap 0 1 θ) := hθ.resolve_left h1
        have hza : a ^ 2 + (circleOrd (circleMap 0 1 θ) : ℂ) ≠ 0 := sq_add_ofReal_ne_zero ha hγ
        have hzx : (x₀ : ℂ) + (circleOrd (circleMap 0 1 θ) : ℂ) ≠ 0 := by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith
        rw [I_mul_hrKernel_eq hs0a hζ h1 hza, I_mul_hrKernel_eq hs0x hζ h1 hzx]
        exact re_kernel_diff_div_nonneg ha hγ hx0 (le_of_eq hx₀)
    rw [hFa, Complex.add_re]
    exact add_nonneg hg0 hker
  -- all of the right half-plane
  intro a ha
  rcases lt_trichotomy 0 a.im with hai | hai | hai
  · exact hQ1 a ha hai
  · have hx : a = ((a.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hai]
    rw [hx]
    exact hpos _ ha
  · have hc : 0 < (conj a).im := by simpa using hai
    have hcr : 0 < (conj a).re := by simpa using ha
    have h := hQ1 (conj a) hcr hc
    rw [hconj a ha, Complex.conj_re] at h
    exact h

end RHTower.AtomDomination
