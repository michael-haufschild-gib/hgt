import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepDualExpansion

/-!
# Displacement derivative on the deep reflected edge

The coupled motion

`s(d)=1/2-d+i*tau`, `w(d)=d-4+i*v`

keeps `s(d)+w(d)=-7/2+i*(tau+v)` fixed.  Consequently the derivative
contains neither `chi'` nor `log(n+1)`: only the Mellin scale and Gaussian
kernel differentiate.
-/

noncomputable section

open Complex MeasureTheory Filter Set

namespace RHTower

/-- Closed derivative of `exp(w^(2 : ℕ))/w` away from its pole. -/
def smoothAFEGaussianKernelDerivative (w : ℂ) : ℂ :=
  Complex.exp (w ^ 2) * (2 * w ^ 2 - 1) / w ^ 2

theorem hasDerivAt_smoothAFEGaussianKernel
    {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt smoothAFEGaussianKernel
      (smoothAFEGaussianKernelDerivative w) w := by
  have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
    convert (hasDerivAt_id w).pow 2 using 1
    · rfl
    · rfl
    · rfl
    · simp [id_eq]
  have hexp := (Complex.hasDerivAt_exp (w ^ 2)).comp w hsq
  have hdiv := hexp.div (hasDerivAt_id w) hw
  have hfun : ((Complex.exp ∘ fun z : ℂ => z ^ 2) / id) =
      smoothAFEGaussianKernel := by
    funext z
    rfl
  rw [hfun] at hdiv
  have hderiv :
      (Complex.exp (w ^ 2) * (2 * w) * w - Complex.exp (w ^ 2)) / w ^ 2 =
        smoothAFEGaussianKernelDerivative w := by
    unfold smoothAFEGaussianKernelDerivative
    field_simp [hw]
  simpa [hderiv] using hdiv

/-- Uniform derivative bound on a vertical line whose real part has norm at
least one. -/
theorem norm_smoothAFEGaussianKernelDerivative_vertical_le
    {sigma : ℝ} (hsigma : 1 ≤ |sigma|) (v : ℝ) :
    ‖smoothAFEGaussianKernelDerivative
        ((sigma : ℂ) + (v : ℂ) * I)‖ ≤
      3 * Real.exp (sigma ^ 2) * Real.exp (-(v ^ 2)) := by
  let w : ℂ := (sigma : ℂ) + (v : ℂ) * I
  have hwnorm : (1 : ℝ) ≤ ‖w‖ := by
    calc
      (1 : ℝ) ≤ |sigma| := hsigma
      _ = |w.re| := by simp [w]
      _ ≤ ‖w‖ := Complex.abs_re_le_norm _
  have hw0 : w ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hwnorm))
  have hpoly : ‖2 * w ^ 2 - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
    calc
      ‖2 * w ^ 2 - 1‖ ≤ ‖2 * w ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖w‖ ^ 2 + 1 := by norm_num [norm_pow]
      _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  have hsqNorm : (0 : ℝ) < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have hexp : ‖Complex.exp (w ^ 2)‖ =
      Real.exp (sigma ^ 2) * Real.exp (-(v ^ 2)) := by
    rw [Complex.norm_exp]
    have hre : (w ^ 2).re = sigma ^ 2 - v ^ 2 := by
      dsimp only [w]
      rw [pow_two]
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hre, show sigma ^ 2 - v ^ 2 = sigma ^ 2 + (-(v ^ 2)) by ring,
      Real.exp_add]
  unfold smoothAFEGaussianKernelDerivative
  rw [norm_div, norm_mul, norm_pow, show
    (((sigma : ℂ) + (v : ℂ) * I)) = w by rfl, hexp]
  calc
    (Real.exp (sigma ^ 2) * Real.exp (-(v ^ 2)) * ‖2 * w ^ 2 - 1‖) /
        ‖w‖ ^ 2
      ≤ (Real.exp (sigma ^ 2) * Real.exp (-(v ^ 2)) *
          (3 * ‖w‖ ^ 2)) / ‖w‖ ^ 2 := by
        gcongr
    _ = 3 * Real.exp (sigma ^ 2) * Real.exp (-(v ^ 2)) := by
      field_simp

/-- Exact pointwise displacement derivative of one deep reflected term. -/
def smoothAFEZetaDisplacedDeepIntegrandDerivative
    (d x tau : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  (zetaChi z * (n + 1 : ℂ) ^ (z - 1)) *
    (((x : ℂ) ^ w * Complex.log (x : ℂ)) * smoothAFEGaussianKernel w +
      (x : ℂ) ^ w * smoothAFEGaussianKernelDerivative w)

theorem hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep
    {x d : ℝ} (hx : 0 < x) (hd4 : d < 4)
    (tau : ℝ) (n : ℕ) (v : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        smoothAFEZetaReflectedTerm (displacedLinePt u tau) x n
          (((u - 4 : ℝ) : ℂ) + (v : ℂ) * I))
      (smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v) d := by
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let W : ℝ → ℂ := fun u => (((u - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hw0 : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [w] at hre
    simp at hre
    linarith
  have hW : HasDerivAt W (1 : ℂ) d := by
    have hreal := ((hasDerivAt_id d).sub_const 4).ofReal_comp
    simpa [W] using hreal.add_const ((v : ℂ) * I)
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpowC := (Complex.hasStrictDerivAt_const_cpow
    (x := (x : ℂ)) (y := w) (Or.inl hx0)).hasDerivAt
  have hpow := hpowC.comp d hW
  have hkernel := (hasDerivAt_smoothAFEGaussianKernel hw0).comp d hW
  have hprod := hpow.mul hkernel
  have hfun : (fun u : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt u tau) x n (W u)) =
      fun u : ℝ =>
        (zetaChi z * (n + 1 : ℂ) ^ (z - 1)) *
          ((x : ℂ) ^ (W u) * smoothAFEGaussianKernel (W u)) := by
    funext u
    rw [smoothAFEZetaReflectedTerm_eq_cpow,
      displacedLinePt_add_deepEdge]
    dsimp only [z]
    rw [mul_assoc]
  rw [hfun]
  dsimp only [smoothAFEZetaDisplacedDeepIntegrandDerivative]
  simpa [z, w, W, Function.comp_apply, mul_add, mul_assoc] using
    hprod.const_mul (zetaChi z * (n + 1 : ℂ) ^ (z - 1))

theorem continuous_smoothAFEZetaReflectedTerm_displaced_deep
    {x d : ℝ} (hx : 0 < x) (hd4 : d ≠ 4) (tau : ℝ) (n : ℕ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
        (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
  let W : ℝ → ℂ := fun v => (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hW : Continuous W := by dsimp only [W]; fun_prop
  let zfun : ℝ → ℂ := fun v => displacedLinePt d tau + W v
  have hzetaChi : Continuous (fun v : ℝ => zetaChi (zfun v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    apply (zetaChi_analyticAt ?_).continuousAt.comp
    · fun_prop
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      dsimp only [zfun, W]
      rw [displacedLinePt_add_deepEdge]
      simp
      norm_num
  have hpowN : Continuous (fun v : ℝ =>
      (n + 1 : ℂ) ^ (zfun v - 1)) :=
    (continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop)
  have hpowX : Continuous (fun v : ℝ => (x : ℂ) ^ (W v)) :=
    (continuous_const_cpow (x : ℂ)).comp hW
  have hW0 : ∀ v : ℝ, W v ≠ 0 := by
    intro v h
    have hre := congrArg Complex.re h
    dsimp only [W] at hre
    simp at hre
    exact hd4 (by linarith)
  have hkernel : Continuous (fun v : ℝ => smoothAFEGaussianKernel (W v)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hW.pow 2)).div hW hW0
  rw [show (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (W v)) =
    fun v => zetaChi (zfun v) * (n + 1 : ℂ) ^ (zfun v - 1) *
      (x : ℂ) ^ (W v) * smoothAFEGaussianKernel (W v) by
        funext v
        exact smoothAFEZetaReflectedTerm_eq_cpow _ _ _ _]
  exact ((hzetaChi.mul hpowN).mul hpowX).mul hkernel

theorem continuous_smoothAFEZetaDisplacedDeepIntegrandDerivative
    {x d : ℝ} (hx : 0 < x) (hd4 : d ≠ 4) (tau : ℝ) (n : ℕ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v) := by
  haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
  let Z : ℝ → ℂ := fun v =>
    (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let W : ℝ → ℂ := fun v => (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hZ : Continuous Z := by dsimp only [Z]; fun_prop
  have hW : Continuous W := by dsimp only [W]; fun_prop
  have hchi : Continuous (fun v : ℝ => zetaChi (Z v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    apply (zetaChi_analyticAt ?_).continuousAt.comp
    · exact hZ.continuousAt
    · apply Complex.Gammaℝ_ne_zero_of_re_pos
      dsimp only [Z]
      simp
      norm_num
  have hpowN : Continuous (fun v : ℝ => (n + 1 : ℂ) ^ (Z v - 1)) :=
    (continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop)
  have hpowX : Continuous (fun v : ℝ => (x : ℂ) ^ (W v)) :=
    (continuous_const_cpow (x : ℂ)).comp hW
  have hW0 : ∀ v : ℝ, W v ≠ 0 := by
    intro v h
    have hre := congrArg Complex.re h
    dsimp only [W] at hre
    simp at hre
    exact hd4 (by linarith)
  have hkernel : Continuous (fun v : ℝ => smoothAFEGaussianKernel (W v)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hW.pow 2)).div hW hW0
  have hkernel' : Continuous
      (fun v : ℝ => smoothAFEGaussianKernelDerivative (W v)) := by
    unfold smoothAFEGaussianKernelDerivative
    exact ((Complex.continuous_exp.comp (hW.pow 2)).mul
      (continuous_const.mul (hW.pow 2) |>.sub continuous_const)).div
        (hW.pow 2) (fun v => pow_ne_zero 2 (hW0 v))
  unfold smoothAFEZetaDisplacedDeepIntegrandDerivative
  change Continuous (fun v : ℝ =>
    (zetaChi (Z v) * (n + 1 : ℂ) ^ (Z v - 1)) *
      ((((x : ℂ) ^ (W v) * Complex.log (x : ℂ)) *
          smoothAFEGaussianKernel (W v)) +
        (x : ℂ) ^ (W v) * smoothAFEGaussianKernelDerivative (W v)))
  exact (hchi.mul hpowN).mul
    (((hpowX.mul continuous_const).mul hkernel).add (hpowX.mul hkernel'))

/-- Uniform pointwise envelope throughout the local displacement strip
`0 ≤ d ≤ 1/2`. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepIntegrandDerivative_le
    {x : ℝ} (hx : 0 < x) :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 →
      ∀ tau : ℝ, ∀ n : ℕ, ∀ v : ℝ,
      ‖smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖ ≤
        K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
  obtain ⟨C, N, hC, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_poly_le
  let K : ℝ := C * Real.exp (4 * |Real.log x|) * Real.exp 16 *
    (‖Complex.log (x : ℂ)‖ + 3)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, N, hK, fun d hd0 hdhalf tau n v => ?_⟩
  let z : ℂ := (((-7 / 2 : ℝ) : ℂ) + ((tau + v : ℝ) : ℂ) * I)
  let w : ℂ := (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hdAbs : (1 : ℝ) ≤ |d - 4| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdSq : (d - 4) ^ 2 ≤ 16 := by nlinarith [sq_nonneg d]
  have hchiBase := hchi (tau + v)
  have hshift : 1 + |tau + v| ≤ 1 + |tau| + |v| := by
    linarith [abs_add_le tau v]
  have hchi' : ‖zetaChi z‖ ≤ C * (1 + |tau| + |v|) ^ N := by
    dsimp only [z]
    exact hchiBase.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hshift N) hC)
  have hpowN : ‖(n + 1 : ℂ) ^ (z - 1)‖ =
      1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ) := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    have hre : (z - 1).re = -(9 / 2 : ℝ) := by
      dsimp only [z]
      simp
      norm_num
    rw [hre, Real.rpow_neg hn.le, one_div]
  have hpowX : ‖(x : ℂ) ^ w‖ ≤ Real.exp (4 * |Real.log x|) := by
    have h := norm_cpow_horizontal_arbitrary_le
      (x := x) (c := (4 : ℝ)) (u := d - 4) (v := v)
      hx (by norm_num) (by linarith) (by linarith)
    norm_num at h ⊢
    dsimp only [w]
    convert h using 1
    · push_cast
      ring
  have hkernel0 := norm_smoothAFEGaussianKernel_vertical_le_of_ne
    (σ := d - 4) (by linarith) v
  have hkernel : ‖smoothAFEGaussianKernel w‖ ≤
      Real.exp 16 * Real.exp (-(v ^ 2)) := by
    dsimp only [w]
    calc
      ‖smoothAFEGaussianKernel (↑(d - 4) + ↑v * I)‖
        ≤ Real.exp ((d - 4) ^ 2) / |d - 4| * Real.exp (-(v ^ 2)) := hkernel0
      _ ≤ Real.exp 16 * Real.exp (-(v ^ 2)) := by
        have he : Real.exp ((d - 4) ^ 2) ≤ Real.exp 16 := Real.exp_le_exp.mpr hdSq
        have hi : Real.exp ((d - 4) ^ 2) / |d - 4| ≤ Real.exp 16 := by
          rw [div_le_iff₀ (zero_lt_one.trans_le hdAbs)]
          exact he.trans (le_mul_of_one_le_right (Real.exp_pos _).le hdAbs)
        gcongr
  have hkernel'0 :=
    norm_smoothAFEGaussianKernelDerivative_vertical_le hdAbs v
  have hkernel' : ‖smoothAFEGaussianKernelDerivative w‖ ≤
      3 * Real.exp 16 * Real.exp (-(v ^ 2)) := by
    dsimp only [w]
    exact hkernel'0.trans (by gcongr)
  unfold smoothAFEZetaDisplacedDeepIntegrandDerivative
  change ‖(zetaChi z * (n + 1 : ℂ) ^ (z - 1)) *
      (((x : ℂ) ^ w * Complex.log (x : ℂ)) * smoothAFEGaussianKernel w +
        (x : ℂ) ^ w * smoothAFEGaussianKernelDerivative w)‖ ≤ _
  rw [norm_mul, norm_mul, hpowN]
  have hinner :
      ‖(x : ℂ) ^ w * Complex.log (x : ℂ) * smoothAFEGaussianKernel w +
          (x : ℂ) ^ w * smoothAFEGaussianKernelDerivative w‖ ≤
        (Real.exp (4 * |Real.log x|) * ‖Complex.log (x : ℂ)‖ *
            (Real.exp 16 * Real.exp (-(v ^ 2)))) +
          Real.exp (4 * |Real.log x|) *
            (3 * Real.exp 16 * Real.exp (-(v ^ 2))) := by
    exact (norm_add_le _ _).trans (add_le_add
      (by rw [norm_mul, norm_mul]; gcongr)
      (by rw [norm_mul]; gcongr))
  calc
    ‖zetaChi z‖ * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
        ‖(x : ℂ) ^ w * Complex.log (x : ℂ) * smoothAFEGaussianKernel w +
          (x : ℂ) ^ w * smoothAFEGaussianKernelDerivative w‖
      ≤ (C * (1 + |tau| + |v|) ^ N) *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
        ((Real.exp (4 * |Real.log x|) * ‖Complex.log (x : ℂ)‖ *
            (Real.exp 16 * Real.exp (-(v ^ 2)))) +
          Real.exp (4 * |Real.log x|) *
            (3 * Real.exp 16 * Real.exp (-(v ^ 2)))) := by
        gcongr
    _ = K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
          ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
        dsimp only [K]
        ring

/-- Normalized displacement derivative of one deep reflected coefficient. -/
def smoothAFEZetaDisplacedDeepCoefficientDerivative
    (d x tau : ℝ) (n : ℕ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ v : ℝ, smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v

theorem hasDerivAt_smoothAFEZetaDisplacedDeepCoefficient
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (tau : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedDeepCoefficient u tau x n)
      (smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) d := by
  let F : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaReflectedTerm (displacedLinePt u tau) x n
      (((u - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  let F' : ℝ → ℝ → ℂ := fun u v =>
    smoothAFEZetaDisplacedDeepIntegrandDerivative u x tau n v
  obtain ⟨K, N, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepIntegrandDerivative_le hx
  let bound : ℝ → ℝ := fun v =>
    K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) *
      ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))
  have hr : 0 < d / 2 := by positivity
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.ball d (d / 2)) (bound := bound)
    (Metric.ball_mem_nhds d hr)
    (by
      filter_upwards [Metric.ball_mem_nhds d hr] with u hu
      have hudist : |u - d| < d / 2 := by
        have h := Metric.mem_ball.mp hu
        simpa only [Real.dist_eq, abs_sub_comm] using h
      obtain ⟨hlow, hupp⟩ := abs_lt.mp hudist
      have hu4 : u ≠ 4 := by linarith
      exact (continuous_smoothAFEZetaReflectedTerm_displaced_deep
        hx hu4 tau n).aestronglyMeasurable)
    (smoothAFEZetaReflectedTerm_displaced_deep_integrable hx hd hdq tau n)
    (continuous_smoothAFEZetaDisplacedDeepIntegrandDerivative
      hx (by linarith) tau n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v u hu => by
      have hudist : |u - d| < d / 2 := by
        have h := Metric.mem_ball.mp hu
        simpa only [Real.dist_eq, abs_sub_comm] using h
      obtain ⟨hlow, hupp⟩ := abs_lt.mp hudist
      have hu0 : 0 ≤ u := by linarith
      have huhalf : u ≤ 1 / 2 := by
        linarith
      dsimp only [F', bound]
      exact hpoint u hu0 huhalf tau n v)
    (by
      have hg := integrable_shifted_pow_mul_exp_neg_sq (1 + |tau|) N
      exact hg.const_mul (K * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))))
    (Filter.Eventually.of_forall fun v u hu => by
      have hudist : |u - d| < d / 2 := by
        have h := Metric.mem_ball.mp hu
        simpa only [Real.dist_eq, abs_sub_comm] using h
      obtain ⟨hlow, hupp⟩ := abs_lt.mp hudist
      have hu4 : u < 4 := by linarith
      dsimp only [F, F']
      exact hasDerivAt_smoothAFEZetaReflectedTerm_displaced_deep
        hx hu4 tau n v)
  have hcoeffEq : (fun u : ℝ =>
      smoothAFEZetaDisplacedDeepCoefficient u tau x n) =
      fun u : ℝ => (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ v : ℝ, F u v := by
    funext u
    unfold smoothAFEZetaDisplacedDeepCoefficient
    rw [Complex.real_smul]
  rw [hcoeffEq]
  unfold smoothAFEZetaDisplacedDeepCoefficientDerivative
  exact hparam.2.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

end RHTower
