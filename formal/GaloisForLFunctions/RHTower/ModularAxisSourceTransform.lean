import Mathlib

/-!
# Even sources and entire transforms from the weight-`½` inversion law

For `F` holomorphic on the upper half-plane with `F(i e^{-2x}) = e^{x} F(i e^{2x})` and cusp decay
`‖F τ - c‖ ≤ M e^{-π im τ}` (`im τ ≥ 1`), put `T(x) = e^{x/2}(F(ie^{2x}) - c)/2` and
`k_F = T'' - T/4 = e^{x/2}(3pF'(p) + 2p²F''(p))`, `p = ie^{2x}`.  Then `k_F` is even, continuous,
beats every exponential weight, and `Ξ_F(w) = ∫ e^{-iwx} k_F(x) dx` is entire and even.  For
`F = θ₃` this is the theta source of `ξ`.
-/

open Complex MeasureTheory Filter Topology
open scoped Real

namespace RHTower

noncomputable section

/-- The open upper half-plane as a subset of `ℂ`. -/
def modUpperSet : Set ℂ := {τ : ℂ | 0 < τ.im}

theorem isOpen_modUpperSet : IsOpen modUpperSet :=
  isOpen_lt continuous_const Complex.continuous_im

/-- The imaginary-axis point `i·e^{2x}`. -/
def modAxisPoint (x : ℝ) : ℂ := I * (Real.exp (2 * x) : ℂ)

theorem modAxisPoint_im (x : ℝ) : (modAxisPoint x).im = Real.exp (2 * x) := by
  simp only [modAxisPoint, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem modAxisPoint_mem (x : ℝ) : modAxisPoint x ∈ modUpperSet := by
  show 0 < (modAxisPoint x).im
  rw [modAxisPoint_im]; exact Real.exp_pos _

theorem hasDerivAt_modAxisPoint (x : ℝ) :
    HasDerivAt modAxisPoint (2 * modAxisPoint x) x := by
  unfold modAxisPoint
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 := (Real.hasDerivAt_exp (2 * x)).comp x h1
  have h3 := (h2.ofReal_comp).const_mul I
  refine h3.congr_deriv ?_
  push_cast; ring

/-- Elementary reflection mode `(e^{x/2}-e^{-x/2})/2`, complexified. -/
def modReflectionMode (x : ℝ) : ℂ := ((Real.exp (x / 2) - Real.exp (-x / 2)) / 2 : ℝ)

def modReflectionModeDeriv (x : ℝ) : ℂ := ((Real.exp (x / 2) + Real.exp (-x / 2)) / 4 : ℝ)

theorem hasDerivAt_modReflectionMode (x : ℝ) :
    HasDerivAt modReflectionMode (modReflectionModeDeriv x) x := by
  unfold modReflectionMode modReflectionModeDeriv
  have hraw := (((Real.hasDerivAt_exp (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).sub
      ((Real.hasDerivAt_exp (-x / 2)).comp x
        (((hasDerivAt_id x).neg).div_const 2))).div_const 2
  have h := hraw.ofReal_comp
  convert h using 1
  · funext y; simp
  · push_cast; ring

theorem hasDerivAt_modReflectionModeDeriv (x : ℝ) :
    HasDerivAt modReflectionModeDeriv ((1 / 4 : ℂ) * modReflectionMode x) x := by
  unfold modReflectionMode modReflectionModeDeriv
  have hraw := (((Real.hasDerivAt_exp (x / 2)).comp x
    ((hasDerivAt_id x).div_const 2)).add
      ((Real.hasDerivAt_exp (-x / 2)).comp x
        (((hasDerivAt_id x).neg).div_const 2))).div_const 4
  have h := hraw.ofReal_comp
  convert h using 1
  · funext y; simp
  · push_cast; ring

variable (F : ℂ → ℂ) (c : ℂ)

/-- Tail `T(x) = e^{x/2}(F(ie^{2x}) - c)/2`. -/
def modTail (x : ℝ) : ℂ := (Real.exp (x / 2) : ℂ) * (F (modAxisPoint x) - c) / 2

/-- Its first derivative. -/
def modTailDeriv (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) *
    ((F (modAxisPoint x) - c) / 2 + 2 * modAxisPoint x * deriv F (modAxisPoint x)) / 2

/-- Its second derivative. -/
def modTailDeriv2 (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) *
    ((F (modAxisPoint x) - c) / 4 + 6 * modAxisPoint x * deriv F (modAxisPoint x) +
      4 * modAxisPoint x ^ 2 * deriv (deriv F) (modAxisPoint x)) / 2

/-- The source `k_F = T'' - T/4 = e^{x/2}(3pF'(p) + 2p²F''(p))`, `p = ie^{2x}`. -/
def modSource (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) *
    (3 * modAxisPoint x * deriv F (modAxisPoint x) +
      2 * modAxisPoint x ^ 2 * deriv (deriv F) (modAxisPoint x))

theorem modSource_eq (x : ℝ) : modSource F x = modTailDeriv2 F c x - modTail F c x / 4 := by
  unfold modSource modTailDeriv2 modTail; ring

variable {F}

theorem hasDerivAt_exp_half_complex (x : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.exp (x / 2) : ℂ)) ((Real.exp (x / 2) : ℂ) / 2) x := by
  have h := ((Real.hasDerivAt_exp (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).ofReal_comp
  convert h using 1
  · funext y; simp [Function.comp_def]
  · push_cast; ring

theorem hasDerivAt_modTail (hF : DifferentiableOn ℂ F modUpperSet) (x : ℝ) :
    HasDerivAt (modTail F c) (modTailDeriv F c x) x := by
  have hp := modAxisPoint_mem x
  have hFd : HasDerivAt F (deriv F (modAxisPoint x)) (modAxisPoint x) :=
    ((hF _ hp).differentiableAt (isOpen_modUpperSet.mem_nhds hp)).hasDerivAt
  have hcomp : HasDerivAt (fun x => F (modAxisPoint x))
      (deriv F (modAxisPoint x) * (2 * modAxisPoint x)) x :=
    hFd.comp x (hasDerivAt_modAxisPoint x)
  have h := ((hasDerivAt_exp_half_complex x).mul (hcomp.sub_const c)).div_const 2
  refine h.congr_deriv ?_
  unfold modTailDeriv
  ring

theorem hasDerivAt_modTailDeriv (hF : DifferentiableOn ℂ F modUpperSet) (x : ℝ) :
    HasDerivAt (modTailDeriv F c) (modTailDeriv2 F c x) x := by
  have hp := modAxisPoint_mem x
  have hnhds := isOpen_modUpperSet.mem_nhds hp
  have hF' : DifferentiableOn ℂ (deriv F) modUpperSet := hF.deriv isOpen_modUpperSet
  have hFd : HasDerivAt F (deriv F (modAxisPoint x)) (modAxisPoint x) :=
    ((hF _ hp).differentiableAt hnhds).hasDerivAt
  have hFd' : HasDerivAt (deriv F) (deriv (deriv F) (modAxisPoint x)) (modAxisPoint x) :=
    ((hF' _ hp).differentiableAt hnhds).hasDerivAt
  have hc1 : HasDerivAt (fun x => F (modAxisPoint x))
      (deriv F (modAxisPoint x) * (2 * modAxisPoint x)) x :=
    hFd.comp x (hasDerivAt_modAxisPoint x)
  have hc2 : HasDerivAt (fun x => deriv F (modAxisPoint x))
      (deriv (deriv F) (modAxisPoint x) * (2 * modAxisPoint x)) x :=
    hFd'.comp x (hasDerivAt_modAxisPoint x)
  have hq : HasDerivAt (fun x => 2 * modAxisPoint x * deriv F (modAxisPoint x))
      (2 * (2 * modAxisPoint x) * deriv F (modAxisPoint x) +
        2 * modAxisPoint x * (deriv (deriv F) (modAxisPoint x) * (2 * modAxisPoint x))) x :=
    ((hasDerivAt_modAxisPoint x).const_mul 2).mul hc2
  have hinner := (hc1.sub_const c).div_const 2 |>.add hq
  have h := ((hasDerivAt_exp_half_complex x).mul hinner).div_const 2
  refine h.congr_deriv ?_
  unfold modTailDeriv2
  simp only [Pi.add_apply]
  ring

/-- **Reflection of the tail.**  The weight-`½` inversion law on the imaginary axis leaves only the
elementary mode. -/
theorem modTail_neg (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (x : ℝ) : modTail F c (-x) = modTail F c x + c * modReflectionMode x := by
  unfold modTail modReflectionMode
  rw [hS x]
  push_cast
  have he : Complex.exp (-(x : ℂ) / 2) * Complex.exp (x : ℂ) = Complex.exp ((x : ℂ) / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (F (modAxisPoint x) / 2) * he

/-- **Evenness of the source.** -/
theorem modSource_neg (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x)) (x : ℝ) :
    modSource F (-x) = modSource F x := by
  have hrefl : modTail F 0 ∘ Neg.neg = fun y => modTail F 0 y + (0:ℂ) * modReflectionMode y := by
    funext y; exact modTail_neg 0 hS y
  have hfirst (y : ℝ) :
      -modTailDeriv F 0 (-y) = modTailDeriv F 0 y + (0:ℂ) * modReflectionModeDeriv y := by
    have hl := (hasDerivAt_modTail 0 hF (-y)).scomp y (hasDerivAt_neg y)
    have hr := (hasDerivAt_modTail 0 hF y).add ((hasDerivAt_modReflectionMode y).const_mul (0:ℂ))
    rw [hrefl] at hl
    have := hl.unique hr
    simp only [neg_smul, one_smul] at this
    simpa using this
  have hfirstFun : (fun y => -modTailDeriv F 0 (-y)) =
      fun y => modTailDeriv F 0 y + (0:ℂ) * modReflectionModeDeriv y := funext hfirst
  have hsecond : modTailDeriv2 F 0 (-x) =
      modTailDeriv2 F 0 x + (0:ℂ) * ((1 / 4 : ℂ) * modReflectionMode x) := by
    have hl := ((hasDerivAt_modTailDeriv 0 hF (-x)).scomp x (hasDerivAt_neg x)).neg
    have hr := (hasDerivAt_modTailDeriv 0 hF x).add
      ((hasDerivAt_modReflectionModeDeriv x).const_mul (0:ℂ))
    have hl' : HasDerivAt (fun y => -modTailDeriv F 0 (-y))
        (modTailDeriv2 F 0 (-x)) x := by
      have h0 := hl
      simp only [Function.comp_def, neg_smul, one_smul, neg_neg] at h0
      exact h0
    rw [hfirstFun] at hl'
    have := hl'.unique hr
    linear_combination this
  rw [modSource_eq F 0, modSource_eq F 0, hsecond, modTail_neg 0 hS]
  ring


/-! ## Cusp decay transfers to the source -/

section Decay

variable {F : ℂ → ℂ} {c : ℂ} {M : ℝ}

theorem modUpper_closedBall_subset {τ : ℂ} (hτ : 1 ≤ τ.im) :
    Metric.closedBall τ (1 / 2) ⊆ modUpperSet := by
  intro z hz
  have h := Complex.abs_im_le_norm (z - τ)
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  show 0 < z.im
  have : |z.im - τ.im| ≤ 1 / 2 := by
    have := h.trans hz; simpa [Complex.sub_im] using this
  linarith [(abs_le.mp this).1]

theorem im_ge_of_mem_sphere_half {τ z : ℂ} (hz : z ∈ Metric.sphere τ (1 / 2)) :
    τ.im - 1 / 2 ≤ z.im := by
  have h := Complex.abs_im_le_norm (z - τ)
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have : |z.im - τ.im| ≤ 1 / 2 := by
    rw [hz] at h; simpa [Complex.sub_im] using h
  linarith [(abs_le.mp this).1]

theorem cuspDecay_const_nonneg
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im)) : 0 ≤ M := by
  by_contra h
  have h := not_le.mp h
  have h1 := hdec I (by simp)
  have h2 := norm_nonneg (F I - c)
  have h3 := Real.exp_pos (-π * I.im)
  nlinarith

theorem norm_deriv_le_of_cuspDecay (hF : DifferentiableOn ℂ F modUpperSet)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im))
    {τ : ℂ} (hτ : 2 ≤ τ.im) :
    ‖deriv F τ‖ ≤ 2 * M * Real.exp (π / 2) * Real.exp (-π * τ.im) := by
  have hM := cuspDecay_const_nonneg hdec
  have hball : Metric.closedBall τ (1 / 2) ⊆ modUpperSet :=
    modUpper_closedBall_subset (by linarith)
  have hd : DiffContOnCl ℂ (fun z => F z - c) (Metric.ball τ (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball τ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact (hF.mono hball).sub_const c
  have hC : ∀ z ∈ Metric.sphere τ (1 / 2),
      ‖(fun z => F z - c) z‖ ≤ M * Real.exp (π / 2) * Real.exp (-π * τ.im) := by
    intro z hz
    have hz' := im_ge_of_mem_sphere_half hz
    refine (hdec z (by linarith)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hM
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2) hd hC
  have hderiv : deriv (fun z => F z - c) τ = deriv F τ := deriv_sub_const c
  rw [hderiv] at h
  calc ‖deriv F τ‖ ≤ M * Real.exp (π / 2) * Real.exp (-π * τ.im) / (1 / 2) := h
    _ = 2 * M * Real.exp (π / 2) * Real.exp (-π * τ.im) := by ring

theorem norm_deriv_deriv_le_of_cuspDecay (hF : DifferentiableOn ℂ F modUpperSet)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im))
    {τ : ℂ} (hτ : 3 ≤ τ.im) :
    ‖deriv (deriv F) τ‖ ≤ 4 * M * Real.exp π * Real.exp (-π * τ.im) := by
  have hM := cuspDecay_const_nonneg hdec
  have hF' : DifferentiableOn ℂ (deriv F) modUpperSet := hF.deriv isOpen_modUpperSet
  have hball : Metric.closedBall τ (1 / 2) ⊆ modUpperSet :=
    modUpper_closedBall_subset (by linarith)
  have hd : DiffContOnCl ℂ (deriv F) (Metric.ball τ (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball τ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact hF'.mono hball
  have hC : ∀ z ∈ Metric.sphere τ (1 / 2),
      ‖deriv F z‖ ≤ 2 * M * Real.exp π * Real.exp (-π * τ.im) := by
    intro z hz
    have hz' := im_ge_of_mem_sphere_half hz
    refine (norm_deriv_le_of_cuspDecay hF hdec (by linarith)).trans ?_
    have hexp : Real.exp (π / 2) * Real.exp (-π * z.im) ≤
        Real.exp π * Real.exp (-π * τ.im) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    calc 2 * M * Real.exp (π / 2) * Real.exp (-π * z.im)
        = 2 * M * (Real.exp (π / 2) * Real.exp (-π * z.im)) := by ring
      _ ≤ 2 * M * (Real.exp π * Real.exp (-π * τ.im)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2 * M * Real.exp π * Real.exp (-π * τ.im) := by ring
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2) hd hC
  calc ‖deriv (deriv F) τ‖ ≤ 2 * M * Real.exp π * Real.exp (-π * τ.im) / (1 / 2) := h
    _ = 4 * M * Real.exp π * Real.exp (-π * τ.im) := by ring

theorem norm_modAxisPoint (x : ℝ) : ‖modAxisPoint x‖ = Real.exp (2 * x) := by
  rw [modAxisPoint, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem norm_modSource_le_of_cuspDecay (hF : DifferentiableOn ℂ F modUpperSet)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im))
    {x : ℝ} (hx : 3 ≤ Real.exp (2 * x)) :
    ‖modSource F x‖ ≤ 4 * M * Real.exp π * Real.exp (x / 2) *
      (3 * Real.exp (2 * x) + 2 * Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)) := by
  have hM := cuspDecay_const_nonneg hdec
  set y := Real.exp (2 * x) with hy
  have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
  have h1 := norm_deriv_le_of_cuspDecay hF hdec (τ := modAxisPoint x) (by rw [hpim]; linarith)
  have h2 := norm_deriv_deriv_le_of_cuspDecay hF hdec (τ := modAxisPoint x) (by rw [hpim]; linarith)
  rw [hpim] at h1 h2
  have hK : 2 * M * Real.exp (π / 2) ≤ 4 * M * Real.exp π := by
    have : Real.exp (π / 2) ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
    nlinarith [Real.exp_pos (π / 2)]
  have h1' : ‖deriv F (modAxisPoint x)‖ ≤ 4 * M * Real.exp π * Real.exp (-π * y) :=
    h1.trans (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le)
  unfold modSource
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hsum : ‖3 * modAxisPoint x * deriv F (modAxisPoint x) +
      2 * modAxisPoint x ^ 2 * deriv (deriv F) (modAxisPoint x)‖ ≤
      (3 * y + 2 * y ^ 2) * (4 * M * Real.exp π * Real.exp (-π * y)) := by
    refine (norm_add_le _ _).trans ?_
    have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [norm_mul, norm_pow, norm_modAxisPoint, e3, e2, ← hy]
    have hA := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ 3 * y)
    have hB := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * y ^ 2)
    nlinarith [hA, hB]
  calc Real.exp (x / 2) * ‖3 * modAxisPoint x * deriv F (modAxisPoint x) +
        2 * modAxisPoint x ^ 2 * deriv (deriv F) (modAxisPoint x)‖
      ≤ Real.exp (x / 2) * ((3 * y + 2 * y ^ 2) * (4 * M * Real.exp π * Real.exp (-π * y))) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = 4 * M * Real.exp π * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := by
        ring

theorem continuous_modSource (hF : DifferentiableOn ℂ F modUpperSet) :
    Continuous (modSource F) := by
  have hF' : DifferentiableOn ℂ (deriv F) modUpperSet := hF.deriv isOpen_modUpperSet
  have hF'' : DifferentiableOn ℂ (deriv (deriv F)) modUpperSet :=
    hF'.deriv isOpen_modUpperSet
  have hp : Continuous modAxisPoint := by
    unfold modAxisPoint; fun_prop
  have hmaps : ∀ x, modAxisPoint x ∈ modUpperSet := modAxisPoint_mem
  have c1 : Continuous (fun x => deriv F (modAxisPoint x)) :=
    hF'.continuousOn.comp_continuous hp hmaps
  have c2 : Continuous (fun x => deriv (deriv F) (modAxisPoint x)) :=
    hF''.continuousOn.comp_continuous hp hmaps
  unfold modSource
  fun_prop

/-- Every exponential weight is beaten by the source. -/
theorem exists_norm_modSource_le_exp (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖modSource F x‖ ≤ C * Real.exp (-(B * |x|)) := by
  have hM := cuspDecay_const_nonneg hdec
  set x₀ : ℝ := Real.log 3 / 2 with hx₀
  have hx₀pos : 0 ≤ x₀ := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  set K : ℝ := 4 * M * Real.exp π with hK
  have hK0 : 0 ≤ K := by positivity
  -- far region
  have hfar : ∀ x : ℝ, x₀ ≤ x →
      ‖modSource F x‖ ≤ 5 * K * ((N + 2).factorial : ℝ) * Real.exp (-(B * x)) := by
    intro x hx
    have hx0 : 0 ≤ x := hx₀pos.trans hx
    set y := Real.exp (2 * x) with hy
    have hy3 : 3 ≤ y := by
      have : Real.exp (2 * x₀) = 3 := by
        rw [hx₀, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
      rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
    have hy1 : 1 ≤ y := by linarith
    have hbound := norm_modSource_le_of_cuspDecay hF hdec (x := x) hy3
    rw [← hy] at hbound
    -- e^{(B+1/2)x} ≤ y^N
    have hBN : B + 1 / 2 ≤ 2 * (N : ℝ) := by
      have := Nat.le_ceil B
      rw [hN]; push_cast; linarith
    have hpow : Real.exp (B * x) * Real.exp (x / 2) ≤ y ^ N := by
      rw [← Real.exp_add, hy, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hpoly : 3 * y + 2 * y ^ 2 ≤ 5 * y ^ 2 := by nlinarith
    have hfac : y ^ (N + 2) * Real.exp (-π * y) ≤ ((N + 2).factorial : ℝ) := by
      have h1 := Real.pow_div_factorial_le_exp (x := y) (by linarith) (N + 2)
      have hfpos : (0 : ℝ) < ((N + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : y ^ (N + 2) ≤ ((N + 2).factorial : ℝ) * Real.exp y := by
        rw [div_le_iff₀ hfpos] at h1; linarith
      have h3 : Real.exp y * Real.exp (-π * y) ≤ 1 := by
        rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; nlinarith [Real.pi_gt_three]
      calc y ^ (N + 2) * Real.exp (-π * y)
          ≤ ((N + 2).factorial : ℝ) * Real.exp y * Real.exp (-π * y) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = ((N + 2).factorial : ℝ) * (Real.exp y * Real.exp (-π * y)) := by ring
        _ ≤ ((N + 2).factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hfpos.le
        _ = _ := by ring
    have hkey : Real.exp (B * x) * ‖modSource F x‖ ≤ 5 * K * ((N + 2).factorial : ℝ) := by
      calc Real.exp (B * x) * ‖modSource F x‖
          ≤ Real.exp (B * x) * (K * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) *
              Real.exp (-π * y)) := mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
        _ = K * (Real.exp (B * x) * Real.exp (x / 2)) * (3 * y + 2 * y ^ 2) *
              Real.exp (-π * y) := by ring
        _ ≤ K * y ^ N * (5 * y ^ 2) * Real.exp (-π * y) := by
            gcongr
        _ = 5 * K * (y ^ (N + 2) * Real.exp (-π * y)) := by ring
        _ ≤ 5 * K * ((N + 2).factorial : ℝ) := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
    have hexpB : Real.exp (-(B * x)) = (Real.exp (B * x))⁻¹ := Real.exp_neg _
    rw [hexpB]
    rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    linarith [hkey]
  -- middle region
  have hcomp : IsCompact (Set.Icc (-x₀) x₀) := isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hcomp.exists_bound_of_continuousOn
    (continuous_modSource hF).continuousOn
  set C₁ : ℝ := 5 * K * ((N + 2).factorial : ℝ) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max C₁ (max C₀ 0 * Real.exp (B * x₀)), le_max_of_le_left hC₁0, fun x => ?_⟩
  by_cases hmid : |x| ≤ x₀
  · have hxI : x ∈ Set.Icc (-x₀) x₀ := ⟨by linarith [(abs_le.mp hmid).1], (abs_le.mp hmid).2⟩
    have h0 := hC₀ x hxI
    have hexp : 1 ≤ Real.exp (B * x₀) * Real.exp (-(B * |x|)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    calc ‖modSource F x‖ ≤ max C₀ 0 := h0.trans (le_max_left _ _)
      _ ≤ max C₀ 0 * (Real.exp (B * x₀) * Real.exp (-(B * |x|))) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max C₀ 0 * Real.exp (B * x₀) * Real.exp (-(B * |x|)) := by ring
      _ ≤ max C₁ (max C₀ 0 * Real.exp (B * x₀)) * Real.exp (-(B * |x|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hmid := not_le.mp hmid
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at hmid ⊢
      exact (hfar x hmid.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · rw [abs_of_neg hx] at hmid ⊢
      have heven := modSource_neg hF hS (-x)
      rw [neg_neg] at heven
      rw [heven]
      exact (hfar (-x) hmid.le).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

end Decay


/-! ## The Fourier--Laplace transform of the source -/

section Transform

theorem integrable_exp_neg_mul_abs_modSource {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -a) (neg_lt_zero.mpr ha) 0
    exact h.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Set.Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := a) ha 0
    exact h.congr_fun (fun x hx => by rw [abs_of_nonpos hx]; ring_nf) measurableSet_Iic
  simpa [Set.Ioi_union_Iic] using hpos.union hneg

variable (F : ℂ → ℂ)

/-- The Fourier--Laplace transform `Ξ_F(w) = ∫ e^{-iwx} k_F(x) dx`. -/
def modXiIntegrand (w : ℂ) (x : ℝ) : ℂ := Complex.exp (-I * w * (x : ℂ)) * modSource F x

def modXi (w : ℂ) : ℂ := ∫ x : ℝ, modXiIntegrand F w x

def modXiDerivIntegrand (w : ℂ) (x : ℝ) : ℂ := (-I * (x : ℂ)) * modXiIntegrand F w x

variable {F} {c : ℂ} {M : ℝ}

theorem norm_modXiIntegrand (w : ℂ) (x : ℝ) :
    ‖modXiIntegrand F w x‖ = Real.exp (w.im * x) * ‖modSource F x‖ := by
  rw [modXiIntegrand, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem hasDerivAt_modXiIntegrand (w : ℂ) (x : ℝ) :
    HasDerivAt (fun w => modXiIntegrand F w x) (modXiDerivIntegrand F w x) w := by
  unfold modXiDerivIntegrand modXiIntegrand
  have h := ((hasDerivAt_id w).const_mul (-I)).mul_const (x : ℂ)
  have h2 := (h.cexp).mul_const (modSource F x)
  refine h2.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_modXi (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im)) (w₀ : ℂ) :
    HasDerivAt (modXi F) (∫ x : ℝ, modXiDerivIntegrand F w₀ x) w₀ := by
  set B : ℝ := |w₀.im| + 1 with hBdef
  have hB0 : 0 ≤ B + 2 := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_norm_modSource_le_exp (c := c) (M := M) hF hS hdec hB0
  have hcont := continuous_modSource hF
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (modXiIntegrand F w) volume := by
    intro w
    unfold modXiIntegrand
    exact (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) * modSource F x).aestronglyMeasurable
  -- pointwise domination by an integrable exponential
  have hdomC : ∀ w : ℂ, |w.im| ≤ B → ∀ x : ℝ,
      ‖modXiIntegrand F w x‖ ≤ C * Real.exp (-(2 * |x|)) := by
    intro w hw x
    rw [norm_modXiIntegrand]
    have hx := hC x
    have hwx : w.im * x ≤ B * |x| := by
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ B * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x)
    calc Real.exp (w.im * x) * ‖modSource F x‖
        ≤ Real.exp (B * |x|) * (C * Real.exp (-((B + 2) * |x|))) :=
          mul_le_mul (Real.exp_le_exp.mpr hwx) hx (norm_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-(2 * |x|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hint : ∀ w : ℂ, |w.im| ≤ B → Integrable (modXiIntegrand F w) := by
    intro w hw
    refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 2) (by norm_num)).const_mul C)
      (hmeas w) (Filter.Eventually.of_forall fun x => ?_)
    have := hdomC w hw x
    rw [show -(2 * |x|) = -2 * |x| by ring] at this
    exact this
  set bound : ℝ → ℝ := fun x => C * Real.exp (-|x|) with hbound
  have hboundInt : Integrable bound := by
    have := (integrable_exp_neg_mul_abs_modSource (a := 1) (by norm_num)).const_mul C
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [hbound]
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1, ‖modXiDerivIntegrand F w x‖ ≤ bound x := by
    filter_upwards with x
    intro w hw
    have hdist : ‖w - w₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have him : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
    have hwB : |w.im| ≤ B := by
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ B := by rw [hBdef]; linarith
    have h1 := hdomC w hwB x
    rw [modXiDerivIntegrand, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have hxexp : |x| ≤ Real.exp |x| := by
      have := Real.add_one_le_exp |x|; linarith
    calc |x| * ‖modXiIntegrand F w x‖ ≤ Real.exp |x| * (C * Real.exp (-(2 * |x|))) :=
          mul_le_mul hxexp h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = bound x := by
          rw [hbound, mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := modXiIntegrand F) (F' := modXiDerivIntegrand F) (x₀ := w₀) (bound := bound)
    (Metric.ball_mem_nhds w₀ one_pos) (Filter.Eventually.of_forall hmeas)
    (hint w₀ (by rw [hBdef]; linarith))
    (by
      unfold modXiDerivIntegrand modXiIntegrand
      exact (by fun_prop : Continuous fun x : ℝ =>
        (-I * (x : ℂ)) * (Complex.exp (-I * w₀ * (x : ℂ)) * modSource F x)).aestronglyMeasurable)
    hdom hboundInt
    (Filter.Eventually.of_forall fun x w _ => hasDerivAt_modXiIntegrand w x)
  exact hres.2

/-- **The transform is entire.** -/
theorem differentiable_modXi (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x))
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ - c‖ ≤ M * Real.exp (-π * τ.im)) :
    Differentiable ℂ (modXi F) :=
  fun w => (hasDerivAt_modXi (c := c) (M := M) hF hS hdec w).differentiableAt

/-- **The transform is even.** -/
theorem modXi_neg (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x)) (w : ℂ) :
    modXi F (-w) = modXi F w := by
  unfold modXi modXiIntegrand
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [modSource_neg hF hS x]
  push_cast
  ring_nf

end Transform

end

end RHTower
