import GaloisForLFunctions.HTGeometry.LiouvilleGreenExponentialErrorBound
import GaloisForLFunctions.HTGeometry.LinearSecondOrderUnique

/-!
# A perturbed barrier satisfies its variation-of-constants equation

The error bound of the previous file is stated for a function obeying the exponential Volterra
equation.  This file shows that a genuine solution of

```text
W'' = (u² + ψ) W ,      W(b) = e^{−u(b−a)} ,  W'(b) = −u e^{−u(b−a)}
```

obeys it — the recessive data being imposed at the *right* endpoint, which is where the exponential
Volterra kernel is anchored.

The device is the addition formula: `sinh(u(ξ − t)) = sinh(uξ)cosh(ut) − cosh(uξ)sinh(ut)` separates
the two variables, so the kernel integral is a combination of ordinary tail primitives and
elementary functions, and the terms produced by differentiating the lower limit cancel at the first
step exactly as in the oscillatory case.  Uniqueness is the corpus's own uniqueness for `v'' = P v`.

Normalizing by `e^{u(ξ−a)}` turns the unbounded kernel `sinh(u(ξ−t))` into
`(1 − e^{−2u(t−ξ)})/2 ∈ [0, 1/2]`, which is the whole point of the normalization and is what makes
the Grönwall step available.
-/

noncomputable section

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {a b u : ℝ} {ψ W W' W'' : ℝ → ℝ}

/-- The `cosh`-weighted tail integral of the perturbation. -/
def barrierCoshTail (u b : ℝ) (ψ W : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ t in ξ..b, Real.cosh (u * t) * (ψ t * W t)

/-- The `sinh`-weighted tail integral of the perturbation. -/
def barrierSinhTail (u b : ℝ) (ψ W : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ t in ξ..b, Real.sinh (u * t) * (ψ t * W t)

/-- The separated form of the kernel integral. -/
def barrierKernelTail (u b : ℝ) (ψ W : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  Real.sinh (u * ξ) * barrierCoshTail u b ψ W ξ
    - Real.cosh (u * ξ) * barrierSinhTail u b ψ W ξ

/-- Its derivative. -/
def barrierKernelTailDeriv (u b : ℝ) (ψ W : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  u * (Real.cosh (u * ξ) * barrierCoshTail u b ψ W ξ
    - Real.sinh (u * ξ) * barrierSinhTail u b ψ W ξ)

/-- The separated form is the kernel integral. -/
theorem barrierKernelTail_eq (hψ : Continuous ψ) (hW : Continuous W) (ξ : ℝ) :
    barrierKernelTail u b ψ W ξ = ∫ t in ξ..b, Real.sinh (u * (ξ - t)) * (ψ t * W t) := by
  have hc : IntervalIntegrable (fun t => Real.sinh (u * ξ) * (Real.cosh (u * t) * (ψ t * W t)))
      volume ξ b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hs : IntervalIntegrable (fun t => Real.cosh (u * ξ) * (Real.sinh (u * t) * (ψ t * W t)))
      volume ξ b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [barrierKernelTail, barrierCoshTail, barrierSinhTail, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc hs]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show Real.sinh (u * ξ) * (Real.cosh (u * t) * (ψ t * W t))
      - Real.cosh (u * ξ) * (Real.sinh (u * t) * (ψ t * W t))
    = Real.sinh (u * (ξ - t)) * (ψ t * W t)
  rw [show u * (ξ - t) = u * ξ - u * t by ring, Real.sinh_sub]
  ring

/-! ## Derivatives of the tails -/

theorem hasDerivAt_barrierCoshTail (hψ : Continuous ψ) (hW : Continuous W) (ξ : ℝ) :
    HasDerivAt (barrierCoshTail u b ψ W)
      (-(Real.cosh (u * ξ) * (ψ ξ * W ξ))) ξ := by
  have hcont : Continuous fun t : ℝ => Real.cosh (u * t) * (ψ t * W t) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable ξ b)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

theorem hasDerivAt_barrierSinhTail (hψ : Continuous ψ) (hW : Continuous W) (ξ : ℝ) :
    HasDerivAt (barrierSinhTail u b ψ W)
      (-(Real.sinh (u * ξ) * (ψ ξ * W ξ))) ξ := by
  have hcont : Continuous fun t : ℝ => Real.sinh (u * t) * (ψ t * W t) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable ξ b)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

theorem hasDerivAt_barrierKernelTail (hψ : Continuous ψ) (hW : Continuous W) (ξ : ℝ) :
    HasDerivAt (barrierKernelTail u b ψ W) (barrierKernelTailDeriv u b ψ W ξ) ξ := by
  have hC := hasDerivAt_barrierCoshTail (u := u) (b := b) hψ hW ξ
  have hS := hasDerivAt_barrierSinhTail (u := u) (b := b) hψ hW ξ
  have hsh : HasDerivAt (fun x : ℝ => Real.sinh (u * x)) (Real.cosh (u * ξ) * u) ξ := by
    have h := (Real.hasDerivAt_sinh (u * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul u)
    simpa [Function.comp_def] using h
  have hch : HasDerivAt (fun x : ℝ => Real.cosh (u * x)) (Real.sinh (u * ξ) * u) ξ := by
    have h := (Real.hasDerivAt_cosh (u * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul u)
    simpa [Function.comp_def] using h
  have h := (hsh.mul hC).sub (hch.mul hS)
  refine h.congr_deriv ?_
  rw [barrierKernelTailDeriv]
  ring

theorem hasDerivAt_barrierKernelTailDeriv (hψ : Continuous ψ) (hW : Continuous W) (ξ : ℝ) :
    HasDerivAt (barrierKernelTailDeriv u b ψ W)
      (u ^ 2 * barrierKernelTail u b ψ W ξ - u * (ψ ξ * W ξ)) ξ := by
  have hC := hasDerivAt_barrierCoshTail (u := u) (b := b) hψ hW ξ
  have hS := hasDerivAt_barrierSinhTail (u := u) (b := b) hψ hW ξ
  have hsh : HasDerivAt (fun x : ℝ => Real.sinh (u * x)) (Real.cosh (u * ξ) * u) ξ := by
    have h := (Real.hasDerivAt_sinh (u * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul u)
    simpa [Function.comp_def] using h
  have hch : HasDerivAt (fun x : ℝ => Real.cosh (u * x)) (Real.sinh (u * ξ) * u) ξ := by
    have h := (Real.hasDerivAt_cosh (u * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul u)
    simpa [Function.comp_def] using h
  have h := ((hch.mul hC).sub (hsh.mul hS)).const_mul u
  refine h.congr_deriv ?_
  have hid : Real.cosh (u * ξ) ^ 2 - Real.sinh (u * ξ) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  rw [barrierKernelTail]
  linear_combination (-(u * (ψ ξ * W ξ))) * hid

/-! ## The Volterra form -/

/-- **A solution of the barrier equation with recessive data at the right endpoint obeys the
exponential Volterra equation.** -/
theorem barrier_volterra_eq (hu : 0 < u) (hψ : Continuous ψ)
    (hW : ∀ x, HasDerivAt W (W' x) x) (hW' : ∀ x, HasDerivAt W' (W'' x) x)
    (hode : ∀ x, W'' x = (u ^ 2 + ψ x) * W x)
    (hWb : W b = Real.exp (-(u * (b - a))))
    (hW'b : W' b = -u * Real.exp (-(u * (b - a)))) :
    ∀ ξ : ℝ, W ξ
      = Real.exp (-(u * (ξ - a))) - (1 / u) * barrierKernelTail u b ψ W ξ := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  set G : ℝ → ℝ := fun ξ => Real.exp (-(u * (ξ - a))) - (1 / u) * barrierKernelTail u b ψ W ξ
    with hG
  set G' : ℝ → ℝ := fun ξ => -u * Real.exp (-(u * (ξ - a)))
    - (1 / u) * barrierKernelTailDeriv u b ψ W ξ with hG'
  have hexp : ∀ ξ : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-(u * (x - a))))
      (-u * Real.exp (-(u * (ξ - a)))) ξ := by
    intro ξ
    have hin : HasDerivAt (fun x : ℝ => -(u * (x - a))) (-u) ξ := by
      have h0 : HasDerivAt (fun x : ℝ => u * (x - a)) (u * 1) ξ :=
        ((hasDerivAt_id ξ).sub_const a).const_mul u
      have h1 : HasDerivAt (fun x : ℝ => -(u * (x - a))) (-(u * 1)) ξ := h0.neg
      simpa using h1
    have h := hin.exp
    refine h.congr_deriv ?_
    ring
  have hexp' : ∀ ξ : ℝ, HasDerivAt (fun x : ℝ => -u * Real.exp (-(u * (x - a))))
      (u ^ 2 * Real.exp (-(u * (ξ - a)))) ξ := by
    intro ξ
    have h := (hexp ξ).const_mul (-u)
    refine h.congr_deriv ?_
    ring
  have hGd : ∀ ξ : ℝ, HasDerivAt G (G' ξ) ξ := by
    intro ξ
    exact (hexp ξ).sub (((hasDerivAt_barrierKernelTail (u := u) (b := b) hψ hWc ξ).const_mul (1 / u)))
  have hG'd : ∀ ξ : ℝ, HasDerivAt G'
      (u ^ 2 * G ξ + ψ ξ * W ξ) ξ := by
    intro ξ
    have h := (hexp' ξ).sub ((hasDerivAt_barrierKernelTailDeriv (u := u) (b := b) hψ hWc ξ).const_mul (1 / u))
    refine h.congr_deriv ?_
    rw [hG]
    field_simp
    ring
  -- the difference solves the unperturbed barrier equation with zero data at `b`
  set D : ℝ → ℝ := fun ξ => G ξ - W ξ with hD
  set D' : ℝ → ℝ := fun ξ => G' ξ - W' ξ with hD'
  have hDd : ∀ x : ℝ, HasDerivAt D (D' x) x := fun x => (hGd x).sub (hW x)
  have hD'd : ∀ x : ℝ, HasDerivAt D' ((fun _ : ℝ => u ^ 2) x * D x) x := by
    intro x
    have h := (hG'd x).sub (hW' x)
    refine h.congr_deriv ?_
    rw [hD, hode x]
    ring
  have hzero : ∀ x : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => (0 : ℝ)) x) x :=
    fun x => hasDerivAt_const x 0
  have hzero' : ∀ x : ℝ,
      HasDerivAt (fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => u ^ 2) x * (fun _ : ℝ => (0 : ℝ)) x) x := by
    intro x
    simpa using hasDerivAt_const x (0 : ℝ)
  have hDb : D b = 0 := by
    have hK : barrierKernelTail u b ψ W b = 0 := by
      rw [barrierKernelTail, barrierCoshTail, barrierSinhTail]
      simp
    rw [hD, hG]
    simp only
    rw [hK, hWb]
    ring
  have hD'b : D' b = 0 := by
    have hKd : barrierKernelTailDeriv u b ψ W b = 0 := by
      rw [barrierKernelTailDeriv, barrierCoshTail, barrierSinhTail]
      simp
    rw [hD', hG']
    simp only
    rw [hKd, hW'b]
    ring
  have heq := secondOrder_eq_at (P := fun _ : ℝ => u ^ 2) (u := D) (u' := D')
    (v := fun _ : ℝ => (0 : ℝ)) (v' := fun _ : ℝ => (0 : ℝ)) continuous_const b
    hDd hD'd hzero hzero' (by rw [hDb]) (by rw [hD'b])
  intro ξ
  have := congrFun heq ξ
  simp only [hD] at this
  linarith [this]

/-- **The normalized recessive branch satisfies the exponential Liouville–Green Volterra
equation.** -/
theorem isExponentialLGSolution_of_ode (hu : 0 < u) (hψ : Continuous ψ)
    (hW : ∀ x, HasDerivAt W (W' x) x) (hW' : ∀ x, HasDerivAt W' (W'' x) x)
    (hode : ∀ x, W'' x = (u ^ 2 + ψ x) * W x)
    (hWb : W b = Real.exp (-(u * (b - a))))
    (hW'b : W' b = -u * Real.exp (-(u * (b - a)))) :
    IsExponentialLGSolution b u ψ (fun ξ => Real.exp (u * (ξ - a)) * W ξ) a := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  intro ξ _
  have hvol := barrier_volterra_eq hu hψ hW hW' hode hWb hW'b ξ
  have hkey : Real.exp (u * (ξ - a)) * barrierKernelTail u b ψ W ξ
      = -∫ t in ξ..b, expLGKernel u ξ t * ψ t * (Real.exp (u * (t - a)) * W t) := by
    rw [barrierKernelTail_eq hψ hWc ξ, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Real.exp (u * (ξ - a)) * (Real.sinh (u * (ξ - t)) * (ψ t * W t))
      = -(expLGKernel u ξ t * ψ t * (Real.exp (u * (t - a)) * W t))
    have hsplit : Real.exp (u * (ξ - a)) = Real.exp (u * (ξ - t)) * Real.exp (u * (t - a)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hker : Real.exp (u * (ξ - t)) * Real.sinh (u * (ξ - t)) = -expLGKernel u ξ t := by
      have h1 : Real.exp (u * (ξ - t)) * Real.exp (u * (ξ - t))
          = Real.exp (2 * (u * (ξ - t))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (u * (ξ - t)) * Real.exp (-(u * (ξ - t))) = 1 := by
        rw [← Real.exp_add]
        simp
      have h3 : Real.exp (2 * (u * (ξ - t))) = Real.exp (-(2 * u * (t - ξ))) := by
        congr 1
        ring
      have hE : Real.exp (u * (ξ - t)) * Real.sinh (u * (ξ - t))
          = (Real.exp (u * (ξ - t)) * Real.exp (u * (ξ - t))
            - Real.exp (u * (ξ - t)) * Real.exp (-(u * (ξ - t)))) / 2 := by
        rw [Real.sinh_eq]
        ring
      rw [hE, h1, h2, h3, expLGKernel]
      ring
    rw [hsplit]
    calc Real.exp (u * (ξ - t)) * Real.exp (u * (t - a)) * (Real.sinh (u * (ξ - t)) * (ψ t * W t))
        = (Real.exp (u * (ξ - t)) * Real.sinh (u * (ξ - t)))
            * (ψ t * (Real.exp (u * (t - a)) * W t)) := by ring
      _ = -(expLGKernel u ξ t * ψ t * (Real.exp (u * (t - a)) * W t)) := by
          rw [hker]; ring
  show Real.exp (u * (ξ - a)) * W ξ
    = 1 + (1 / u) * ∫ t in ξ..b, expLGKernel u ξ t * ψ t * (Real.exp (u * (t - a)) * W t)
  rw [hvol, mul_sub]
  have hone : Real.exp (u * (ξ - a)) * Real.exp (-(u * (ξ - a))) = 1 := by
    rw [← Real.exp_add]
    simp
  have hassoc : Real.exp (u * (ξ - a)) * (1 / u * barrierKernelTail u b ψ W ξ)
      = (1 / u) * (Real.exp (u * (ξ - a)) * barrierKernelTail u b ψ W ξ) := by ring
  rw [hone, hassoc, hkey]
  ring

/-! ## The barrier estimate -/

/-- **The barrier estimate.**  A solution with recessive data at the right endpoint differs from
`e^{−u(ξ−a)}` by a relative error controlled by the mass of the perturbation on the remaining
interval. -/
theorem abs_barrier_normalized_sub_one_le (hab : a ≤ b) (hu : 0 < u) (hψ : Continuous ψ)
    (hW : ∀ x, HasDerivAt W (W' x) x) (hW' : ∀ x, HasDerivAt W' (W'' x) x)
    (hode : ∀ x, W'' x = (u ^ 2 + ψ x) * W x)
    (hWb : W b = Real.exp (-(u * (b - a))))
    (hW'b : W' b = -u * Real.exp (-(u * (b - a)))) :
    ∀ ξ ∈ Icc a b, |Real.exp (u * (ξ - a)) * W ξ - 1|
      ≤ Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|) - 1 := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  have hVc : Continuous fun ξ : ℝ => Real.exp (u * (ξ - a)) * W ξ := by
    exact (Real.continuous_exp.comp (by fun_prop)).mul hWc
  exact abs_sub_one_le_exp_sub_one_of_exponentialLG hab hu hVc hψ
    (isExponentialLGSolution_of_ode hu hψ hW hW' hode hWb hW'b)

/-- **The two-sided barrier estimate.**  The solution is trapped between two multiples of the
unperturbed exponential, with the same error-control factor on both sides. -/
theorem barrier_two_sided (hab : a ≤ b) (hu : 0 < u) (hψ : Continuous ψ)
    (hW : ∀ x, HasDerivAt W (W' x) x) (hW' : ∀ x, HasDerivAt W' (W'' x) x)
    (hode : ∀ x, W'' x = (u ^ 2 + ψ x) * W x)
    (hWb : W b = Real.exp (-(u * (b - a))))
    (hW'b : W' b = -u * Real.exp (-(u * (b - a))))
    {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    (2 - Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|)) * Real.exp (-(u * (ξ - a))) ≤ W ξ ∧
      W ξ ≤ Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|) * Real.exp (-(u * (ξ - a))) := by
  set E : ℝ := Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|) with hE
  have habs := abs_barrier_normalized_sub_one_le hab hu hψ hW hW' hode hWb hW'b ξ hξ
  rw [abs_le] at habs
  have hpos : (0 : ℝ) < Real.exp (-(u * (ξ - a))) := Real.exp_pos _
  have hcancel : Real.exp (-(u * (ξ - a))) * Real.exp (u * (ξ - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  constructor
  · have hlow : 2 - E ≤ Real.exp (u * (ξ - a)) * W ξ := by linarith [habs.1]
    have := mul_le_mul_of_nonneg_right hlow hpos.le
    calc (2 - E) * Real.exp (-(u * (ξ - a)))
        ≤ Real.exp (u * (ξ - a)) * W ξ * Real.exp (-(u * (ξ - a))) := this
      _ = W ξ := by
          rw [mul_comm (Real.exp (u * (ξ - a))) (W ξ), mul_assoc,
            mul_comm (Real.exp (u * (ξ - a))) (Real.exp (-(u * (ξ - a)))), hcancel, mul_one]
  · have hup : Real.exp (u * (ξ - a)) * W ξ ≤ E := by linarith [habs.2]
    have := mul_le_mul_of_nonneg_right hup hpos.le
    calc W ξ
        = Real.exp (u * (ξ - a)) * W ξ * Real.exp (-(u * (ξ - a))) := by
          rw [mul_comm (Real.exp (u * (ξ - a))) (W ξ), mul_assoc,
            mul_comm (Real.exp (u * (ξ - a))) (Real.exp (-(u * (ξ - a)))), hcancel, mul_one]
      _ ≤ E * Real.exp (-(u * (ξ - a))) := this

end GaloisForLFunctions.HTGeometry
