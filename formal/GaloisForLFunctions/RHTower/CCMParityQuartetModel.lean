import Mathlib

/-!
# The isolated off-line quartet model: closed forms and the phase-aperture gap

Fix `t, δ > 0` (the top off-line spectral point is `σ = t + iδ`) and an aperture `a`. Put

* `D⁺(a) = ∫_{−a}^{a} 4 sin²(tx) sinh²(δx) dx` (`evenFloorMass`): squared norm of the even
  difference vector `cos(σx) − cos(σ̄x) = −2i sin(tx) sinh(δx)`;
* `D⁻(a) = ∫_{−a}^{a} 4 cos²(tx) sinh²(δx) dx` (`oddTestMass`): squared norm of the odd test
  `g(x) = 2 cos(tx) sinh(δx)`;
* `I(a) = ∫_{−a}^{a} 2 cos(tx) sinh(δx) · sin(tx) cosh(δx) dx` (`oddTestCross`): the real part of
  `−i ĝ(σ)`.

**Closed forms.** `D⁻ + D⁺ = 2 sinh(2δa)/δ − 4a`,
`D⁻ − D⁺ = 2J − 2 sin(2ta)/t` with `J = (δ sinh(2δa) cos(2ta) + t cosh(2δa) sin(2ta))/(δ²+t²)`,
`I = (δ cosh(2δa) sin(2ta) − t sinh(2δa) cos(2ta))/(2(δ²+t²))`.

**Phase apertures.** With `θ = arg(δ + it)` and `r = √(δ²+t²)`, the apertures
`a_k = (θ + 2πk)/(2t)` have `sin(2ta_k) = t/r`, `cos(2ta_k) = δ/r`, hence
`D⁻ − D⁺ ≥ 2(sinh(2δa_k) − 1)/r`, `0 ≤ I(a_k) ≤ 1/(4r)` and `D⁻ ≥ sinh(2δa_k)/δ − 2a_k − 1/r`.

**Theorem** (`exists_phaseAperture_gap`). For `M > 0`, `C₁, C₂ ≥ 0` and `δ' < δ`, arbitrarily
large phase apertures satisfy
`2C₁e^{2δ'a} + C₂(1+a)²e^{2δa}/D⁻ + M I²/D⁻ < (M/4)(D⁻ − D⁺)`.
This is the analytic core of the parity-selection no-go: the left side collects the shallower
off-line quartets, the critical-line zeros and the imaginary part of the top transform, and the
right side is the parity gap produced by the top quartet.
-/

open Real Filter Topology

namespace RHTower.CCMParityQuartet

noncomputable section

/-! ## The three model integrals -/

/-- `D⁺(a) = ∫_{−a}^{a} 4 sin²(tx) sinh²(δx) dx`. -/
def evenFloorMass (t δ a : ℝ) : ℝ :=
  ∫ x in (-a)..a, 4 * Real.sin (t * x) ^ 2 * Real.sinh (δ * x) ^ 2

/-- `D⁻(a) = ∫_{−a}^{a} 4 cos²(tx) sinh²(δx) dx`. -/
def oddTestMass (t δ a : ℝ) : ℝ :=
  ∫ x in (-a)..a, 4 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2

/-- `I(a) = ∫_{−a}^{a} 2 cos(tx) sinh(δx) sin(tx) cosh(δx) dx`. -/
def oddTestCross (t δ a : ℝ) : ℝ :=
  ∫ x in (-a)..a, 2 * Real.cos (t * x) * Real.sinh (δ * x) * (Real.sin (t * x) * Real.cosh (δ * x))

/-- The phase-weighted hyperbolic integral `J(a)`. -/
def phaseJ (t δ a : ℝ) : ℝ :=
  (δ * Real.sinh (2 * δ * a) * Real.cos (2 * t * a) +
      t * Real.cosh (2 * δ * a) * Real.sin (2 * t * a)) / (δ ^ 2 + t ^ 2)

/-! ## Derivatives of the elementary building blocks -/

theorem hasDerivAt_sinh_mul (α x : ℝ) :
    HasDerivAt (fun y => Real.sinh (α * y)) (Real.cosh (α * x) * α) x := by
  simpa using ((hasDerivAt_id x).const_mul α).sinh

theorem hasDerivAt_cosh_mul (α x : ℝ) :
    HasDerivAt (fun y => Real.cosh (α * y)) (Real.sinh (α * x) * α) x := by
  simpa using ((hasDerivAt_id x).const_mul α).cosh

theorem hasDerivAt_sin_mul (α x : ℝ) :
    HasDerivAt (fun y => Real.sin (α * y)) (Real.cos (α * x) * α) x := by
  simpa using ((hasDerivAt_id x).const_mul α).sin

theorem hasDerivAt_cos_mul (α x : ℝ) :
    HasDerivAt (fun y => Real.cos (α * y)) (-Real.sin (α * x) * α) x := by
  simpa using ((hasDerivAt_id x).const_mul α).cos

/-! ## Pointwise identities -/

theorem sum_integrand_eq (t δ x : ℝ) :
    4 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 +
        4 * Real.sin (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 =
      2 * Real.cosh (2 * δ * x) - 2 := by
  have h1 := Real.sin_sq_add_cos_sq (t * x)
  have h2 := Real.cosh_sq (δ * x)
  have hc : Real.cosh (2 * δ * x) = Real.cosh (δ * x) ^ 2 + Real.sinh (δ * x) ^ 2 := by
    rw [show 2 * δ * x = 2 * (δ * x) by ring, Real.cosh_two_mul]
  rw [hc]
  linear_combination (4 * Real.sinh (δ * x) ^ 2) * h1 - 2 * h2

theorem diff_integrand_eq (t δ x : ℝ) :
    4 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 -
        4 * Real.sin (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 =
      2 * Real.cos (2 * t * x) * Real.cosh (2 * δ * x) - 2 * Real.cos (2 * t * x) := by
  have h1 := Real.sin_sq_add_cos_sq (t * x)
  have h2 := Real.cosh_sq (δ * x)
  have hc : Real.cosh (2 * δ * x) = Real.cosh (δ * x) ^ 2 + Real.sinh (δ * x) ^ 2 := by
    rw [show 2 * δ * x = 2 * (δ * x) by ring, Real.cosh_two_mul]
  have hco : Real.cos (2 * t * x) = 2 * Real.cos (t * x) ^ 2 - 1 := by
    rw [show 2 * t * x = 2 * (t * x) by ring, Real.cos_two_mul]
  rw [hc, hco]
  linear_combination (-4 * Real.sinh (δ * x) ^ 2) * h1 +
    (2 - 4 * Real.cos (t * x) ^ 2) * h2

theorem cross_integrand_eq (t δ x : ℝ) :
    2 * Real.cos (t * x) * Real.sinh (δ * x) * (Real.sin (t * x) * Real.cosh (δ * x)) =
      Real.sin (2 * t * x) * Real.sinh (2 * δ * x) / 2 := by
  rw [show 2 * t * x = 2 * (t * x) by ring, show 2 * δ * x = 2 * (δ * x) by ring,
    Real.sin_two_mul, Real.sinh_two_mul]
  ring

/-! ## Closed forms -/

theorem oddTestMass_add_evenFloorMass {δ : ℝ} (hδ : δ ≠ 0) (t a : ℝ) :
    oddTestMass t δ a + evenFloorMass t δ a = 2 * Real.sinh (2 * δ * a) / δ - 4 * a := by
  unfold oddTestMass evenFloorMass
  rw [← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hcongr : (∫ x in (-a)..a, 4 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 +
      4 * Real.sin (t * x) ^ 2 * Real.sinh (δ * x) ^ 2) =
      ∫ x in (-a)..a, (2 * Real.cosh (2 * δ * x) - 2) :=
    intervalIntegral.integral_congr fun x _ => sum_integrand_eq t δ x
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun y => Real.sinh (2 * δ * y) / δ - 2 * y)
        (2 * Real.cosh (2 * δ * x) - 2) x := by
    intro x _
    have h := ((hasDerivAt_sinh_mul (2 * δ) x).div_const δ).sub ((hasDerivAt_id x).const_mul 2)
    refine h.congr_deriv ?_
    rw [mul_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_neg, Real.sinh_neg]
  ring

theorem oddTestMass_sub_evenFloorMass {t δ : ℝ} (ht : t ≠ 0) (hδt : δ ^ 2 + t ^ 2 ≠ 0) (a : ℝ) :
    oddTestMass t δ a - evenFloorMass t δ a =
      2 * phaseJ t δ a - 2 * Real.sin (2 * t * a) / t := by
  unfold oddTestMass evenFloorMass
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hcongr : (∫ x in (-a)..a, 4 * Real.cos (t * x) ^ 2 * Real.sinh (δ * x) ^ 2 -
      4 * Real.sin (t * x) ^ 2 * Real.sinh (δ * x) ^ 2) =
      ∫ x in (-a)..a,
        (2 * Real.cos (2 * t * x) * Real.cosh (2 * δ * x) - 2 * Real.cos (2 * t * x)) :=
    intervalIntegral.integral_congr fun x _ => diff_integrand_eq t δ x
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun y => phaseJ t δ y - Real.sin (2 * t * y) / t)
        (2 * Real.cos (2 * t * x) * Real.cosh (2 * δ * x) - 2 * Real.cos (2 * t * x)) x := by
    intro x _
    have hA := (hasDerivAt_sinh_mul (2 * δ) x).mul (hasDerivAt_cos_mul (2 * t) x)
    have hB := (hasDerivAt_cosh_mul (2 * δ) x).mul (hasDerivAt_sin_mul (2 * t) x)
    have hJ := ((hA.const_mul δ).add (hB.const_mul t)).div_const (δ ^ 2 + t ^ 2)
    have h := hJ.sub ((hasDerivAt_sin_mul (2 * t) x).div_const t)
    have h' := h.congr_deriv (show _ = 2 * Real.cos (2 * t * x) * Real.cosh (2 * δ * x) -
        2 * Real.cos (2 * t * x) by
      rw [div_sub_div _ _ hδt ht, div_eq_iff (mul_ne_zero hδt ht)]
      ring)
    unfold phaseJ
    exact h'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  unfold phaseJ
  simp only [mul_neg, Real.sinh_neg, Real.cosh_neg, Real.sin_neg, Real.cos_neg]
  ring

theorem oddTestCross_eq {t δ : ℝ} (hδt : δ ^ 2 + t ^ 2 ≠ 0) (a : ℝ) :
    oddTestCross t δ a =
      (δ * Real.cosh (2 * δ * a) * Real.sin (2 * t * a) -
          t * Real.sinh (2 * δ * a) * Real.cos (2 * t * a)) / (2 * (δ ^ 2 + t ^ 2)) := by
  unfold oddTestCross
  have hcongr : (∫ x in (-a)..a,
      2 * Real.cos (t * x) * Real.sinh (δ * x) * (Real.sin (t * x) * Real.cosh (δ * x))) =
      ∫ x in (-a)..a, Real.sin (2 * t * x) * Real.sinh (2 * δ * x) / 2 :=
    intervalIntegral.integral_congr fun x _ => cross_integrand_eq t δ x
  rw [hcongr]
  have hderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun y => (δ * Real.cosh (2 * δ * y) * Real.sin (2 * t * y) -
          t * Real.sinh (2 * δ * y) * Real.cos (2 * t * y)) / (4 * (δ ^ 2 + t ^ 2)))
        (Real.sin (2 * t * x) * Real.sinh (2 * δ * x) / 2) x := by
    intro x _
    have hA := (hasDerivAt_cosh_mul (2 * δ) x).mul (hasDerivAt_sin_mul (2 * t) x)
    have hB := (hasDerivAt_sinh_mul (2 * δ) x).mul (hasDerivAt_cos_mul (2 * t) x)
    have h := ((hA.const_mul δ).sub (hB.const_mul t)).div_const (4 * (δ ^ 2 + t ^ 2))
    have h' := h.congr_deriv (show _ = Real.sin (2 * t * x) * Real.sinh (2 * δ * x) / 2 by
      rw [div_eq_div_iff (mul_ne_zero four_ne_zero hδt) two_ne_zero]
      ring)
    exact h'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp only [Pi.sub_apply, Pi.mul_apply]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_neg, Real.sinh_neg, Real.cosh_neg, Real.sin_neg, Real.cos_neg]
  field_simp
  ring

/-! ## Phase apertures -/

/-- The phase angle `θ = arg(δ + it)`. -/
def phaseAngle (t δ : ℝ) : ℝ := Complex.arg (⟨δ, t⟩ : ℂ)

/-- The phase apertures `a_k = (θ + 2πk)/(2t)`. -/
def phaseAperture (t δ : ℝ) (k : ℕ) : ℝ := (phaseAngle t δ + k * (2 * π)) / (2 * t)

theorem norm_mk_eq_sqrt (t δ : ℝ) : ‖(⟨δ, t⟩ : ℂ)‖ = Real.sqrt (δ ^ 2 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_mk]
  ring_nf

theorem two_mul_phaseAperture {t : ℝ} (ht : t ≠ 0) (δ : ℝ) (k : ℕ) :
    2 * t * phaseAperture t δ k = phaseAngle t δ + (k : ℤ) * (2 * π) := by
  unfold phaseAperture
  rw [mul_div_cancel₀ _ (mul_ne_zero two_ne_zero ht)]
  push_cast
  rfl

theorem sin_phaseAperture {t δ : ℝ} (ht : t ≠ 0) (k : ℕ) :
    Real.sin (2 * t * phaseAperture t δ k) = t / Real.sqrt (δ ^ 2 + t ^ 2) := by
  rw [two_mul_phaseAperture ht, Real.sin_add_int_mul_two_pi, phaseAngle, Complex.sin_arg,
    norm_mk_eq_sqrt]

theorem cos_phaseAperture {t δ : ℝ} (ht : t ≠ 0) (k : ℕ) :
    Real.cos (2 * t * phaseAperture t δ k) = δ / Real.sqrt (δ ^ 2 + t ^ 2) := by
  have hne : (⟨δ, t⟩ : ℂ) ≠ 0 := by
    intro h
    exact ht (congrArg Complex.im h)
  rw [two_mul_phaseAperture ht, Real.cos_add_int_mul_two_pi, phaseAngle, Complex.cos_arg hne,
    norm_mk_eq_sqrt]

theorem exists_phaseAperture_gt {t : ℝ} (ht : 0 < t) (δ A : ℝ) :
    ∃ k : ℕ, A < phaseAperture t δ k := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((2 * t * A - phaseAngle t δ) / (2 * π))
  refine ⟨k, ?_⟩
  unfold phaseAperture
  rw [lt_div_iff₀ (by positivity)]
  have hπ : 0 < 2 * π := by positivity
  rw [div_lt_iff₀ hπ] at hk
  linarith

/-! ## Values at the phase apertures -/

section Phase

variable {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
include ht hδ

theorem sqrt_pos' : 0 < Real.sqrt (δ ^ 2 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)

theorem sq_sqrt' : Real.sqrt (δ ^ 2 + t ^ 2) ^ 2 = δ ^ 2 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem phaseJ_phaseAperture (k : ℕ) :
    phaseJ t δ (phaseAperture t δ k) =
      (δ ^ 2 * Real.sinh (2 * δ * phaseAperture t δ k) +
          t ^ 2 * Real.cosh (2 * δ * phaseAperture t δ k)) /
        Real.sqrt (δ ^ 2 + t ^ 2) ^ 3 := by
  have hr := sqrt_pos' ht hδ
  have hr2 := sq_sqrt' ht hδ
  unfold phaseJ
  rw [sin_phaseAperture ht.ne', cos_phaseAperture ht.ne']
  set r := Real.sqrt (δ ^ 2 + t ^ 2) with hr_def
  rw [← hr2]
  field_simp

theorem sinh_div_le_phaseJ (k : ℕ) :
    Real.sinh (2 * δ * phaseAperture t δ k) / Real.sqrt (δ ^ 2 + t ^ 2) ≤
      phaseJ t δ (phaseAperture t δ k) := by
  have hr := sqrt_pos' ht hδ
  have hr2 := sq_sqrt' ht hδ
  rw [phaseJ_phaseAperture ht hδ, div_le_div_iff₀ hr (by positivity)]
  have hsc := (Real.sinh_lt_cosh (2 * δ * phaseAperture t δ k)).le
  have hstep : Real.sinh (2 * δ * phaseAperture t δ k) * Real.sqrt (δ ^ 2 + t ^ 2) ^ 3 =
      (δ ^ 2 * Real.sinh (2 * δ * phaseAperture t δ k) +
        t ^ 2 * Real.sinh (2 * δ * phaseAperture t δ k)) * Real.sqrt (δ ^ 2 + t ^ 2) := by
    rw [pow_succ, hr2]
    ring
  rw [hstep]
  apply mul_le_mul_of_nonneg_right _ hr.le
  nlinarith [sq_nonneg t]

theorem gap_ge_phaseAperture (k : ℕ) :
    2 * (Real.sinh (2 * δ * phaseAperture t δ k) - 1) / Real.sqrt (δ ^ 2 + t ^ 2) ≤
      oddTestMass t δ (phaseAperture t δ k) - evenFloorMass t δ (phaseAperture t δ k) := by
  have hr := sqrt_pos' ht hδ
  rw [oddTestMass_sub_evenFloorMass ht.ne' (by positivity), sin_phaseAperture ht.ne']
  have hJ := sinh_div_le_phaseJ ht hδ k
  have : 2 * (t / Real.sqrt (δ ^ 2 + t ^ 2)) / t = 2 / Real.sqrt (δ ^ 2 + t ^ 2) := by
    field_simp
  rw [this]
  have h2 : 2 * (Real.sinh (2 * δ * phaseAperture t δ k) - 1) / Real.sqrt (δ ^ 2 + t ^ 2) =
      2 * (Real.sinh (2 * δ * phaseAperture t δ k) / Real.sqrt (δ ^ 2 + t ^ 2)) -
        2 / Real.sqrt (δ ^ 2 + t ^ 2) := by
    field_simp
  rw [h2]
  linarith

theorem oddTestCross_phaseAperture (k : ℕ) :
    oddTestCross t δ (phaseAperture t δ k) =
      t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) /
        (2 * Real.sqrt (δ ^ 2 + t ^ 2) ^ 3) := by
  have hr := sqrt_pos' ht hδ
  have hr2 := sq_sqrt' ht hδ
  rw [oddTestCross_eq (by positivity), sin_phaseAperture ht.ne', cos_phaseAperture ht.ne',
    ← Real.cosh_sub_sinh]
  set r := Real.sqrt (δ ^ 2 + t ^ 2) with hr_def
  rw [← hr2]
  field_simp

theorem oddTestCross_sq_le_phaseAperture (k : ℕ) (hk : 0 ≤ phaseAperture t δ k) :
    oddTestCross t δ (phaseAperture t δ k) ^ 2 ≤ 1 / (16 * (δ ^ 2 + t ^ 2)) := by
  have hr := sqrt_pos' ht hδ
  have hr2 := sq_sqrt' ht hδ
  rw [oddTestCross_phaseAperture ht hδ]
  have hexp : Real.exp (-(2 * δ * phaseAperture t δ k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hexp0 : 0 ≤ Real.exp (-(2 * δ * phaseAperture t δ k)) := (Real.exp_pos _).le
  have hnum : t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) ≤ (δ ^ 2 + t ^ 2) / 2 := by
    have h1 : t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) ≤ t * δ :=
      mul_le_of_le_one_right (by positivity) hexp
    nlinarith [sq_nonneg (t - δ)]
  have hnum0 : 0 ≤ t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) := by positivity
  have hq : t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) /
      (2 * Real.sqrt (δ ^ 2 + t ^ 2) ^ 3) ≤ 1 / (4 * Real.sqrt (δ ^ 2 + t ^ 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : Real.sqrt (δ ^ 2 + t ^ 2) ^ 3 = (δ ^ 2 + t ^ 2) * Real.sqrt (δ ^ 2 + t ^ 2) := by
      rw [pow_succ, hr2]
    rw [this]
    nlinarith
  have hq0 : 0 ≤ t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) /
      (2 * Real.sqrt (δ ^ 2 + t ^ 2) ^ 3) := by positivity
  calc (t * δ * Real.exp (-(2 * δ * phaseAperture t δ k)) /
        (2 * Real.sqrt (δ ^ 2 + t ^ 2) ^ 3)) ^ 2
      ≤ (1 / (4 * Real.sqrt (δ ^ 2 + t ^ 2))) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    _ = 1 / (16 * (δ ^ 2 + t ^ 2)) := by
      rw [div_pow, mul_pow, hr2]
      norm_num

theorem oddTestMass_ge_phaseAperture (k : ℕ) (hk : 0 ≤ phaseAperture t δ k) :
    Real.sinh (2 * δ * phaseAperture t δ k) / δ - 2 * phaseAperture t δ k -
        1 / Real.sqrt (δ ^ 2 + t ^ 2) ≤
      oddTestMass t δ (phaseAperture t δ k) := by
  have hr := sqrt_pos' ht hδ
  have hsum := oddTestMass_add_evenFloorMass hδ.ne' t (phaseAperture t δ k)
  have hdiff := oddTestMass_sub_evenFloorMass ht.ne' (by positivity : δ ^ 2 + t ^ 2 ≠ 0)
    (phaseAperture t δ k)
  rw [sin_phaseAperture ht.ne'] at hdiff
  have hJ := sinh_div_le_phaseJ ht hδ k
  have hsinh : 0 ≤ Real.sinh (2 * δ * phaseAperture t δ k) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hJ0 : 0 ≤ phaseJ t δ (phaseAperture t δ k) := le_trans (by positivity) hJ
  have h2 : 2 * (t / Real.sqrt (δ ^ 2 + t ^ 2)) / t = 2 / Real.sqrt (δ ^ 2 + t ^ 2) := by
    field_simp
  rw [h2] at hdiff
  have h3 : 1 / Real.sqrt (δ ^ 2 + t ^ 2) = (2 / Real.sqrt (δ ^ 2 + t ^ 2)) / 2 := by ring
  rw [h3]
  have h4 : 2 * Real.sinh (2 * δ * phaseAperture t δ k) / δ =
      2 * (Real.sinh (2 * δ * phaseAperture t δ k) / δ) := by ring
  rw [h4] at hsum
  linarith

end Phase

/-! ## Asymptotics -/

/-- Eventually `e^{2δa}/(4δ) ≤ sinh(2δa)/δ − 2a − c`. -/
theorem eventually_exp_div_le_sinh_sub {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    ∀ᶠ a in atTop, Real.exp (2 * δ * a) / (4 * δ) ≤ Real.sinh (2 * δ * a) / δ - 2 * a - c := by
  have hlin : (fun a : ℝ => a ^ 1) =o[atTop] fun a => Real.exp ((2 * δ) * a) :=
    isLittleO_pow_exp_pos_mul_atTop 1 (by positivity)
  have hb := hlin.bound (show (0 : ℝ) < 1 / (16 * δ) by positivity)
  have hexp : Tendsto (fun a : ℝ => Real.exp (2 * δ * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have hbig := hexp.eventually_ge_atTop (8 * δ * |c| + 4)
  filter_upwards [hb, hbig, eventually_ge_atTop (0 : ℝ)] with a ha hE ha0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_of_nonneg ha0,
    abs_of_pos (Real.exp_pos _)] at ha
  have hsinh : Real.sinh (2 * δ * a) = (Real.exp (2 * δ * a) - Real.exp (-(2 * δ * a))) / 2 :=
    Real.sinh_eq _
  have hneg : Real.exp (-(2 * δ * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [hsinh]
  rw [div_le_iff₀ (by positivity)]
  have hrhs : ((Real.exp (2 * δ * a) - Real.exp (-(2 * δ * a))) / 2 / δ - 2 * a - c) * (4 * δ) =
      2 * Real.exp (2 * δ * a) - 2 * Real.exp (-(2 * δ * a)) - 8 * δ * a - 4 * δ * c := by
    field_simp
    ring
  rw [hrhs]
  -- the target, cleared of denominators
  have hc : 4 * δ * c ≤ 4 * δ * |c| := by
    have := le_abs_self c
    nlinarith
  have ha8 : 8 * δ * a ≤ Real.exp (2 * δ * a) / 2 := by
    have h16 : 8 * δ * (1 / (16 * δ) * Real.exp (2 * δ * a)) = Real.exp (2 * δ * a) / 2 := by
      field_simp
      ring
    rw [← h16]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  nlinarith [abs_nonneg c]

/-- Eventually `c·e^{2δ'a} ≤ ε·e^{2δa}` for `δ' < δ`. -/
theorem eventually_exp_le_eps_mul_exp {δ δ' : ℝ} (hδ' : δ' < δ) {c ε : ℝ} (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ a in atTop, c * Real.exp (2 * δ' * a) ≤ ε * Real.exp (2 * δ * a) := by
  have hdecay : Tendsto (fun a : ℝ => Real.exp (-(2 * (δ - δ') * a))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith))
  have hsmall := hdecay.eventually (ge_mem_nhds (show (0 : ℝ) < ε / (c + 1) by positivity))
  filter_upwards [hsmall] with a ha
  have hsplit : Real.exp (2 * δ' * a) =
      Real.exp (2 * δ * a) * Real.exp (-(2 * (δ - δ') * a)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  have hE := (Real.exp_pos (2 * δ * a)).le
  have hstep : c * (ε / (c + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc c * (Real.exp (2 * δ * a) * Real.exp (-(2 * (δ - δ') * a)))
      = Real.exp (2 * δ * a) * (c * Real.exp (-(2 * (δ - δ') * a))) := by ring
    _ ≤ Real.exp (2 * δ * a) * (c * (ε / (c + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hE
        exact mul_le_mul_of_nonneg_left ha hc
    _ ≤ Real.exp (2 * δ * a) * ε := mul_le_mul_of_nonneg_left hstep hE
    _ = ε * Real.exp (2 * δ * a) := by ring

/-- Eventually `c·(1+a)² ≤ ε·e^{2δa}`. -/
theorem eventually_sq_le_eps_mul_exp {δ : ℝ} (hδ : 0 < δ) {c ε : ℝ} (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ a in atTop, c * (1 + a) ^ 2 ≤ ε * Real.exp (2 * δ * a) := by
  have hlin : (fun a : ℝ => a ^ 2) =o[atTop] fun a => Real.exp ((2 * δ) * a) :=
    isLittleO_pow_exp_pos_mul_atTop 2 (by positivity)
  have hb := hlin.bound (show (0 : ℝ) < ε / (4 * c + 1) by positivity)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with a ha ha1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (Real.exp_pos _)] at ha
  have hsq : (1 + a) ^ 2 ≤ 4 * a ^ 2 := by nlinarith
  have hE := (Real.exp_pos (2 * δ * a)).le
  have hstep : 4 * c * (ε / (4 * c + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc c * (1 + a) ^ 2 ≤ c * (4 * a ^ 2) := mul_le_mul_of_nonneg_left hsq hc
    _ = 4 * c * a ^ 2 := by ring
    _ ≤ 4 * c * (ε / (4 * c + 1) * Real.exp (2 * δ * a)) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
    _ = (4 * c * (ε / (4 * c + 1))) * Real.exp (2 * δ * a) := by ring
    _ ≤ ε * Real.exp (2 * δ * a) := mul_le_mul_of_nonneg_right hstep hE

/-- **The phase-aperture gap.**  For `t, δ, M > 0`, `C₁, C₂ ≥ 0` and `δ' < δ`, arbitrarily large
phase apertures `a` have `D⁻(a) > 0` and
`2C₁e^{2δ'a} + C₂(1+a)²e^{2δa}/D⁻ + M I²/D⁻ < (M/4)(D⁻ − D⁺)`. -/
theorem exists_phaseAperture_gap {t δ δ' M C₁ C₂ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hδ' : δ' < δ) (hM : 0 < M) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (A : ℝ) :
    ∃ k : ℕ, A < phaseAperture t δ k ∧ 0 < phaseAperture t δ k ∧
      0 < oddTestMass t δ (phaseAperture t δ k) ∧
      2 * C₁ * Real.exp (2 * δ' * phaseAperture t δ k) +
          C₂ * (1 + phaseAperture t δ k) ^ 2 * Real.exp (2 * δ * phaseAperture t δ k) /
            oddTestMass t δ (phaseAperture t δ k) +
          M * oddTestCross t δ (phaseAperture t δ k) ^ 2 / oddTestMass t δ (phaseAperture t δ k) <
        M / 4 * (oddTestMass t δ (phaseAperture t δ k) -
          evenFloorMass t δ (phaseAperture t δ k)) := by
  set r := Real.sqrt (δ ^ 2 + t ^ 2) with hr_def
  have hr : 0 < r := sqrt_pos' ht hδ
  have hr2 : r ^ 2 = δ ^ 2 + t ^ 2 := sq_sqrt' ht hδ
  set ε := M / (32 * r) with hε_def
  have hε : 0 < ε := by positivity
  have hexp : Tendsto (fun a : ℝ => Real.exp (2 * δ * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  have hev : ∀ᶠ a in atTop,
      (Real.exp (2 * δ * a) / (4 * δ) ≤ Real.sinh (2 * δ * a) / δ - 2 * a - 1 / r) ∧
      (2 * C₁ * Real.exp (2 * δ' * a) ≤ ε * Real.exp (2 * δ * a)) ∧
      (4 * δ * C₂ * (1 + a) ^ 2 ≤ ε * Real.exp (2 * δ * a)) ∧
      (8 * δ / r + 5 ≤ Real.exp (2 * δ * a)) ∧ (1 ≤ a) :=
    (eventually_exp_div_le_sinh_sub hδ (1 / r)).and
      ((eventually_exp_le_eps_mul_exp hδ' (by positivity) hε).and
        ((eventually_sq_le_eps_mul_exp hδ (by positivity) hε).and
          ((hexp.eventually_ge_atTop _).and (eventually_ge_atTop 1))))
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨k, hk⟩ := exists_phaseAperture_gt ht δ (max A A₀)
  set a := phaseAperture t δ k with ha_def
  obtain ⟨h1, h2, h3, h4, h5⟩ := hA₀ a ((le_max_right A A₀).trans hk.le)
  have ha0 : 0 ≤ a := by linarith
  refine ⟨k, lt_of_le_of_lt (le_max_left A A₀) hk, by linarith, ?_⟩
  set e := Real.exp (2 * δ * a) with he_def
  have he1 : 1 ≤ e := by
    have : 0 < 8 * δ / r := by positivity
    linarith
  -- lower bound on `D⁻`
  have hD : e / (4 * δ) ≤ oddTestMass t δ a :=
    le_trans h1 (oddTestMass_ge_phaseAperture ht hδ k ha0)
  have hDpos : 0 < oddTestMass t δ a := lt_of_lt_of_le (by positivity) hD
  refine ⟨hDpos, ?_⟩
  set D := oddTestMass t δ a with hD_def
  -- the critical-line term
  have hP : C₂ * (1 + a) ^ 2 * e / D ≤ ε * e := by
    rw [div_le_iff₀ hDpos]
    have hDe : e ≤ 4 * δ * D := by
      rw [div_le_iff₀ (by positivity)] at hD
      linarith
    calc C₂ * (1 + a) ^ 2 * e ≤ C₂ * (1 + a) ^ 2 * (4 * δ * D) :=
          mul_le_mul_of_nonneg_left hDe (by positivity)
      _ = (4 * δ * C₂ * (1 + a) ^ 2) * D := by ring
      _ ≤ ε * e * D := mul_le_mul_of_nonneg_right h3 hDpos.le
  -- the cross term
  have hI2 : oddTestCross t δ a ^ 2 ≤ 1 / (16 * r ^ 2) := by
    rw [hr2]
    exact oddTestCross_sq_le_phaseAperture ht hδ k ha0
  have hI : M * oddTestCross t δ a ^ 2 / D ≤ ε * e := by
    rw [div_le_iff₀ hDpos]
    have hDe : e ≤ 4 * δ * D := by
      rw [div_le_iff₀ (by positivity)] at hD
      linarith
    have hee : 8 * δ / r ≤ e * e := by nlinarith
    have hstep : M * oddTestCross t δ a ^ 2 ≤ M * (1 / (16 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left hI2 hM.le
    have hkey : M * (1 / (16 * r ^ 2)) ≤ ε * e * (e / (4 * δ)) := by
      rw [hε_def]
      have h8 : 8 * δ ≤ r * (e * e) := by
        rw [div_le_iff₀ hr] at hee
        linarith
      rw [show M / (32 * r) * e * (e / (4 * δ)) = M * (e * e) / (128 * r * δ) by
        field_simp; ring]
      rw [show M * (1 / (16 * r ^ 2)) = M / (16 * r ^ 2) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h16 := mul_le_mul_of_nonneg_left h8 (show (0 : ℝ) ≤ 16 * M * r by positivity)
      calc M * (128 * r * δ) = 16 * M * r * (8 * δ) := by ring
        _ ≤ 16 * M * r * (r * (e * e)) := h16
        _ = M * (e * e) * (16 * r ^ 2) := by ring
    calc M * oddTestCross t δ a ^ 2 ≤ M * (1 / (16 * r ^ 2)) := hstep
      _ ≤ ε * e * (e / (4 * δ)) := hkey
      _ ≤ ε * e * D := mul_le_mul_of_nonneg_left hD (by positivity)
  -- the parity gap
  have hgap := gap_ge_phaseAperture ht hδ k
  have hsinh : e / 2 - 1 / 2 ≤ Real.sinh (2 * δ * a) := by
    rw [Real.sinh_eq]
    have : Real.exp (-(2 * δ * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hgap' : M / 4 * (2 * (e / 2 - 3 / 2) / r) ≤ M / 4 * (D - evenFloorMass t δ a) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans ?_ hgap
    apply div_le_div_of_nonneg_right _ hr.le
    linarith
  have hfinal : 3 * (ε * e) < M / 4 * (2 * (e / 2 - 3 / 2) / r) := by
    rw [hε_def]
    have h5' : (5 : ℝ) ≤ e := by
      have : 0 < 8 * δ / r := by positivity
      linarith
    rw [show M / 4 * (2 * (e / 2 - 3 / 2) / r) = M * (e - 3) / (4 * r) by field_simp]
    rw [show 3 * (M / (32 * r) * e) = M * (3 * e) / (32 * r) by field_simp]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < M * r := by positivity
    have h5'' := mul_le_mul_of_nonneg_left h5' hp.le
    calc M * (3 * e) * (4 * r) = 12 * (M * r) * e := by ring
      _ < 12 * (M * r) * e + 4 * (M * r) * (5 * e - 24) := by nlinarith
      _ = M * (e - 3) * (32 * r) := by ring
  linarith

end

end RHTower.CCMParityQuartet
