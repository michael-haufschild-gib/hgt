import Mathlib

/-!
# The modified Bessel function of order zero

At the regular singular endpoint of the prolate band the model equation is the *modified* Bessel
equation, not Bessel's: writing `u = 1 − y` and `K = χ + c²`, the Sturm form
`((1−y²)Φ')' = (χ + c²y²)Φ` becomes `(u Φ_u)_u = (K/2)Φ`, and `z = √(2Ku)` turns it into

```text
I'' + I'/z − I = 0 .
```

The band side of the endpoint is the *forbidden* region, so the model is `I₀`, `K₀`, whereas the
radial side — which the corpus already treats through `besselJ0` — is the allowed one with `J₀`,
`Y₀`.  mathlib has neither family; this file builds `I₀` from its integral representation exactly as
the corpus builds `J₀`, replacing the circular functions in the integrand by the hyperbolic ones.

The one structural difference is the domination: `cos` is bounded, `cosh` is not, so differentiation
under the integral sign is justified on a ball rather than on the whole line.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The modified Bessel function of order zero, by its integral representation. -/
def besselI0 (u : ℝ) : ℝ := (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (u * Real.sin θ)

/-- Its derivative, as an integral. -/
def besselI0Deriv (u : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sinh (u * Real.sin θ)

/-- Its second derivative, as an integral. -/
def besselI0SecondDeriv (u : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 2 * Real.cosh (u * Real.sin θ)

theorem continuous_cosh_mul_sin (u : ℝ) :
    Continuous fun θ : ℝ => Real.cosh (u * Real.sin θ) := by fun_prop

theorem continuous_sin_mul_sinh (u : ℝ) :
    Continuous fun θ : ℝ => Real.sin θ * Real.sinh (u * Real.sin θ) := by fun_prop

theorem continuous_sin_sq_mul_cosh (u : ℝ) :
    Continuous fun θ : ℝ => Real.sin θ ^ 2 * Real.cosh (u * Real.sin θ) := by fun_prop

theorem continuous_cos_sq_mul_cosh (u : ℝ) :
    Continuous fun θ : ℝ => Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ) := by fun_prop

/-! ## Elementary bounds -/

theorem abs_sinh_le {t M : ℝ} (h : |t| ≤ M) : |Real.sinh t| ≤ Real.sinh M := by
  rw [abs_le] at h
  rw [abs_le]
  constructor
  · have := Real.sinh_le_sinh.2 h.1
    have hodd : Real.sinh (-M) = -Real.sinh M := Real.sinh_neg M
    have h2 : Real.sinh (-M) ≤ Real.sinh t := Real.sinh_le_sinh.2 (by linarith)
    linarith [hodd ▸ h2]
  · exact Real.sinh_le_sinh.2 h.2

theorem cosh_le_cosh_of_abs_le {t M : ℝ} (h : |t| ≤ M) : Real.cosh t ≤ Real.cosh M := by
  have habs : Real.cosh t = Real.cosh |t| := (Real.cosh_abs t).symm
  rw [habs]
  exact Real.cosh_le_cosh.2 (by rwa [abs_abs, abs_of_nonneg (le_trans (abs_nonneg t) h)])

theorem abs_mul_sin_le {x θ : ℝ} : |x * Real.sin θ| ≤ |x| := by
  rw [abs_mul]
  have h := Real.abs_sin_le_one θ
  nlinarith [abs_nonneg x, abs_nonneg (Real.sin θ)]

/-! ## Differentiation under the integral sign -/

theorem hasDerivAt_besselI0 (u : ℝ) : HasDerivAt besselI0 (besselI0Deriv u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi)
    (bound := fun _ : ℝ => Real.sinh (|u| + 1))
    (F := fun (x : ℝ) (θ : ℝ) => Real.cosh (x * Real.sin θ))
    (F' := fun (x : ℝ) (θ : ℝ) => Real.sin θ * Real.sinh (x * Real.sin θ))
    (x₀ := u) (s := Metric.ball u 1) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_cosh_mul_sin x).aestronglyMeasurable).restrict)
    ((continuous_cosh_mul_sin u).intervalIntegrable _ _)
    (((continuous_sin_mul_sinh u).aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun θ _ x hx => by
      have hxu : |x| ≤ |u| + 1 := by
        have := Metric.mem_ball.1 hx
        rw [Real.dist_eq] at this
        cases' abs_le.1 (le_of_lt this) with h1 h2
        rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;>
          rcases abs_cases x with ⟨hx1, _⟩ | ⟨hx1, _⟩ <;> linarith
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have h2 : |Real.sinh (x * Real.sin θ)| ≤ Real.sinh (|u| + 1) :=
        abs_sinh_le (le_trans abs_mul_sin_le hxu)
      have h3 : (0 : ℝ) ≤ Real.sinh (|u| + 1) := by
        have : (0 : ℝ) ≤ |u| + 1 := by positivity
        simpa using Real.sinh_nonneg_iff.2 this
      nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.sinh (x * Real.sin θ))])
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.sin θ) (Real.sin θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.sin θ)
      have h := (Real.hasDerivAt_cosh (x * Real.sin θ)).comp x hinner
      refine h.congr_deriv ?_
      ring)
  have hderiv := hmain.2
  have h := hderiv.const_mul (1 / Real.pi)
  have hb : besselI0 = fun x : ℝ => (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
      Real.cosh (x * Real.sin θ) := rfl
  rw [hb]
  exact h

theorem hasDerivAt_besselI0Deriv (u : ℝ) :
    HasDerivAt besselI0Deriv (besselI0SecondDeriv u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi)
    (bound := fun _ : ℝ => Real.cosh (|u| + 1))
    (F := fun (x : ℝ) (θ : ℝ) => Real.sin θ * Real.sinh (x * Real.sin θ))
    (F' := fun (x : ℝ) (θ : ℝ) => Real.sin θ ^ 2 * Real.cosh (x * Real.sin θ))
    (x₀ := u) (s := Metric.ball u 1) (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_sin_mul_sinh x).aestronglyMeasurable).restrict)
    ((continuous_sin_mul_sinh u).intervalIntegrable _ _)
    (((continuous_sin_sq_mul_cosh u).aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun θ _ x hx => by
      have hxu : |x| ≤ |u| + 1 := by
        have := Metric.mem_ball.1 hx
        rw [Real.dist_eq] at this
        cases' abs_le.1 (le_of_lt this) with h1 h2
        rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;>
          rcases abs_cases x with ⟨hx1, _⟩ | ⟨hx1, _⟩ <;> linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      have h1 : Real.sin θ ^ 2 ≤ 1 := by
        nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
      have h2 : |Real.cosh (x * Real.sin θ)| ≤ Real.cosh (|u| + 1) := by
        rw [abs_of_nonneg ((Real.cosh_pos _).le)]
        exact cosh_le_cosh_of_abs_le (le_trans abs_mul_sin_le hxu)
      have h3 : (0 : ℝ) ≤ Real.cosh (|u| + 1) := (Real.cosh_pos _).le
      nlinarith [sq_nonneg (Real.sin θ), abs_nonneg (Real.cosh (x * Real.sin θ))])
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.sin θ) (Real.sin θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.sin θ)
      have h := ((Real.hasDerivAt_sinh (x * Real.sin θ)).comp x hinner).const_mul (Real.sin θ)
      refine h.congr_deriv ?_
      ring)
  have hderiv := hmain.2
  have h := hderiv.const_mul (1 / Real.pi)
  have hb : besselI0Deriv = fun x : ℝ => (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.sinh (x * Real.sin θ) := rfl
  rw [hb]
  exact h

/-! ## The integration by parts -/

/-- The boundary terms vanish, so the first moment of `sinh(u sin θ)` is the `cos²`-weighted
hyperbolic cosine integral. -/
theorem integral_sin_mul_sinh_eq (u : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sinh (u * Real.sin θ))
      = u * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ) := by
  have hf : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt Real.cos (-Real.sin x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hg : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => Real.sinh (u * Real.sin θ))
        (u * Real.cos x * Real.cosh (u * Real.sin x)) x := by
    intro x _
    have hinner : HasDerivAt (fun θ : ℝ => u * Real.sin θ) (u * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul u
    have h := (Real.hasDerivAt_sinh (u * Real.sin x)).comp x hinner
    refine h.congr_deriv ?_
    ring
  have hf' : IntervalIntegrable (fun x : ℝ => -Real.sin x) volume 0 Real.pi :=
    (Real.continuous_sin.neg).intervalIntegrable _ _
  have hg' : IntervalIntegrable
      (fun x : ℝ => u * Real.cos x * Real.cosh (u * Real.sin x)) volume 0 Real.pi := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hg hf' hg'
  have hbdry : Real.cos Real.pi * Real.sinh (u * Real.sin Real.pi)
      - Real.cos 0 * Real.sinh (u * Real.sin 0) = 0 := by
    simp
  rw [hbdry] at hibp
  have hleft : (∫ x in (0 : ℝ)..Real.pi,
      Real.cos x * (u * Real.cos x * Real.cosh (u * Real.sin x)))
      = u * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  have hright : (∫ x in (0 : ℝ)..Real.pi, -Real.sin x * Real.sinh (u * Real.sin x))
      = -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sinh (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [hleft, hright] at hibp
  linarith [hibp]

/-! ## The modified Bessel equation -/

theorem besselI0SecondDeriv_sub_besselI0 (u : ℝ) :
    besselI0SecondDeriv u - besselI0 u
      = -((1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
          Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ)) := by
  have hsub : (∫ θ in (0 : ℝ)..Real.pi, Real.cosh (u * Real.sin θ))
      - ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 2 * Real.cosh (u * Real.sin θ)
      = ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_sub ((continuous_cosh_mul_sin u).intervalIntegrable _ _)
      ((continuous_sin_sq_mul_cosh u).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hpy : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpy]
    ring
  rw [besselI0SecondDeriv, besselI0, ← hsub]
  ring

/-- **The modified Bessel equation of order zero.**  The integral representation is a genuine
solution, so the endpoint model of the prolate band is available in the same form as the radial
model. -/
theorem besselI0_ode {u : ℝ} (hu : u ≠ 0) :
    besselI0SecondDeriv u + besselI0Deriv u / u - besselI0 u = 0 := by
  have hkey := integral_sin_mul_sinh_eq u
  have hsum := besselI0SecondDeriv_sub_besselI0 u
  have hd : besselI0Deriv u / u
      = (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cosh (u * Real.sin θ) := by
    rw [besselI0Deriv, hkey]
    field_simp
  rw [hd]
  linarith [hsum]

/-! ## Basic values and positivity -/

theorem besselI0_zero : besselI0 0 = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [besselI0]
  have : (∫ _θ in (0 : ℝ)..Real.pi, Real.cosh (0 * Real.sin _θ)) = Real.pi := by
    simp
  rw [this]
  field_simp

theorem besselI0_pos (u : ℝ) : 0 < besselI0 u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hint : (0 : ℝ) < ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (u * Real.sin θ) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_cosh_mul_sin u).intervalIntegrable _ _) (fun θ _ => ?_) hpi
    exact Real.cosh_pos _
  rw [besselI0]
  positivity

/-! ## Monotonicity and the logarithmic derivative -/

theorem besselI0Deriv_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ besselI0Deriv u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hint : (0 : ℝ) ≤ ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sinh (u * Real.sin θ) := by
    refine intervalIntegral.integral_nonneg hpi.le fun θ hθ => ?_
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hsh : 0 ≤ Real.sinh (u * Real.sin θ) := by
      simpa using Real.sinh_nonneg_iff.2 (mul_nonneg hu hs)
    exact mul_nonneg hs hsh
  rw [besselI0Deriv]
  positivity

theorem monotoneOn_besselI0 : MonotoneOn besselI0 (Ici (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_besselI0 x).continuousAt).continuousOn
    (fun x _ => (hasDerivAt_besselI0 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hasDerivAt_besselI0 x).deriv]
  exact besselI0Deriv_nonneg (le_of_lt hx)

/-- **The logarithmic derivative of the analytic branch is at most one.**  Pointwise
`sin θ · sinh(u sin θ) ≤ cosh(u sin θ)`, because `sin θ ≤ 1` and `sinh ≤ cosh`. -/
theorem besselI0Deriv_le_besselI0 {u : ℝ} (hu : 0 ≤ u) : besselI0Deriv u ≤ besselI0 u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sinh (u * Real.sin θ))
      ≤ ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (u * Real.sin θ) := by
    refine intervalIntegral.integral_mono_on hpi.le
      ((continuous_sin_mul_sinh u).intervalIntegrable _ _)
      ((continuous_cosh_mul_sin u).intervalIntegrable _ _) fun θ hθ => ?_
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hsh : 0 ≤ Real.sinh (u * Real.sin θ) := by
      simpa using Real.sinh_nonneg_iff.2 (mul_nonneg hu hs)
    have hshc : Real.sinh (u * Real.sin θ) ≤ Real.cosh (u * Real.sin θ) := by
      have := Real.sinh_lt_cosh (u * Real.sin θ)
      linarith
    nlinarith [hs, hs1, hsh, hshc]
  rw [besselI0Deriv, besselI0]
  have : (0 : ℝ) < 1 / Real.pi := by positivity
  exact mul_le_mul_of_nonneg_left hmono this.le

theorem besselI0_logDeriv_le_one {u : ℝ} (hu : 0 ≤ u) :
    besselI0Deriv u / besselI0 u ≤ 1 := by
  have hpos := besselI0_pos u
  rw [div_le_one hpos]
  exact besselI0Deriv_le_besselI0 hu

end GaloisForLFunctions.RHTower
