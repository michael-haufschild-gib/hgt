import GaloisForLFunctions.RHTower.ProlateHermiteRungWindowLimit
import GaloisForLFunctions.RHTower.HermiteFunctionOrthogonality

/-!
# The rung-`n` Rayleigh defect is a square

Rescaling the Hermite function to the bandwidth turns the prolate action into the oscillator ladder
value `−(2n+1)c` plus an explicit defect, and the defect integrates to a *square*:

```text
∫_{-R}^{R} ( −ξ² φ_n'' φ_n − 2ξ φ_n' φ_n ) dξ
     = ∫_{-R}^{R} ξ² (φ_n')² dξ  −  [ ξ² φ_n φ_n' ]_{-R}^{R} .
```

One integration by parts does it: the two correction terms of the quasi-eigenfunction identity are
exactly the two terms produced by differentiating `ξ² φ_n`.  Since the boundary term is a
polynomial times a Gaussian it vanishes at infinity, so the defect is eventually positive — with no
Hermite moment computation anywhere.

This is the upper-bound half of the rung-`n` separation constant: a trial function at the `n`-th
rung has prolate Rayleigh quotient above `−(2n+1)c`, uniformly for large bandwidth.
-/

open Filter Topology Set MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- The integrand of the rung-`n` Rayleigh defect. -/
def hermiteRungDefect (n : ℕ) (ξ : ℝ) : ℝ :=
  -(ξ ^ 2 * ((ξ ^ 2 - 2 * n - 1) * hermiteFun n ξ) * hermiteFun n ξ)
    - 2 * ξ * deriv (hermiteFun n) ξ * hermiteFun n ξ

theorem continuous_hermiteRungIntegrandA (n : ℕ) :
    Continuous fun ξ : ℝ => ξ ^ 2 * ((ξ ^ 2 - 2 * (n : ℝ) - 1) * hermiteFun n ξ) * hermiteFun n ξ :=
  ((continuous_pow 2).mul ((((continuous_pow 2).sub continuous_const).sub continuous_const).mul
    (continuous_hermiteFun n))).mul (continuous_hermiteFun n)

theorem continuous_hermiteRungIntegrandB (n : ℕ) :
    Continuous fun ξ : ℝ => 2 * ξ * deriv (hermiteFun n) ξ * hermiteFun n ξ :=
  ((continuous_const.mul continuous_id).mul (continuous_deriv_hermiteFun n)).mul
    (continuous_hermiteFun n)

theorem continuous_hermiteRungSquare (n : ℕ) :
    Continuous fun ξ : ℝ => ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2 :=
  (continuous_pow 2).mul ((continuous_deriv_hermiteFun n).pow 2)

theorem continuous_hermiteRungU (n : ℕ) :
    Continuous fun ξ : ℝ => 2 * ξ * hermiteFun n ξ + ξ ^ 2 * deriv (hermiteFun n) ξ :=
  ((continuous_const.mul continuous_id).mul (continuous_hermiteFun n)).add
    ((continuous_pow 2).mul (continuous_deriv_hermiteFun n))

theorem continuous_hermiteRungV (n : ℕ) :
    Continuous fun ξ : ℝ => (ξ ^ 2 - 2 * (n : ℝ) - 1) * hermiteFun n ξ :=
  (((continuous_pow 2).sub continuous_const).sub continuous_const).mul (continuous_hermiteFun n)

theorem continuous_hermiteRungDefect (n : ℕ) : Continuous (hermiteRungDefect n) :=
  (continuous_hermiteRungIntegrandA n).neg.sub (continuous_hermiteRungIntegrandB n)

/-- **The defect is a square up to a boundary term.**  One integration by parts, using only the
oscillator equation. -/
theorem integral_hermiteRungDefect (n : ℕ) (R : ℝ) :
    (∫ ξ in (-R)..R, hermiteRungDefect n ξ)
      = (∫ ξ in (-R)..R, ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2)
        - (R ^ 2 * hermiteFun n R * deriv (hermiteFun n) R
            - (-R) ^ 2 * hermiteFun n (-R) * deriv (hermiteFun n) (-R)) := by
  set u : ℝ → ℝ := fun ξ => ξ ^ 2 * hermiteFun n ξ with hu
  set u' : ℝ → ℝ := fun ξ => 2 * ξ * hermiteFun n ξ + ξ ^ 2 * deriv (hermiteFun n) ξ with hu'
  set v : ℝ → ℝ := deriv (hermiteFun n) with hv
  set v' : ℝ → ℝ := fun ξ => (ξ ^ 2 - 2 * n - 1) * hermiteFun n ξ with hv'
  have hud : ∀ ξ ∈ uIcc (-R) R, HasDerivAt u (u' ξ) ξ := by
    intro ξ _
    have h := ((hasDerivAt_pow 2 ξ).mul (hasDerivAt_hermiteFun n ξ))
    refine h.congr_deriv ?_
    simp only [hu']
    push_cast
    ring
  have hvd : ∀ ξ ∈ uIcc (-R) R, HasDerivAt v (v' ξ) ξ := by
    intro ξ _
    have h := hasDerivAt_deriv_hermiteFun n ξ
    refine h.congr_deriv ?_
    simp only [hv', hermiteRungP]
    ring
  have hu'i : IntervalIntegrable u' volume (-R) R :=
    (continuous_hermiteRungU n).intervalIntegrable _ _
  have hv'i : IntervalIntegrable v' volume (-R) R :=
    (continuous_hermiteRungV n).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud hvd hu'i hv'i
  have hlhs : (∫ ξ in (-R)..R, u ξ * v' ξ)
      = ∫ ξ in (-R)..R, ξ ^ 2 * ((ξ ^ 2 - 2 * n - 1) * hermiteFun n ξ) * hermiteFun n ξ := by
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [hu, hv']
    ring
  have hrhs : (∫ ξ in (-R)..R, u' ξ * v ξ)
      = (∫ ξ in (-R)..R, 2 * ξ * deriv (hermiteFun n) ξ * hermiteFun n ξ)
        + ∫ ξ in (-R)..R, ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2 := by
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun ξ _ => ?_
      simp only [hu', hv]
      ring
    · exact (continuous_hermiteRungIntegrandB n).intervalIntegrable _ _
    · exact (continuous_hermiteRungSquare n).intervalIntegrable _ _
  have hdef : (∫ ξ in (-R)..R, hermiteRungDefect n ξ)
      = -(∫ ξ in (-R)..R, ξ ^ 2 * ((ξ ^ 2 - 2 * n - 1) * hermiteFun n ξ) * hermiteFun n ξ)
        - ∫ ξ in (-R)..R, 2 * ξ * deriv (hermiteFun n) ξ * hermiteFun n ξ := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun ξ _ => ?_
      simp only [hermiteRungDefect]
    · exact ((continuous_hermiteRungIntegrandA n).neg).intervalIntegrable _ _
    · exact (continuous_hermiteRungIntegrandB n).intervalIntegrable _ _
  rw [hdef]
  have hA : (∫ ξ in (-R)..R, ξ ^ 2 * ((ξ ^ 2 - 2 * (n : ℝ) - 1) * hermiteFun n ξ)
        * hermiteFun n ξ)
      = u R * v R - u (-R) * v (-R) - ∫ ξ in (-R)..R, u' ξ * v ξ := by
    rw [← hlhs]
    exact hparts
  rw [hA, hrhs]
  simp only [hu, hv]
  ring

/-! ### The boundary term vanishes -/

/-- `x² φ_n(x)` as a polynomial times a Gaussian. -/
theorem sq_mul_hermiteFun_eq (n : ℕ) (x : ℝ) :
    x ^ 2 * hermiteFun n x
      = (Polynomial.X ^ 2 * ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).comp
            (Polynomial.C (Real.sqrt 2) * Polynomial.X)).eval x
        * Real.exp (-(1 / 2 * x ^ 2)) := by
  have hx : (Real.sqrt 2 * x) ^ 2 / 4 = 1 / 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hmap : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
      = ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval (Real.sqrt 2 * x) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_C]
  rw [← hmap]
  show x ^ 2 * (Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
      * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4))) = _
  rw [hx]
  ring

theorem tendsto_sq_mul_hermiteFun_atTop (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ 2 * hermiteFun n x) atTop (𝓝 0) := by
  refine (tendsto_polyEval_mul_gauss_atTop
    (Polynomial.X ^ 2 * ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).comp
      (Polynomial.C (Real.sqrt 2) * Polynomial.X)) (by norm_num : (0 : ℝ) < 1 / 2)).congr ?_
  intro x
  exact (sq_mul_hermiteFun_eq n x).symm

theorem tendsto_sq_mul_hermiteFun_atBot (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ 2 * hermiteFun n x) atBot (𝓝 0) := by
  refine (tendsto_polyEval_mul_gauss_atBot
    (Polynomial.X ^ 2 * ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).comp
      (Polynomial.C (Real.sqrt 2) * Polynomial.X)) (by norm_num : (0 : ℝ) < 1 / 2)).congr ?_
  intro x
  exact (sq_mul_hermiteFun_eq n x).symm

/-- **The boundary term of the defect vanishes at infinity.** -/
theorem tendsto_hermiteRungBoundary (n : ℕ) :
    Tendsto (fun R : ℝ => R ^ 2 * hermiteFun n R * deriv (hermiteFun n) R
        - (-R) ^ 2 * hermiteFun n (-R) * deriv (hermiteFun n) (-R)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => R ^ 2 * hermiteFun n R * deriv (hermiteFun n) R) atTop (𝓝 0) := by
    have := (tendsto_sq_mul_hermiteFun_atTop n).mul (tendsto_deriv_hermiteFun_atTop n)
    simpa using this
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have h2 : Tendsto (fun R : ℝ => (-R) ^ 2 * hermiteFun n (-R) * deriv (hermiteFun n) (-R))
      atTop (𝓝 0) := by
    have hA : Tendsto (fun R : ℝ => (-R) ^ 2 * hermiteFun n (-R)) atTop (𝓝 0) :=
      (tendsto_sq_mul_hermiteFun_atBot n).comp hneg
    have hB : Tendsto (fun R : ℝ => deriv (hermiteFun n) (-R)) atTop (𝓝 0) :=
      (tendsto_deriv_hermiteFun_atBot n).comp hneg
    simpa using hA.mul hB
  simpa using h1.sub h2

/-! ### The square has positive mass -/

theorem exists_deriv_hermiteFun_ne_zero (n : ℕ) : ∃ x : ℝ, deriv (hermiteFun n) x ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hconst : ∀ x : ℝ, hermiteFun n x = hermiteFun n 0 :=
    fun x => is_const_of_deriv_eq_zero (differentiable_hermiteFun n) hcon x 0
  have hlim : Tendsto (hermiteFun n) atTop (𝓝 (hermiteFun n 0)) := by
    have hfun : (fun x : ℝ => hermiteFun n x) = fun _ : ℝ => hermiteFun n 0 := funext hconst
    rw [show hermiteFun n = fun x : ℝ => hermiteFun n x from rfl, hfun]
    exact tendsto_const_nhds
  have hzero : hermiteFun n 0 = 0 :=
    tendsto_nhds_unique hlim (tendsto_hermiteFun_atTop n)
  obtain ⟨x, -, hx⟩ := exists_hermiteFun_ne_zero n (by norm_num : (0 : ℝ) < 1)
  exact hx (by rw [hconst x, hzero])

/-- A window away from the origin on which the derivative does not vanish. -/
theorem exists_window_deriv_ne_zero (n : ℕ) :
    ∃ a b : ℝ, a < b ∧ (0 < a ∨ b < 0) ∧ ∀ x ∈ Ioo a b, deriv (hermiteFun n) x ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_deriv_hermiteFun_ne_zero n
  have hopen : IsOpen {x : ℝ | deriv (hermiteFun n) x ≠ 0} :=
    (continuous_deriv_hermiteFun n).isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x₀ hx₀
  rcases le_or_gt 0 x₀ with hx | hx
  · refine ⟨x₀ + ε / 4, x₀ + ε / 2, by linarith, Or.inl (by linarith), fun x hx' => ?_⟩
    refine hball ?_
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hx'.1]; linarith [hx'.2]]
  · refine ⟨x₀ - ε / 2, x₀ - ε / 4, by linarith, Or.inr (by linarith), fun x hx' => ?_⟩
    refine hball ?_
    simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hx'.1]; linarith [hx'.2]]

/-- **The square has positive mass on a fixed window.** -/
theorem exists_pos_window_integral (n : ℕ) :
    ∃ a b : ℝ, a < b ∧ 0 < ∫ ξ in a..b, ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2 := by
  obtain ⟨a, b, hab, hsign, hne⟩ := exists_window_deriv_ne_zero n
  refine ⟨a, b, hab, ?_⟩
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_hermiteRungSquare n).intervalIntegrable _ _) (fun x hx => ?_) hab
  have hx0 : x ≠ 0 := by
    rcases hsign with h | h
    · exact ne_of_gt (lt_trans h hx.1)
    · exact ne_of_lt (lt_trans hx.2 h)
  have := hne x hx
  positivity

/-- **The rung-`n` Rayleigh defect is eventually positive.**  The defect is the square integral
minus a boundary term that vanishes at infinity. -/
theorem eventually_hermiteRungDefect_pos (n : ℕ) :
    ∀ᶠ R in atTop, 0 < ∫ ξ in (-R)..R, hermiteRungDefect n ξ := by
  obtain ⟨a, b, hab, hm⟩ := exists_pos_window_integral n
  set m : ℝ := ∫ ξ in a..b, ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2 with hmdef
  have hbd := (tendsto_hermiteRungBoundary n).eventually
    (eventually_abs_sub_lt (0 : ℝ) hm)
  filter_upwards [hbd, eventually_ge_atTop (|a| + |b| + 1)] with R hR hRbig
  have hRa : -R ≤ a := by
    have h1 : -|a| ≤ a := neg_abs_le a
    have h2 : (0 : ℝ) ≤ |b| := abs_nonneg b
    linarith
  have hRb : b ≤ R := by
    have h1 : b ≤ |b| := le_abs_self b
    have h2 : (0 : ℝ) ≤ |a| := abs_nonneg a
    linarith
  have hsq : m ≤ ∫ ξ in (-R)..R, ξ ^ 2 * deriv (hermiteFun n) ξ ^ 2 := by
    refine intervalIntegral.integral_mono_interval hRa hab.le hRb ?_
      ((continuous_hermiteRungSquare n).intervalIntegrable _ _)
    filter_upwards with x
    positivity
  have hbnd : |R ^ 2 * hermiteFun n R * deriv (hermiteFun n) R
      - (-R) ^ 2 * hermiteFun n (-R) * deriv (hermiteFun n) (-R)| < m := by
    simpa using hR
  rw [integral_hermiteRungDefect n R]
  have habs := abs_lt.1 hbnd
  linarith [habs.2]

/-! ### The rung-`n` trial function -/

/-- The rung-`n` trial function at bandwidth `c`. -/
def hermiteTrial (c : ℝ) (n : ℕ) (x : ℝ) : ℝ := hermiteFun n (Real.sqrt c * x)

/-- Pointwise form of the trial Rayleigh integrand. -/
theorem prolate_hermiteTrial_integrand {c : ℝ} (hc : 0 < c) (n : ℕ) (x : ℝ) :
    prolateSLAction c (hermiteTrial c n) x * hermiteTrial c n x
      = -((2 * n + 1) * c) * (hermiteTrial c n x * hermiteTrial c n x)
        + hermiteRungDefect n (Real.sqrt c * x) := by
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hxx : Real.sqrt c * x / Real.sqrt c = x := by field_simp
  have h := prolateSLAction_hermiteFun hc n (Real.sqrt c * x)
  rw [hxx] at h
  show prolateSLAction c (fun y => hermiteFun n (Real.sqrt c * y)) x
      * hermiteFun n (Real.sqrt c * x) = _
  rw [h]
  simp only [hermiteRungDefect, hermiteTrial]
  ring

/-- **The rung-`n` trial Rayleigh quotient exceeds the ladder value for large bandwidth.** -/
theorem eventually_prolate_hermiteTrial_rayleigh_gt (n : ℕ) :
    ∀ᶠ c in atTop,
      -((2 * n + 1) * c) * (∫ x in (-1 : ℝ)..1, hermiteTrial c n x * hermiteTrial c n x)
        < ∫ x in (-1 : ℝ)..1, prolateSLAction c (hermiteTrial c n) x * hermiteTrial c n x := by
  have hsqrt : Tendsto (fun c : ℝ => Real.sqrt c) atTop atTop := Real.tendsto_sqrt_atTop
  have hdef := hsqrt.eventually (eventually_hermiteRungDefect_pos n)
  filter_upwards [hdef, eventually_gt_atTop (0 : ℝ)] with c hpos hc
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hspos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsub : (∫ x in (-1 : ℝ)..1, hermiteRungDefect n (Real.sqrt c * x))
      = (Real.sqrt c)⁻¹ • ∫ ξ in (Real.sqrt c * (-1))..(Real.sqrt c * 1), hermiteRungDefect n ξ :=
    intervalIntegral.integral_comp_mul_left (c := Real.sqrt c) _ hs
  have hsplit : (∫ x in (-1 : ℝ)..1, prolateSLAction c (hermiteTrial c n) x * hermiteTrial c n x)
      = -((2 * n + 1) * c) * (∫ x in (-1 : ℝ)..1, hermiteTrial c n x * hermiteTrial c n x)
        + ∫ x in (-1 : ℝ)..1, hermiteRungDefect n (Real.sqrt c * x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      exact prolate_hermiteTrial_integrand hc n x
    · refine Continuous.intervalIntegrable ?_ _ _
      exact (continuous_const.mul
        (((continuous_hermiteFun n).comp (continuous_const.mul continuous_id)).mul
          ((continuous_hermiteFun n).comp (continuous_const.mul continuous_id))))
    · exact ((continuous_hermiteRungDefect n).comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [hsplit, hsub]
  have hpos' : 0 < ∫ ξ in (Real.sqrt c * (-1))..(Real.sqrt c * 1), hermiteRungDefect n ξ := by
    have hrw : Real.sqrt c * (-1) = -Real.sqrt c := by ring
    have hrw' : Real.sqrt c * 1 = Real.sqrt c := by ring
    rw [hrw, hrw']
    exact hpos
  have : (0 : ℝ) < (Real.sqrt c)⁻¹ • ∫ ξ in (Real.sqrt c * (-1))..(Real.sqrt c * 1),
      hermiteRungDefect n ξ := by
    rw [smul_eq_mul]
    exact mul_pos (inv_pos.2 hspos) hpos'
  linarith

end RHTower

end
