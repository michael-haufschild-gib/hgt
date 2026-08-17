import GaloisForLFunctions.RHTower.BesselIZeroODE

/-!
# `I₀` from above

The integral representation `I₀(z) = (1/π)∫₀^π cosh(z sin θ) dθ` gives the matching upper Laplace
bound to the corpus's lower one: `cosh ≤ exp` on the positive axis, Jordan's inequality turns
`sin θ ≤ 1 − 2(θ − π/2)²/π²` into a Gaussian, and the Gaussian integral over the line dominates the
integral over `[0, π]`.

`besselI0 z ≤ exp z · sqrt (π / (2 z))`

The exponential rate and the `z^{-1/2}` are sharp; the constant is not.  Together with
`exp_div_le_besselI0` this traps `I₀` two-sidedly with the same shape, which is what the collar
comparison of the prolate band mode consumes.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.2 (by linarith)
  linarith

/-- The quadratic upper bound for the sine on `[0, π]`, from Jordan's inequality. -/
theorem sin_le_one_sub_sq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    Real.sin θ ≤ 1 - 2 * (θ - Real.pi / 2) ^ 2 / Real.pi ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set u : ℝ := θ - Real.pi / 2 with hu
  have hu1 : |u| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> [linarith; linarith]
  have hsin : Real.sin θ = Real.cos u := by
    rw [hu]
    rw [show θ - Real.pi / 2 = -(Real.pi / 2 - θ) by ring, Real.cos_neg,
      Real.cos_pi_div_two_sub]
  have hhalf : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    have h2 : Real.sin (u / 2) ^ 2 = (1 - Real.cos u) / 2 := by
      have hpy := Real.sin_sq_add_cos_sq (u / 2)
      have hc := Real.cos_two_mul (u / 2)
      have hval : Real.cos (2 * (u / 2)) = Real.cos u := by
        congr 1
        ring
      rw [hval] at hc
      linarith
    rw [h2]
    ring
  have hjordan : |u| / Real.pi ≤ Real.sin (|u| / 2) := by
    have h0' : (0 : ℝ) ≤ |u| / 2 := by positivity
    have h1' : |u| / 2 ≤ Real.pi / 2 := by linarith [abs_nonneg u, hu1]
    have := Real.mul_le_sin h0' h1'
    calc |u| / Real.pi = 2 / Real.pi * (|u| / 2) := by ring
      _ ≤ Real.sin (|u| / 2) := this
  have hsq : Real.sin (u / 2) ^ 2 = Real.sin (|u| / 2) ^ 2 := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      rw [show -u / 2 = -(u / 2) by ring, Real.sin_neg]
      ring
  have hnn : (0 : ℝ) ≤ |u| / Real.pi := by positivity
  have hmul := mul_self_le_mul_self hnn hjordan
  have habs : |u| * |u| = u ^ 2 := by
    rw [abs_mul_abs_self u]
    ring
  have he1 : (|u| / Real.pi) * (|u| / Real.pi) = u ^ 2 / Real.pi ^ 2 := by
    rw [div_mul_div_comm, habs]
    ring
  have hlow : u ^ 2 / Real.pi ^ 2 ≤ Real.sin (u / 2) ^ 2 := by
    have h2 : Real.sin (|u| / 2) ^ 2 = Real.sin (|u| / 2) * Real.sin (|u| / 2) := pow_two _
    rw [hsq, h2, ← he1]
    exact hmul
  have hdiv : 2 * u ^ 2 / Real.pi ^ 2 = 2 * (u ^ 2 / Real.pi ^ 2) := by ring
  rw [hsin, hhalf]
  linarith [hlow, hdiv.le, hdiv.ge]

/-- **`I₀` from above.**  The exponential rate and the `z^{-1/2}` are sharp; the constant is not. -/
theorem besselI0_le_exp_div_sqrt {z : ℝ} (hz : 0 < z) :
    besselI0 z ≤ Real.exp z * Real.sqrt (Real.pi / (2 * z)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set b : ℝ := 2 * z / Real.pi ^ 2 with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  -- pointwise bound on the integrand
  have hpt : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      Real.cosh (z * Real.sin θ) ≤ Real.exp z * Real.exp (-(b * (θ - Real.pi / 2) ^ 2)) := by
    intro θ hθ
    rw [uIcc_of_le hpi.le] at hθ
    have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have h1 : Real.cosh (z * Real.sin θ) ≤ Real.exp (z * Real.sin θ) :=
      cosh_le_exp_of_nonneg (by positivity)
    have h2 : z * Real.sin θ ≤ z - b * (θ - Real.pi / 2) ^ 2 := by
      have := sin_le_one_sub_sq hθ.1 hθ.2
      have hmul := mul_le_mul_of_nonneg_left this hz.le
      have hval : z * (1 - 2 * (θ - Real.pi / 2) ^ 2 / Real.pi ^ 2)
          = z - b * (θ - Real.pi / 2) ^ 2 := by
        rw [hb]
        field_simp
      linarith [hmul, hval.le, hval.ge]
    refine le_trans h1 ?_
    have h3 : Real.exp (z * Real.sin θ) ≤ Real.exp (z - b * (θ - Real.pi / 2) ^ 2) :=
      Real.exp_le_exp.2 h2
    rw [show z - b * (θ - Real.pi / 2) ^ 2 = z + -(b * (θ - Real.pi / 2) ^ 2) by ring,
      Real.exp_add] at h3
    exact h3
  -- integrate
  have hcont1 : Continuous fun θ : ℝ => Real.cosh (z * Real.sin θ) :=
    Real.continuous_cosh.comp (continuous_const.mul Real.continuous_sin)
  have hcont2 : Continuous fun θ : ℝ =>
      Real.exp z * Real.exp (-(b * (θ - Real.pi / 2) ^ 2)) := by
    refine continuous_const.mul (Real.continuous_exp.comp ?_)
    fun_prop
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, Real.cosh (z * Real.sin θ))
      ≤ ∫ θ in (0 : ℝ)..Real.pi, Real.exp z * Real.exp (-(b * (θ - Real.pi / 2) ^ 2)) := by
    refine intervalIntegral.integral_mono_on hpi.le (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) ?_
    intro θ hθ
    exact hpt θ (by rw [uIcc_of_le hpi.le]; exact hθ)
  -- the Gaussian
  have hgauss : (∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(b * (θ - Real.pi / 2) ^ 2)))
      ≤ Real.sqrt (Real.pi / b) := by
    have hshift : (∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(b * (θ - Real.pi / 2) ^ 2)))
        = ∫ u in (0 - Real.pi / 2)..(Real.pi - Real.pi / 2),
            Real.exp (-(b * u ^ 2)) :=
      intervalIntegral.integral_comp_sub_right
        (fun u => Real.exp (-(b * u ^ 2))) (Real.pi / 2)
    have hint : Integrable fun u : ℝ => Real.exp (-(b * u ^ 2)) := by
      simpa [neg_mul] using integrable_exp_neg_mul_sq hb0
    have hnn : ∀ u : ℝ, (0 : ℝ) ≤ Real.exp (-(b * u ^ 2)) := fun u => (Real.exp_pos _).le
    have hle : (∫ u in (0 - Real.pi / 2)..(Real.pi - Real.pi / 2), Real.exp (-(b * u ^ 2)))
        ≤ ∫ u : ℝ, Real.exp (-(b * u ^ 2)) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun u => hnn u)
    have hval : (∫ u : ℝ, Real.exp (-(b * u ^ 2))) = Real.sqrt (Real.pi / b) := by
      simpa [neg_mul] using integral_gaussian b
    rw [hshift]
    rw [← hval]
    exact hle
  have hconst : (∫ θ in (0 : ℝ)..Real.pi,
      Real.exp z * Real.exp (-(b * (θ - Real.pi / 2) ^ 2)))
      = Real.exp z * ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(b * (θ - Real.pi / 2) ^ 2)) :=
    intervalIntegral.integral_const_mul _ _
  have hkey : (∫ θ in (0 : ℝ)..Real.pi, Real.cosh (z * Real.sin θ))
      ≤ Real.exp z * Real.sqrt (Real.pi / b) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hgauss (Real.exp_pos z).le)
  have hbval : Real.pi / b = Real.pi ^ 2 * (Real.pi / (2 * z)) := by
    rw [hb]
    field_simp
  have hsq : Real.sqrt (Real.pi / b) = Real.pi * Real.sqrt (Real.pi / (2 * z)) := by
    rw [hbval, Real.sqrt_mul (by positivity), Real.sqrt_sq hpi.le]
  rw [besselI0]
  rw [hsq] at hkey
  have hπ : (0 : ℝ) < 1 / Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hkey hπ.le
  calc (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cosh (z * Real.sin θ)
      ≤ (1 / Real.pi) * (Real.exp z * (Real.pi * Real.sqrt (Real.pi / (2 * z)))) := this
    _ = Real.exp z * Real.sqrt (Real.pi / (2 * z)) := by
        field_simp

end GaloisForLFunctions.RHTower

end
