import GaloisForLFunctions.RHTower.HeatEnergyCoefficients
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The canonical nonzero tangent of the regularized germ

The linear coefficient of the Jonquière remainder is `i ζ(s-1)`, and `ζ(s-1)` is nonzero
throughout the Goldilocks strip.  This is the card's `(11b)`/`(11c)`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- **The zeta value one step to the left, through the functional equation.** -/
theorem riemannZeta_sub_one_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (s - 1)
      = -(2 * ((2 * ↑Real.pi : ℂ)) ^ (s - 2) * Complex.Gamma (2 - s)
          * Complex.cos (↑Real.pi * s / 2) * riemannZeta (2 - s)) := by
  have hu : ∀ n : ℕ, (2 - s) ≠ -(n : ℂ) := by
    intro n hcon
    have hre : (2 - s).re = -(n : ℝ) := by rw [hcon]; simp
    simp only [Complex.sub_re] at hre
    norm_num at hre
    have hm : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hu1 : (2 - s) ≠ 1 := by
    intro hcon
    have hre : (2 - s).re = 1 := by rw [hcon]; simp
    simp only [Complex.sub_re] at hre
    norm_num at hre
    linarith
  have hfe := riemannZeta_one_sub hu hu1
  rw [show (1 : ℂ) - (2 - s) = s - 1 by ring] at hfe
  rw [hfe]
  have hcos : Complex.cos (↑Real.pi * (2 - s) / 2) = -Complex.cos (↑Real.pi * s / 2) := by
    rw [show (↑Real.pi * (2 - s) / 2 : ℂ) = ↑Real.pi - ↑Real.pi * s / 2 by ring]
    exact Complex.cos_pi_sub _
  rw [hcos, show (-(2 - s) : ℂ) = s - 2 by ring]
  ring

/-- **`ζ(s-1)` does not vanish in the Goldilocks strip.** -/
theorem riemannZeta_sub_one_ne_zero {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    riemannZeta (s - 1) ≠ 0 := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [riemannZeta_sub_one_eq h0' h1]
  have hbase : ((2 * ↑Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr hpi.ne'⟩
  have hpow : ((2 * ↑Real.pi : ℂ)) ^ (s - 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hgam : Complex.Gamma (2 - s) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcon
    have hre : (2 - s).re = -(m : ℝ) := by rw [hcon]; simp
    simp only [Complex.sub_re] at hre
    norm_num at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hzeta : riemannZeta (2 - s) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hcos : Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hcon
    have hre : (↑Real.pi * s / 2 : ℂ).re
        = (((2 * (k : ℂ) + 1) * (↑Real.pi : ℂ) / 2 : ℂ)).re := by rw [hcon]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im] at hre
    norm_num at hre
    have hk : ((2 * k + 1 : ℤ) : ℝ) = s.re := by
      push_cast
      nlinarith [Real.pi_pos, hre]
    have hlt : ((2 * k + 1 : ℤ) : ℝ) < 1 := by rw [hk]; linarith
    have hgt : (1 : ℝ) / 2 < ((2 * k + 1 : ℤ) : ℝ) := by rw [hk]; linarith
    have hk0 : (2 * k + 1) < 1 := by exact_mod_cast hlt
    have hk1 : (0 : ℤ) < 2 * k + 1 := by
      have : (0 : ℝ) < ((2 * k + 1 : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    omega
  simp only [ne_eq, neg_eq_zero, mul_eq_zero]
  push Not
  exact ⟨⟨⟨⟨two_ne_zero, hpow⟩, hgam⟩, hcos⟩, hzeta⟩

/-- **The tangent coefficient is `i ζ(s-1)`.**  This is `(11b)`. -/
theorem jonquiereTangent_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    jonquiereTangent s = I * riemannZeta (s - 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbase : ((2 * ↑Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr hpi.ne'⟩
  have hwne : (1 - s) ≠ 0 := by
    intro hcon
    have hre : (1 - s).re = 0 := by rw [hcon]; simp
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  -- the exponential difference
  have hsin : Complex.exp (-↑Real.pi * I * (1 - s) / 2)
      - Complex.exp (↑Real.pi * I * (1 - s) / 2)
      = -(2 * I) * Complex.sin (↑Real.pi * (1 - s) / 2) := by
    rw [show (-↑Real.pi * I * (1 - s) / 2 : ℂ) = -(↑Real.pi * I * (1 - s) / 2) by ring,
      Complex.sin]
    have h1' : (-(↑Real.pi * (1 - s) / 2) * I) = -(↑Real.pi * I * (1 - s) / 2) := by ring
    have h2' : ((↑Real.pi * (1 - s) / 2) * I) = ↑Real.pi * I * (1 - s) / 2 := by ring
    rw [h1', h2']
    linear_combination (Complex.exp (-(↑Real.pi * I * (1 - s) / 2))
      - Complex.exp (↑Real.pi * I * (1 - s) / 2)) * Complex.I_sq
  -- the sine-cosine shift
  have hshift : Complex.sin (↑Real.pi * (1 - s) / 2) = Complex.cos (↑Real.pi * s / 2) := by
    rw [show (↑Real.pi * (1 - s) / 2 : ℂ) = ↑Real.pi / 2 - ↑Real.pi * s / 2 by ring]
    exact Complex.sin_pi_div_two_sub _
  -- the Gamma shift
  have hgam : (1 - s) * Complex.Gamma (1 - s) = Complex.Gamma (2 - s) := by
    have h := Complex.Gamma_add_one (1 - s) hwne
    rw [show ((1 - s) + 1 : ℂ) = 2 - s by ring] at h
    rw [h]
  -- the power shift
  have hpow : ((2 * ↑Real.pi : ℂ)) ^ (-(1 - s)) = ((2 * ↑Real.pi : ℂ)) ^ (s - 2) * (2 * ↑Real.pi) := by
    rw [show (-(1 - s) : ℂ) = (s - 2) + 1 by ring, Complex.cpow_add _ _ hbase, Complex.cpow_one]
  rw [jonquiereTangent, hsin, hshift, show ((1 - s) + 1 : ℂ) = 2 - s by ring,
    riemannZeta_sub_one_eq h0 h1, hpow]
  rw [show ((2 * ↑Real.pi : ℂ)) ^ (s - 2) * (2 * ↑Real.pi) * Complex.Gamma (1 - s)
      * ((1 - s) * riemannZeta (2 - s) * (-(2 * I) * Complex.cos (↑Real.pi * s / 2)))
      / (2 * ↑Real.pi)
      = ((1 - s) * Complex.Gamma (1 - s)) * (((2 * ↑Real.pi : ℂ)) ^ (s - 2)
        * riemannZeta (2 - s) * (-(2 * I) * Complex.cos (↑Real.pi * s / 2)))
        * ((2 * ↑Real.pi) / (2 * ↑Real.pi)) by ring]
  rw [div_self hbase, hgam]
  ring

/-! ## The regularized germ -/

/-- The regularized local germ `R_s(θ) = f_s(θ) - Γ(1-s)(-iθ)^{s-1}`; for `θ > 0` the subtracted
term is `A₊(s) θ^{s-1}`. -/
noncomputable def regGerm (s : ℂ) (θ : ℝ) : ℂ :=
  phaseGerm s θ - jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1)

theorem regGerm_eq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ Real.pi) :
    regGerm s θ = riemannZeta s + jonquiereRemainder s θ := by
  rw [regGerm, phaseGerm, expZeta_eq_jonquiere h0 h1 hθ0 hθ1]
  ring

/-- **`(11b)`.**  The regularized germ is `ζ(s) + i ζ(s-1) θ + O(θ²)`. -/
theorem norm_regGerm_sub_tangent_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖regGerm s θ - (riemannZeta s + I * riemannZeta (s - 1) * (θ : ℂ))‖
      ≤ jonquiereTangentConst s * θ ^ 2 := by
  have hcancel : regGerm s θ - (riemannZeta s + I * riemannZeta (s - 1) * (θ : ℂ))
      = jonquiereRemainder s θ - jonquiereTangent s * (θ : ℂ) := by
    rw [regGerm_eq h0 h1 hθ0 hθ1, jonquiereTangent_eq h0 h1]
    ring
  rw [hcancel]
  exact norm_jonquiereRemainder_sub_tangent_le h0 h1 hθ0 hθ1

/-- **`R_s(0) = ζ(s)`.** -/
theorem tendsto_regGerm {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Tendsto (fun θ : ℝ => regGerm s θ) (𝓝[>] (0 : ℝ)) (𝓝 (riemannZeta s)) := by
  have hmaj : Tendsto (fun θ : ℝ => jonquiereTangentConst s * θ ^ 2 + ‖I * riemannZeta (s - 1)‖ * θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1' : Tendsto (fun θ : ℝ => jonquiereTangentConst s * θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun θ : ℝ => jonquiereTangentConst s * θ ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun θ : ℝ => jonquiereTangentConst s * θ ^ 2) := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    have h2' : Tendsto (fun θ : ℝ => ‖I * riemannZeta (s - 1)‖ * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun θ : ℝ => ‖I * riemannZeta (s - 1)‖ * θ) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun θ : ℝ => ‖I * riemannZeta (s - 1)‖ * θ) := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    simpa using h1'.add h2'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun θ => norm_nonneg _) ?_ hmaj
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT Real.pi_pos] with θ hθ hθ1
  have hθ0 : (0 : ℝ) < θ := hθ
  have hb := norm_regGerm_sub_tangent_le h0 h1 hθ0 hθ1.2.le
  have hsplit : regGerm s θ - riemannZeta s
      = (regGerm s θ - (riemannZeta s + I * riemannZeta (s - 1) * (θ : ℂ)))
        + I * riemannZeta (s - 1) * (θ : ℂ) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hlin : ‖I * riemannZeta (s - 1) * ((θ : ℝ) : ℂ)‖ = ‖I * riemannZeta (s - 1)‖ * θ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hθ0.le]
  rw [hlin]
  linarith [hb]

/-- **`(11c)`.**  At a zeta zero in the strip the regularized germ has slope `i ζ(s-1) ≠ 0`. -/
theorem tendsto_regGerm_slope {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    Tendsto (fun θ : ℝ => regGerm s θ / (θ : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (I * riemannZeta (s - 1))) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hmaj : Tendsto (fun θ : ℝ => jonquiereTangentConst s * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun θ : ℝ => jonquiereTangentConst s * θ) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun θ : ℝ => jonquiereTangentConst s * θ) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun θ => norm_nonneg _) ?_ hmaj
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT Real.pi_pos] with θ hθ hθ1
  have hθ0 : (0 : ℝ) < θ := hθ
  have hθne : ((θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ0.ne'
  have hb := norm_regGerm_sub_tangent_le h0' h1 hθ0 hθ1.2.le
  rw [hz, zero_add] at hb
  have hsplit : regGerm s θ / ((θ : ℝ) : ℂ) - I * riemannZeta (s - 1)
      = (regGerm s θ - I * riemannZeta (s - 1) * ((θ : ℝ) : ℂ)) / ((θ : ℝ) : ℂ) := by
    field_simp
  rw [hsplit, norm_div, Complex.norm_real, Real.norm_of_nonneg hθ0.le,
    div_le_iff₀ hθ0]
  calc ‖regGerm s θ - I * riemannZeta (s - 1) * ((θ : ℝ) : ℂ)‖
      ≤ jonquiereTangentConst s * θ ^ 2 := hb
    _ = jonquiereTangentConst s * θ * θ := by ring

/-- **The tangent is nonzero.** -/
theorem tangent_ne_zero {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    I * riemannZeta (s - 1) ≠ 0 :=
  mul_ne_zero Complex.I_ne_zero (riemannZeta_sub_one_ne_zero h0 h1)

end RHTower
