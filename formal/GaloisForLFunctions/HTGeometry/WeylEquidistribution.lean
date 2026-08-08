/-
Kronecker–Weyl equidistribution for a linear phase flow — the time-average engine.

Mathlib carries ergodicity of a single circle rotation (`ergodic_add_right`, giving
orbit density) but not the equidistribution / time-average statement itself, and no
form of Weyl's criterion. This module supplies the analytic core: on a phase
character the Cesàro time average over `[0,T]` vanishes, hence the time average of a
finite trigonometric polynomial converges to its mean (the sum of the coefficients
carried by the zero frequencies).

* `char_integral_eq` — the closed form `∫₀ᵀ exp(iθt) dt = (exp(iθT) − 1)/(iθ)`.
* `char_time_average_tendsto` — for `θ ≠ 0`, `(1/T)∫₀ᵀ exp(iθt) dt → 0`; the numerator
  is bounded by `2` and the `1/T` factor drives it down. This is Weyl's criterion.
* `trig_time_average` — for a finite family of real frequencies `θ` and coefficients `c`,
  `(1/T)∫₀ᵀ ∑ᵢ cᵢ exp(iθᵢt) dt → ∑_{θᵢ=0} cᵢ`. The zero-frequency terms average to their
  coefficient; every nonzero frequency averages to `0`.

The mean is exactly the constant (Haar) term, so this is equidistribution of the flow
`t ↦ (θᵢ t)ᵢ` on the finite torus, phrased on the characters that determine it.
-/
import Mathlib

open MeasureTheory intervalIntegral Filter Topology Complex
open scoped Classical

namespace RHTower.Weyl

/-- The antiderivative `t ↦ exp(iθt)/(iθ)` of the phase character has derivative the
character itself. -/
theorem hasDerivAt_char_antideriv (θ : ℝ) (hθ : θ ≠ 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (θ * Complex.I * ↑u) / (θ * Complex.I))
      (Complex.exp (θ * Complex.I * ↑t)) t := by
  set a : ℂ := θ * Complex.I with ha
  have hane : a ≠ 0 := by
    rw [ha]; simp [Complex.ext_iff]; exact hθ
  have hlin : HasDerivAt (fun u : ℝ => a * ↑u) a t := by
    have h1 : HasDerivAt (fun u : ℝ => (↑u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have := h1.const_mul a
    simpa using this
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (a * ↑u))
      (Complex.exp (a * ↑t) * a) t := hlin.cexp
  have hdiv := hexp.div_const a
  rw [mul_div_assoc, div_self hane, mul_one] at hdiv
  exact hdiv

/-- Closed form for the phase-character interval integral. -/
theorem char_integral_eq (θ : ℝ) (hθ : θ ≠ 0) (T : ℝ) :
    ∫ t in (0:ℝ)..T, Complex.exp (θ * Complex.I * ↑t)
      = (Complex.exp (θ * Complex.I * ↑T) - 1) / (θ * Complex.I) := by
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun u : ℝ => Complex.exp (θ * Complex.I * ↑u) / (θ * Complex.I))
        (Complex.exp (θ * Complex.I * ↑x)) x := fun x _ => hasDerivAt_char_antideriv θ hθ x
  have hcont : Continuous (fun u : ℝ => Complex.exp (θ * Complex.I * ↑u)) := by
    fun_prop
  have hint : IntervalIntegrable (fun u : ℝ => Complex.exp (θ * Complex.I * ↑u))
      volume 0 T := hcont.intervalIntegrable 0 T
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [sub_div]

/-- **Weyl character time-average → 0.** For a nonzero real frequency `θ`, the Cesàro
time average of the phase `exp(iθt)` over `[0,T]` tends to `0` as `T → ∞`. The closed
form has numerator bounded by `2` in modulus while the `1/T` weight vanishes. This is
Weyl's criterion — the analytic core of Kronecker–Weyl equidistribution. -/
theorem char_time_average_tendsto (θ : ℝ) (hθ : θ ≠ 0) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0:ℝ)..T, Complex.exp (θ * Complex.I * ↑t))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun T : ℝ => (2 / |θ|) * T⁻¹)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [char_integral_eq θ hθ]
    rw [norm_mul, norm_div, norm_inv]
    have hna : ‖(θ : ℂ) * Complex.I‖ = |θ| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hnum : ‖Complex.exp (θ * Complex.I * ↑T) - 1‖ ≤ 2 := by
      calc ‖Complex.exp (θ * Complex.I * ↑T) - 1‖
          ≤ ‖Complex.exp (θ * Complex.I * ↑T)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by
            rw [Complex.norm_exp, norm_one]
            have : (θ * Complex.I * ↑T).re = 0 := by simp
            rw [this, Real.exp_zero]
        _ = 2 := by norm_num
    have hTpos : ‖(T:ℂ)‖ = T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    rw [hTpos, hna]
    have hTinv0 : (0:ℝ) ≤ T⁻¹ := le_of_lt (inv_pos.mpr hT)
    have hθinv0 : (0:ℝ) ≤ |θ|⁻¹ := by positivity
    calc T⁻¹ * (‖Complex.exp (θ * Complex.I * ↑T) - 1‖ / |θ|)
        = (T⁻¹ * |θ|⁻¹) * ‖Complex.exp (θ * Complex.I * ↑T) - 1‖ := by
          rw [div_eq_mul_inv]; ring
      _ ≤ (T⁻¹ * |θ|⁻¹) * 2 :=
          mul_le_mul_of_nonneg_left hnum (mul_nonneg hTinv0 hθinv0)
      _ = 2 / |θ| * T⁻¹ := by rw [div_eq_mul_inv]; ring
  · have : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have := this.const_mul (2 / |θ|)
    simpa using this

/-- Each frequency term's Cesàro time average converges: to its coefficient if the
frequency is zero, to `0` otherwise. -/
theorem char_term_time_average_tendsto {ι : Type*} (θ : ι → ℝ) (c : ι → ℂ) (i : ι) :
    Tendsto (fun T : ℝ => c i *
        ((↑T)⁻¹ * ∫ t in (0:ℝ)..T, Complex.exp (θ i * Complex.I * ↑t)))
      atTop (𝓝 (if θ i = 0 then c i else 0)) := by
  by_cases hi : θ i = 0
  · rw [if_pos hi]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop (0:ℝ)] with T hT
    rw [hi]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
    rw [inv_mul_cancel₀ (by exact_mod_cast hT : (↑T:ℂ) ≠ 0), mul_one]
  · rw [if_neg hi]
    have := (char_time_average_tendsto (θ i) hi).const_mul (c i)
    simpa using this

/-- **Weyl equidistribution for finite trigonometric polynomials.** The Cesàro time
average over `[0,T]` of a finite phase sum `∑ᵢ cᵢ·exp(iθᵢt)` converges to the mean —
the sum of the coefficients carried by the zero frequencies. On a nonconstant
character (all frequencies nonzero) the average vanishes. This is the finite-torus
Kronecker–Weyl statement, phrased on the characters that determine the flow. -/
theorem trig_time_average {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (c : ι → ℂ) :
    Tendsto (fun T : ℝ =>
        (↑T)⁻¹ * ∫ t in (0:ℝ)..T, ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑t))
      atTop (𝓝 (∑ i ∈ s.filter (fun i => θ i = 0), c i)) := by
  have hcont : ∀ i : ι,
      Continuous (fun t : ℝ => c i * Complex.exp (θ i * Complex.I * ↑t)) := by
    intro i; fun_prop
  have hrw : ∀ T : ℝ,
      (↑T)⁻¹ * ∫ t in (0:ℝ)..T, ∑ i ∈ s, c i * Complex.exp (θ i * Complex.I * ↑t)
        = ∑ i ∈ s, c i * ((↑T)⁻¹ * ∫ t in (0:ℝ)..T, Complex.exp (θ i * Complex.I * ↑t)) := by
    intro T
    rw [intervalIntegral.integral_finsetSum
        (fun i _ => (hcont i).intervalIntegrable 0 T)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [hrw]
  rw [Finset.sum_filter]
  exact tendsto_finsetSum _ (fun i _ => char_term_time_average_tendsto θ c i)

end RHTower.Weyl
