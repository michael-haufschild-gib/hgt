import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Cayley Möbius phase of the rational hard-edge test

Writing `w = e^{iz}`, the Cayley Möbius map

`M(z) = (1 - w)/(1 + w)`

is `-i·tan(z/2)` on the real axis, so the oscillatory factor `e^{-iL·tan(θ/2)}` of the rational
hard-edge Fourier transform is exactly `exp(L·M(θ))`.  Off the real axis `M` is holomorphic, and in
the lower half plane its real part is nonpositive:

`Re M(z) = (1 - |w|²)/|1 + w|² ≤ -(e^σ - 1)/(e^σ + 1),   σ = -Im z > 0.`

That is the source of the exponential decay of the hard-edge Fourier transform in the product
`(mass)·(prime logarithm)`: the aperture is bounded, and everything beyond it is exponentially
suppressed.
-/

open Complex

noncomputable section

namespace RHTower

/-- The unit-circle parameter of the Cayley chart. -/
def routeUCayleyCircle (z : ℂ) : ℂ := Complex.exp (z * Complex.I)

/-- The Cayley Möbius phase. -/
def routeUCayleyMobius (z : ℂ) : ℂ := (1 - routeUCayleyCircle z) / (1 + routeUCayleyCircle z)

/-- The exponential decay rate of the Cayley phase at imaginary depth `σ`. -/
def routeUCayleyDecayRate (σ : ℝ) : ℝ := (Real.exp σ - 1) / (Real.exp σ + 1)

theorem routeUCayleyDecayRate_pos {σ : ℝ} (hσ : 0 < σ) : 0 < routeUCayleyDecayRate σ := by
  have h1 : 1 < Real.exp σ := Real.one_lt_exp_iff.mpr hσ
  rw [routeUCayleyDecayRate]
  apply div_pos <;> linarith

theorem norm_routeUCayleyCircle (z : ℂ) : ‖routeUCayleyCircle z‖ = Real.exp (-z.im) := by
  rw [routeUCayleyCircle, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Below the real axis the circle parameter is strictly outside the unit circle. -/
theorem one_lt_norm_routeUCayleyCircle {z : ℂ} (hz : z.im < 0) :
    1 < ‖routeUCayleyCircle z‖ := by
  rw [norm_routeUCayleyCircle]
  exact Real.one_lt_exp_iff.mpr (by linarith)

/-- Off the real axis the Cayley denominator does not vanish. -/
theorem one_add_routeUCayleyCircle_ne_zero {z : ℂ} (hz : z.im < 0) :
    1 + routeUCayleyCircle z ≠ 0 := by
  intro h
  have hw : routeUCayleyCircle z = -1 := by linear_combination h
  have h1 := one_lt_norm_routeUCayleyCircle hz
  rw [hw] at h1
  simp at h1

/-- The real part of the Cayley phase as a ratio of squared norms. -/
theorem re_routeUCayleyMobius (z : ℂ) :
    (routeUCayleyMobius z).re
      = (1 - Complex.normSq (routeUCayleyCircle z))
          / Complex.normSq (1 + routeUCayleyCircle z) := by
  rw [routeUCayleyMobius, Complex.div_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.add_re,
    Complex.add_im, zero_sub, Complex.normSq_apply]
  ring

/-- **The lower half-plane decay of the Cayley phase.**  At imaginary depth `σ` the real part is at
most `-(e^σ - 1)/(e^σ + 1)`. -/
theorem re_routeUCayleyMobius_le {z : ℂ} {σ : ℝ} (hσ : 0 < σ) (hz : z.im = -σ) :
    (routeUCayleyMobius z).re ≤ -routeUCayleyDecayRate σ := by
  have hzim : z.im < 0 := by rw [hz]; linarith
  have hw : ‖routeUCayleyCircle z‖ = Real.exp σ := by
    rw [norm_routeUCayleyCircle, hz, neg_neg]
  have hexp1 : 1 < Real.exp σ := Real.one_lt_exp_iff.mpr hσ
  have hne := one_add_routeUCayleyCircle_ne_zero hzim
  have hnorm : Complex.normSq (routeUCayleyCircle z) = Real.exp σ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hw]
  have hden_pos : 0 < Complex.normSq (1 + routeUCayleyCircle z) :=
    Complex.normSq_pos.2 hne
  have hden_le : Complex.normSq (1 + routeUCayleyCircle z) ≤ (1 + Real.exp σ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have h := norm_add_le (1 : ℂ) (routeUCayleyCircle z)
    rw [norm_one, hw] at h
    have hpos : (0 : ℝ) ≤ ‖1 + routeUCayleyCircle z‖ := norm_nonneg _
    nlinarith
  have hnum : (1 : ℝ) - Complex.normSq (routeUCayleyCircle z) ≤ 0 := by
    rw [hnorm]
    nlinarith
  rw [re_routeUCayleyMobius, hnorm]
  have hstep : (1 - Real.exp σ ^ 2) / Complex.normSq (1 + routeUCayleyCircle z)
      ≤ (1 - Real.exp σ ^ 2) / (1 + Real.exp σ) ^ 2 := by
    rw [div_le_div_iff₀ hden_pos (by positivity)]
    nlinarith [hnum, hden_le, hnorm]
  refine le_trans hstep (le_of_eq ?_)
  rw [routeUCayleyDecayRate]
  field_simp
  ring

/-- On the lower half plane the Cayley phase has nonpositive real part. -/
theorem re_routeUCayleyMobius_nonpos {z : ℂ} (hz : z.im < 0) :
    (routeUCayleyMobius z).re ≤ 0 := by
  have h := re_routeUCayleyMobius_le (σ := -z.im) (by linarith) (by ring)
  have h2 := (routeUCayleyDecayRate_pos (σ := -z.im) (by linarith)).le
  linarith

/-- **The real-axis identity.**  On the real axis the Cayley phase is `-i·tan(θ/2)`. -/
theorem routeUCayleyMobius_ofReal {θ : ℝ} (hθ : Real.cos (θ / 2) ≠ 0) :
    routeUCayleyMobius (θ : ℂ) = -Complex.I * ((Real.tan (θ / 2) : ℝ) : ℂ) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = ((Real.cos (θ / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = ((Real.sin (θ / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact Complex.ofReal_ne_zero.2 hθ
  have hpy : c ^ 2 + s ^ 2 = 1 := by
    rw [hcdef, hsdef, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
    rw [show Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 by
      have := Real.sin_sq_add_cos_sq (θ / 2); linarith]
    norm_num
  have hhalf : Complex.exp ((θ : ℂ) * Complex.I)
      = Complex.exp ((((θ / 2 : ℝ)) : ℂ) * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp : Complex.exp ((((θ / 2 : ℝ)) : ℂ) * Complex.I) = c + s * Complex.I := by
    rw [Complex.exp_mul_I, hcdef, hsdef, Complex.ofReal_cos, Complex.ofReal_sin]
  have hw : routeUCayleyCircle (θ : ℂ) = c ^ 2 - s ^ 2 + 2 * c * s * Complex.I := by
    rw [routeUCayleyCircle, hhalf, hexp]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcs : c + s * Complex.I ≠ 0 := by
    intro h0
    have hprod : (c + s * Complex.I) * (c - s * Complex.I) = 1 := by
      have : (c + s * Complex.I) * (c - s * Complex.I) = c ^ 2 + s ^ 2 := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [this, hpy]
    rw [h0, zero_mul] at hprod
    exact zero_ne_one hprod
  have hfac : (1 : ℂ) + routeUCayleyCircle (θ : ℂ) = 2 * c * (c + s * Complex.I) := by
    rw [hw]
    linear_combination -hpy
  have hden : (1 : ℂ) + routeUCayleyCircle (θ : ℂ) ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hc) hcs
  have htan : ((Real.tan (θ / 2) : ℝ) : ℂ) = s / c := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div, hcdef, hsdef]
  rw [routeUCayleyMobius, htan, div_eq_iff hden, hw]
  field_simp
  linear_combination (-(c + Complex.I * s)) * hpy + (2 * c * s ^ 2) * Complex.I_sq

end RHTower

end
