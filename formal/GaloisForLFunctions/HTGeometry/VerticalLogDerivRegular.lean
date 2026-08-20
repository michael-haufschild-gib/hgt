import Mathlib

/-!
# The real part of a logarithmic derivative is regular across a vertical zero

If `f` vanishes to order `m` at `s₀` and one approaches `s₀` along the *vertical* line through it,
the singular part `m/(s−s₀)` becomes `m/(iτ) = −i m/τ`, which is purely imaginary.  Hence the real
part of `f'/f` along that line agrees with the real part of the logarithmic derivative of the
nonvanishing cofactor, and in particular extends continuously across the zero.

This is why an argument-variation integral along a vertical segment converges even when the
function vanishes on the segment.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem re_div_ofReal_mul_I (m : ℕ) (τ : ℝ) :
    (((m : ℂ)) / ((τ : ℂ) * I)).re = 0 := by
  rw [Complex.div_re]
  simp

theorem logDeriv_shift_pow {s₀ z : ℂ} (m : ℕ) (hz : z - s₀ ≠ 0) :
    logDeriv (fun w : ℂ => (w - s₀) ^ m) z = (m : ℂ) / (z - s₀) := by
  have hd : HasDerivAt (fun w : ℂ => (w - s₀) ^ m) ((m : ℂ) * (z - s₀) ^ (m - 1)) z := by
    have h : HasDerivAt (fun w : ℂ => w - s₀) 1 z := (hasDerivAt_id z).sub_const s₀
    refine (h.pow m).congr_deriv ?_
    ring
  rw [logDeriv_apply, hd.deriv]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hjne : ((z - s₀) ^ j) ≠ 0 := pow_ne_zero j hz
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, mul_div_assoc, div_mul_eq_div_div, div_self hjne, mul_one_div]

/-- **Vertical regularity of the real part of a logarithmic derivative.** -/
theorem re_logDeriv_vertical_eq {f h : ℂ → ℂ} {U : Set ℂ} {s₀ : ℂ} {m : ℕ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, f z = (z - s₀) ^ m * h z)
    {τ : ℝ} (hτ : τ ≠ 0) (hmem : s₀ + (τ : ℂ) * I ∈ U) :
    (logDeriv f (s₀ + (τ : ℂ) * I)).re = (logDeriv h (s₀ + (τ : ℂ) * I)).re := by
  set z : ℂ := s₀ + (τ : ℂ) * I with hz
  have hsub : z - s₀ = (τ : ℂ) * I := by rw [hz]; ring
  have hτC : ((τ : ℂ)) ≠ 0 := by exact_mod_cast hτ
  have hsubne : z - s₀ ≠ 0 := by
    rw [hsub]
    exact mul_ne_zero hτC Complex.I_ne_zero
  have hev : f =ᶠ[nhds z] fun w => (w - s₀) ^ m * h w := by
    filter_upwards [hU.mem_nhds hmem] with w hw using hfact w hw
  have hcong : logDeriv f z = logDeriv (fun w => (w - s₀) ^ m * h w) z := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hpow : ((z - s₀) ^ m) ≠ 0 := pow_ne_zero m hsubne
  have hdpow : DifferentiableAt ℂ (fun w : ℂ => (w - s₀) ^ m) z :=
    ((differentiableAt_id).sub_const s₀).pow m
  have hdh : DifferentiableAt ℂ h z := (hh z hmem).differentiableAt
  rw [hcong, logDeriv_mul z hpow (hh0 z hmem) hdpow hdh, logDeriv_shift_pow m hsubne,
    Complex.add_re, hsub, re_div_ofReal_mul_I m τ, zero_add]

end GaloisForLFunctions.HTGeometry

end
