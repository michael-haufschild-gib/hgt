import Mathlib

/-!
# Logarithmic order from polynomial growth

A nonnegative sequence dominated by a polynomial of degree `d` has logarithmic order at most `d`:
the limsup of `log(1 + f N) / log(N + 1)` is bounded by `d` (`limsup_log_one_add_div_log_le`).

This is the analytic capstone for order laws of the shape `Ψ = limsup log(1 + a_N) / log(N+1) ≤ d`:
once a coefficient sequence is bounded by a degree-`d` polynomial (for instance an additive
convolution power bounded by a binomial count), its logarithmic growth exponent cannot exceed `d`.
The one-sided constant `log(1 + C)` is washed out by the diverging denominator `log(N + 1)`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Logarithmic order bound from polynomial domination.**  If `0 ≤ f N ≤ C·(N+1)^d` for all `N`
(with `C > 0`), then `limsup_N log(1 + f N) / log(N + 1) ≤ d`.  The dominating polynomial contributes
`d·log(N+1)` to the numerator and a constant `log(1+C)` that vanishes against the denominator. -/
theorem limsup_log_one_add_div_log_le {f : ℕ → ℝ} {C : ℝ} {d : ℕ} (hC : 0 < C)
    (hf : ∀ N, 0 ≤ f N) (hbound : ∀ N, f N ≤ C * ((N : ℝ) + 1) ^ d) :
    Filter.limsup (fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1)) Filter.atTop ≤ (d : ℝ) := by
  set g : ℕ → ℝ := fun N => Real.log (1 + f N) / Real.log ((N : ℝ) + 1) with hg
  set h : ℕ → ℝ := fun N => (d : ℝ) + Real.log (1 + C) / Real.log ((N : ℝ) + 1) with hh
  have hcob : IsCoboundedUnder (· ≤ ·) atTop g :=
    isCoboundedUnder_le_of_le atTop (fun N => div_nonneg
      (Real.log_nonneg (by linarith [hf N]))
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)))
  have hlogtop : Tendsto (fun N : ℕ => Real.log ((N:ℝ)+1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hhlim : Tendsto h atTop (𝓝 (d:ℝ)) := by
    have h0 : Tendsto (fun N : ℕ => Real.log (1+C) / Real.log ((N:ℝ)+1)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hlogtop
    simpa [hh] using tendsto_const_nhds.add h0
  have hgh : ∀ᶠ N in atTop, g N ≤ h N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hlogpos : 0 < Real.log ((N:ℝ)+1) := Real.log_pos (by linarith)
    have hpow1 : (1:ℝ) ≤ ((N:ℝ)+1)^d := one_le_pow₀ (by linarith)
    have hle : 1 + f N ≤ (1 + C) * ((N:ℝ)+1) ^ d := by nlinarith [hbound N, hpow1, hC]
    have key : Real.log (1 + f N) ≤ Real.log (1+C) + (d:ℝ) * Real.log ((N:ℝ)+1) := by
      calc Real.log (1 + f N) ≤ Real.log ((1+C) * ((N:ℝ)+1)^d) :=
            Real.log_le_log (by linarith [hf N]) hle
        _ = Real.log (1+C) + (d:ℝ) * Real.log ((N:ℝ)+1) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [hg, hh, div_le_iff₀ hlogpos, add_mul, div_mul_cancel₀ _ hlogpos.ne']
    linarith [key]
  calc Filter.limsup g atTop ≤ Filter.limsup h atTop :=
        limsup_le_limsup hgh hcob hhlim.isBoundedUnder_le
    _ = (d:ℝ) := hhlim.limsup_eq

end GaloisForLFunctions.HTGeometry
