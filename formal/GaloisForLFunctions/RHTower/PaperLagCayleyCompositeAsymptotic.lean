import GaloisForLFunctions.RHTower.PaperLagCayleyCurvatureSeparation

/-! # Signed Cayley asymptotics on the actual arithmetic channels

The quadratic curvature correction determines the complex direction of the
phase error on every constant arithmetic channel. On the composite progression
its leading coefficient is positive real, giving a sharp norm lower scale.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Complex
open scoped Topology

private theorem source_channel_tendsto {r : ℕ → ℕ} {a : ℝ}
    (hr : Tendsto r atTop atTop) (ha : ∀ k, arithmetic (r k) = a) :
    Tendsto (fun k => source (r k)) atTop (𝓝 a) := by
  have h : Tendsto (fun n => source n - arithmetic n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using summable_source_discrepancy.tendsto_atTop_zero
  have h' := (h.comp hr).add_const a
  simpa only [Function.comp_def, ha, sub_add_cancel, zero_add] using h'

private theorem phase_channel_tendsto {r : ℕ → ℕ} {a : ℝ}
    (hr : Tendsto r atTop atTop) (ha : ∀ k, arithmetic (r k) = a) :
    Tendsto (fun k => ((r k + 3 : ℝ) ^ 2 : ℂ) *
      ((phase (r k) : ℂ) - arithmeticPhase (r k))) atTop
        (𝓝 (-I / (3 * ((a : ℂ) + I) ^ 2))) := by
  have hden : ((a : ℂ) + I) * ((a : ℂ) + I) ≠ 0 :=
    mul_ne_zero (real_add_I_ne_zero a) (real_add_I_ne_zero a)
  have h := ((source_discrepancy_quadratic_tendsto.comp hr).ofReal.const_mul (2 * I)).div
    (((source_channel_tendsto hr ha).ofReal.add_const I).mul_const ((a : ℂ) + I)) hden
  have hc : 2 * I * ((-(1 / 6) : ℝ) : ℂ) / (((a : ℂ) + I) * ((a : ℂ) + I)) =
      -I / (3 * ((a : ℂ) + I) ^ 2) := by
    push_cast
    field_simp [real_add_I_ne_zero a]
    ring
  rw [hc] at h
  convert! h using 1
  funext k
  change _ * (realCayley (source (r k)) - realCayley (arithmetic (r k))) =
    2 * I * (((r k + 3 : ℝ) ^ 2 * (source (r k) - arithmetic (r k)) : ℝ) : ℂ) /
      (((source (r k) : ℂ) + I) * ((a : ℂ) + I))
  rw [paperRealCayley_sub, ha]
  push_cast
  ring

theorem phase_compositeIndex_quadratic_tendsto :
    Tendsto (fun k => ((compositeIndex k + 3 : ℝ) ^ 2 : ℂ) *
      ((phase (compositeIndex k) : ℂ) - arithmeticPhase (compositeIndex k))) atTop
        (𝓝 (1 / 6 : ℂ)) := by
  convert phase_channel_tendsto tendsto_compositeIndex arithmetic_compositeIndex using 1
  norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two]

theorem phase_primeIndex_quadratic_tendsto (p : Nat.Primes) :
    Tendsto (fun k => ((primeIndex p k + 3 : ℝ) ^ 2 : ℂ) *
      ((phase (primeIndex p k) : ℂ) - arithmeticPhase (primeIndex p k))) atTop
        (𝓝 (-I / (3 * (((Real.log p - 1 : ℝ) : ℂ) + I) ^ 2))) :=
  phase_channel_tendsto (tendsto_primeIndex p) (arithmetic_primeIndex p)

theorem phase_compositeIndex_rescaled_tendsto :
    Tendsto (fun k : ℕ => ((k + 1 : ℝ) ^ 2 : ℂ) *
      ((phase (compositeIndex k) : ℂ) - arithmeticPhase (compositeIndex k))) atTop
        (𝓝 (1 / 216 : ℂ)) := by
  have he (k : ℕ) : (compositeIndex k + 3 : ℝ) = 6 * (k + 1) := by
    have hn : compositeIndex k + 3 = 6 * (k + 1) :=
      Nat.sub_add_cancel (by omega : 3 ≤ 6 * (k + 1))
    exact_mod_cast hn
  convert! phase_compositeIndex_quadratic_tendsto.div_const (36 : ℂ) using 1
  · funext k
    rw [he]
    push_cast
    ring
  · norm_num

theorem norm_phase_compositeIndex_rescaled_tendsto :
    Tendsto (fun k : ℕ => (k + 1 : ℝ) ^ 2 *
      ‖(phase (compositeIndex k) : ℂ) - arithmeticPhase (compositeIndex k)‖) atTop
        (𝓝 (1 / 216 : ℝ)) := by
  have hn (k : ℕ) : ‖((k + 1 : ℝ) ^ 2 : ℂ)‖ = (k + 1 : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [norm_mul, hn, norm_div, norm_one, norm_ofNat] using
    phase_compositeIndex_rescaled_tendsto.norm

end
end RHTower.PaperLagCayley
