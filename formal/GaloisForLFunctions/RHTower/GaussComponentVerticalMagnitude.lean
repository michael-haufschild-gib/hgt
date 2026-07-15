import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic

/-!
# Critical vertical magnitude of a Gauss component

This specializes the vertical Gamma-ratio asymptotic to the `m`-fold Gauss component.  The
component offset `k/m` disappears, and the magnitude has critical exponent `1/(2m)` with leading
constant `(2π)^(1/(2m))`.
-/

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- Positive critical exponent of an `m`-fold Gauss component. -/
def gaussComponentDelta (m : ℕ) : ℝ :=
  1 / (2 * (m : ℝ))

/-- Real offset of the `k`th Gauss component. -/
def gaussComponentOffset {m : ℕ} (k : Fin m) : ℝ :=
  (k : ℝ) / (m : ℝ)

/-- Positive vertical magnitude obtained from the Gauss component at height `t`. -/
def gaussComponentVerticalMagnitude {m : ℕ} (k : Fin m) (t : ℝ) : ℝ :=
  (Real.pi / (m : ℝ)) ^ gaussComponentDelta m *
    Real.exp
      (Real.log ‖Complex.Gamma
        ((gaussComponentOffset k : ℂ) + (t / (2 * (m : ℝ)) : ℂ) * Complex.I)‖ -
       Real.log ‖Complex.Gamma
        (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
          (t / (2 * (m : ℝ)) : ℂ) * Complex.I)‖)

/-- Conjugate-denominator multiplicative form of the general vertical Gamma-ratio law. -/
theorem gamma_vertical_ratio_conj_norm_rpow_tendsto {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Tendsto (fun τ : ℝ =>
      Real.exp
        (Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖ -
         Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) - (τ : ℂ) * Complex.I)‖) *
        τ ^ δ)
      atTop (nhds 1) := by
  have hmain := gamma_vertical_ratio_conj_log_tendsto ha hδ
  have hexp : Tendsto (fun τ : ℝ =>
      Real.exp
        ((Real.log ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖ -
          Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) - (τ : ℂ) * Complex.I)‖) +
          δ * Real.log τ))
      atTop (nhds 1) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hmain)
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [Real.exp_add, Real.rpow_def_of_pos hτ]
  ring_nf

/-- **Gauss-component critical magnitude.**  For every component label `k`,
`M_{m,k}(t) t^(1/(2m)) → (2π)^(1/(2m))`.  The limit is independent of `k`. -/
theorem gaussComponentVerticalMagnitude_mul_rpow_tendsto
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) :
    Tendsto (fun t : ℝ =>
      gaussComponentVerticalMagnitude k t * t ^ gaussComponentDelta m)
      atTop (nhds ((2 * Real.pi) ^ gaussComponentDelta m)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc : (0 : ℝ) < 2 * (m : ℝ) := mul_pos (by norm_num) hmR
  have ha : 0 ≤ gaussComponentOffset k := by
    rw [gaussComponentOffset]
    positivity
  have hδ : 0 ≤ gaussComponentDelta m := by
    rw [gaussComponentDelta]
    positivity
  have hratio := (gamma_vertical_ratio_conj_norm_rpow_tendsto ha hδ).comp
    (tendsto_id.atTop_div_const hc)
  have hscaled := hratio.const_mul
    ((Real.pi / (m : ℝ)) ^ gaussComponentDelta m *
      (2 * (m : ℝ)) ^ gaussComponentDelta m)
  have hconstant :
      (Real.pi / (m : ℝ)) ^ gaussComponentDelta m *
          (2 * (m : ℝ)) ^ gaussComponentDelta m =
        (2 * Real.pi) ^ gaussComponentDelta m := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ Real.pi / (m : ℝ)) hc.le]
    congr 1
    field_simp
  rw [hconstant] at hscaled
  have hscaled' : Tendsto
      (fun t : ℝ =>
        (2 * Real.pi) ^ gaussComponentDelta m *
          (Real.exp
            (Real.log ‖Complex.Gamma
              ((gaussComponentOffset k : ℂ) +
                (t / (2 * (m : ℝ)) : ℂ) * Complex.I)‖ -
             Real.log ‖Complex.Gamma
              (((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
                (t / (2 * (m : ℝ)) : ℂ) * Complex.I)‖) *
            (t / (2 * (m : ℝ))) ^ gaussComponentDelta m))
      atTop (nhds ((2 * Real.pi) ^ gaussComponentDelta m)) := by
    simpa using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hfactor :
      (t / (2 * (m : ℝ))) ^ gaussComponentDelta m *
          (2 * (m : ℝ)) ^ gaussComponentDelta m =
        t ^ gaussComponentDelta m := by
    rw [← Real.mul_rpow (div_nonneg ht.le hc.le) hc.le, div_mul_cancel₀ t hc.ne']
  rw [gaussComponentVerticalMagnitude]
  rw [← hfactor]
  rw [← hconstant]
  ring

end

end RHTower
