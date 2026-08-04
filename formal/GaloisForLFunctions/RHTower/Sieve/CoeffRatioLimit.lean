import GaloisForLFunctions.RHTower.Sieve.CoeffRatioBound

/-!
# The majorant at the chosen width tends to zero

Combining the pointwise bound of `CoeffRatioBound` with the limit of `ExpQuadraticDecay`: at the
smoothing width `H = N/exp((log N)^{1/20})` the majorant times the saving tends to zero.

All the hypotheses of the pointwise bound hold eventually, and each is one of the facts proved in
`SmoothWidthChoice`, `LogComparison` or `CoeffMajorantMono`.
-/

namespace RHTower.Sieve

open Filter Topology Real

/-- The majorant is nonnegative when its data are. -/
theorem coeffMajorant_nonneg {C C' M₀ a t : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hM₀ : 0 ≤ M₀)
    (ha : 0 ≤ a) (ht : 0 ≤ t) : 0 ≤ coeffMajorant C C' M₀ a t := by
  rw [coeffMajorant]
  have hexp : (0 : ℝ) ≤ Real.exp (22 / 4) := (Real.exp_pos _).le
  positivity

/-- The twentieth-root variable tends to infinity. -/
theorem tendsto_logRpow20_atTop :
    Tendsto (fun N : ℝ => (Real.log N) ^ ((1 : ℝ) / 20)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop

/-- **The majorant at the chosen width tends to zero.** -/
theorem tendsto_coeffMajorant_ratio {C C' M₀ a κ : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (hκ : 0 < κ) :
    Tendsto (fun N : ℝ =>
        coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀ a
            ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
          * Real.exp (-(κ * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))))
      atTop (𝓝 0) := by
  set b : ℝ := 8 * (9 * C) * Real.exp (22 / 4)
      + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
      + M₀ * (4 + 2 * (9 * C)) with hbdef
  set c : ℝ := (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4 with hcdef
  have hmaj : Tendsto (fun v : ℝ =>
      (1 + (512 * a) * (v ^ 2) ^ 9) * (b + c * v ^ 2) * Real.exp (2 * v)
        * Real.exp (-(κ * v ^ 2))) atTop (𝓝 0) :=
    tendsto_poly_exp_two_sub_sq hκ
  have hcomp : Tendsto (fun N : ℝ =>
      (1 + (512 * a) * (((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2) ^ 9)
        * (b + c * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2)
        * Real.exp (2 * (Real.log N) ^ ((1 : ℝ) / 20))
        * Real.exp (-(κ * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2))) atTop (𝓝 0) :=
    hmaj.comp tendsto_logRpow20_atTop
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hlog0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN
    have hH0 : (0 : ℝ) ≤ smoothWidth N := by
      rw [smoothWidth]
      have := smoothRatio_pos N
      positivity
    have hNH : (0 : ℝ) ≤ Real.log (N + smoothWidth N) :=
      Real.log_nonneg (by linarith)
    have hĈ : (0 : ℝ) ≤ C * (smoothRatio N + 2) ^ 2 := by
      have := zero_le_smoothRatio_add_two N
      positivity
    have hĈ' : (0 : ℝ) ≤ C' * (smoothRatio N + 2) := by
      have := zero_le_smoothRatio_add_two N
      positivity
    have ht : (0 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
      Real.rpow_nonneg hNH _
    have := coeffMajorant_nonneg hĈ hĈ' hM₀ ha ht
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))] with N hN hlog1
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
    have hH0 : (0 : ℝ) ≤ smoothWidth N := by
      rw [smoothWidth]
      have := smoothRatio_pos N
      positivity
    have hHN : smoothWidth N ≤ N := smoothWidth_le hN0 hlog0
    have hNH : (0 : ℝ) ≤ Real.log (N + smoothWidth N) := Real.log_nonneg (by linarith)
    have hv : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hlog0 _
    have ht0 : (0 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
      Real.rpow_nonneg hNH _
    have htlo := sq_le_logRpow (H := smoothWidth N) hlog1 hN0 hH0
    have hthi := logRpow_le_two_sq (H := smoothWidth N) hlog1 hN0 hH0 hHN
    have hL := smoothRatio_add_two_le (N := N) hlog0
    exact coeffMajorant_ratio_le hC hC' hM₀ ha hκ.le hv ht0 htlo hthi hL
      (zero_le_smoothRatio_add_two N)

end RHTower.Sieve
