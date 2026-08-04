import GaloisForLFunctions.RHTower.Sieve.CoeffRatioQuantitative
import GaloisForLFunctions.RHTower.Sieve.CoeffRatioLimit

/-!
# The majorant at the chosen width, as a rate in `N`

`CoeffRatioLimit` proves that the majorant times the saving tends to zero at the smoothing width
`H = N/exp((log N)^{1/20})`.  The same three geometric facts it uses — `v² ≤ t`, `t ≤ 2v²` and
`smoothRatio + 2 ≤ 3e^v` — feed the quantitative bound instead, giving

    coeffMajorant … · exp(-κt) ≤ exp(-κ(log N)^{1/10}/2)

for all large `N`.  The `o(1)` becomes a rate with no new estimate.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The majorant at the chosen width, with a rate in `N`.** -/
theorem eventually_coeffMajorant_ratio_rate {C C' M₀ a κ : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (hκ : 0 < κ) :
    ∀ᶠ N : ℝ in atTop,
      coeffMajorant (C * (smoothRatio N + 2) ^ 2) (C' * (smoothRatio N + 2)) M₀ a
          ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10))
        * Real.exp (-(κ * (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10)))
      ≤ Real.exp (-(κ * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) := by
  have hev := tendsto_logRpow20_atTop.eventually
    (eventually_coeffMajorant_ratio_le_exp hC hC' hM₀ ha hκ)
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with N hN hN1 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hH0 : (0 : ℝ) ≤ smoothWidth N := by
    rw [smoothWidth]
    have := smoothRatio_pos N
    positivity
  have hHN : smoothWidth N ≤ N := smoothWidth_le hN0 hlog0
  have hNH : (0 : ℝ) ≤ Real.log (N + smoothWidth N) :=
    Real.log_nonneg (by linarith)
  have ht0 : (0 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
    Real.rpow_nonneg hNH _
  have hv0 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hlog0 _
  have hratio : smoothRatio N + 2 ≤ 3 * Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) := by
    rw [smoothRatio]
    have hexp : (1 : ℝ) ≤ Real.exp ((Real.log N) ^ ((1 : ℝ) / 20)) :=
      Real.one_le_exp hv0
    linarith
  have hratio0 : (0 : ℝ) ≤ smoothRatio N + 2 := by
    have := smoothRatio_pos N
    linarith
  exact hN ((Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10)) (smoothRatio N) ht0
    (sq_le_logRpow hlogN hN0 hH0) (logRpow_le_two_sq hlogN hN0 hH0 hHN) hratio hratio0

end RHTower.Sieve
