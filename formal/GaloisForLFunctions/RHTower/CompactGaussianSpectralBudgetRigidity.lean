import GaloisForLFunctions.RHTower.CompactGaussianSpectralTransportCost

open Complex Finset Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower

/-- A bounded frequency-cost/conductor budget forces every actual normalized
compact-window synthesis target to vanish. This excludes a bounded sharp-MV
certificate for a fixed nonzero target, while retaining signed-error possibilities. -/
theorem eventually_compactGaussian_spectralBudget_target_small
    (b₀ : ℝ) {D : ℕ} (hD : 0 < D) (A : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : SteinhausModel.Omega,
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b₀ → ∀ μ a b : ℕ → ℂ,
      (∀ p ∈ largePrimes N (N / D), ‖a p‖ ^ 2 + ‖b p‖ ^ 2 = 1) →
      (∀ p ∈ largePrimes N (N / D), a p * conj (b p) = μ p) →
      (∑ T ∈ (largePrimes N (N / D)).powerset, ((∏ p ∈ T, p : ℕ) : ℝ) *
        ‖steinhausSpectralSubsetCoefficient (largePrimes N (N / D)) a b T‖ ^ 2) ≤ A * N →
      ‖∑ p ∈ largePrimes N (N / D),
        μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ < ε := by
  obtain ⟨C, hC, hcost⟩ := exists_compactGaussianWindow_spectralTransport_cost_lower b₀ hD
  have hlim : Tendsto (fun N : ℕ => C * A / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hcost, hlim.eventually (Iio_mem_nhds (sq_pos_of_pos hε)),
    eventually_ge_atTop (2 : ℕ)] with N hbound hsmall hN2
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  intro tau L ω s hs0 hsb μ a b hnorm hmean hbudget
  have h := hbound tau L ω s hs0 hsb μ a b hnorm hmean
  have hupper := h.trans (mul_le_mul_of_nonneg_left hbudget hC.le)
  let v := ‖∑ p ∈ largePrimes N (N / D),
    μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖
  have hcancel : Real.log N * v ^ 2 ≤ C * A := by
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith [hupper]
  have hv : v ^ 2 ≤ C * A / Real.log N :=
    (le_div_iff₀ hlog).mpr (by nlinarith [hcancel])
  have hv0 : 0 ≤ v := norm_nonneg _
  change v < ε
  nlinarith [hv.trans_lt hsmall]

end RHTower
