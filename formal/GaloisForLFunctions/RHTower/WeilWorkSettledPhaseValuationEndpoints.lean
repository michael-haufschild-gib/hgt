import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationFactorization
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationPolynomials

/-!
# Actual source endpoints at every prime valuation

The original Weil-positive source has a finite real forward ratio endpoint in
every exact prime-valuation class. The endpoints are the coefficients of a
formal exponential, multiplied by the positive coprime ratio endpoint.

No multiplicativity, coefficient positivity, canonical endpoint values, or
uniformity over primes or depths is asserted or assumed.
-/

noncomputable section

open Complex Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic

open IntegerMassRigidity WeilWorkSettledPhase

/-- All logarithmic valuation endpoints belong to one real sequence. -/
theorem exists_valuation_log_endpoints {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) :
    ∃ ell : ℕ → ℝ, ell 0 = 0 ∧ ∀ k : ℕ,
      Tendsto (fun σ : ℝ =>
        LSeries (valuationPart p k (nonCoprimePart p (lamLog lam))) (σ : ℂ))
        (𝓝[>] 1) (𝓝 (ell k : ℂ)) := by
  have hk (k : ℕ) : ∃ c : ℝ, (k = 0 → c = 0) ∧
      Tendsto (fun σ : ℝ =>
        LSeries (valuationPart p k (nonCoprimePart p (lamLog lam))) (σ : ℂ))
        (𝓝[>] 1) (𝓝 (c : ℂ)) := by
    cases k with
    | zero =>
      refine ⟨0, fun _ => rfl, ?_⟩
      simp [valuationPart_nonCoprimePart_zero hp]
    | succ k =>
      obtain ⟨c, K, eta, _, _, ht, _⟩ :=
        exists_sourceValuationLogarithm_lipschitz_limit hW hp k
      refine ⟨c, by omega, ?_⟩
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      rw [valuationPart_nonCoprimePart_succ hp, valuationPart_lamLog]
      exact ofReal_sourceValuationLogarithm hW p (k + 1) hσ
  choose ell hell0 hell using hk
  exact ⟨ell, hell0 0 rfl, hell⟩

/-- Every prime-valuation forward ratio has its explicit real polynomial endpoint,
derived from the original source without additional analytic hypotheses. -/
theorem exists_forward_valuation_endpoints {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) :
    ∃ (ell : ℕ → ℝ) (r : ℝ), ell 0 = 0 ∧ 0 < r ∧
      (∀ k : ℕ, Tendsto (fun σ : ℝ =>
        LSeries (valuationPart p k (nonCoprimePart p (lamLog lam))) (σ : ℂ))
        (𝓝[>] 1) (𝓝 (ell k : ℂ))) ∧
      (∀ k : ℕ, Tendsto (fun σ : ℝ =>
        LSeries (valuationPart p k (sourceCoeff lam)) (σ : ℂ) /
          LSeries (sourceCoeff lam) (σ : ℂ))
        (𝓝[>] 1) (𝓝 (r * valuationExponentialPolynomial ell k : ℂ))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ell, hell0, hell⟩ := exists_valuation_log_endpoints hW hp
  obtain ⟨r, K, eta, hr, _, _, ht, _⟩ := exists_coprime_source_ratio_limit hW p
  refine ⟨ell, r, hell0, hr, hell, fun k => ?_⟩
  have hf (σ : ℝ) (hσ : 1 < σ) :
      LSeriesSummable (nonCoprimePart p (lamLog lam)) (σ : ℂ) :=
    summable_nonCoprimePart p (lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ h => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW h) hσ)
  have hb := tendsto_valuationPart_dirichletExp hp
    (show nonCoprimePart p (lamLog lam) 0 = 0 by simp [nonCoprimePart, lamLog_zero])
    (show nonCoprimePart p (lamLog lam) 1 = 0 by simp [nonCoprimePart])
    (nonCoprimePart_eq_zero_of_not_dvd hp (lamLog lam)) hf hell k
  have he : (valuationExponentialPolynomial ell k : ℂ) * (r : ℂ) =
      (r * valuationExponentialPolynomial ell k : ℂ) := by ring
  have hprod := hb.mul ht
  rw [he] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (valuation_source_ratio_eq hW p k hσ).symm

end RHTower.WeilSingularArithmetic
