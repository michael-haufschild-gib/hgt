import GaloisForLFunctions.RHTower.ZetaFisherHorizon
import GaloisForLFunctions.RHTower.ZetaHypertranscendental
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFisherTangent
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# The Fisher metric of the arithmetic state family is the Gibbs variance of `log n`

Right of the abscissa of absolute convergence the Bohr state family is the Gibbs law
`p_n = n^{-x}/ζ(x)` on the positive integers, and its second logarithmic derivative is the
variance of the observable `log n`:

`(log ζ)''(x) = ⟨(log n)²⟩ - ⟨log n⟩² = Var_p(log n) ≥ 0`.

This identifies the Fisher metric with the Fisher information of the Gibbs family, and makes its
positivity right of the critical line a variance, not an accident.
-/

noncomputable section

open Filter Topology Complex

namespace RHTower

/-! ### The logarithmic Dirichlet sums as `L`-series -/

theorem log_natCast_pow_zero (k : ℕ) (hk : 0 < k) : (Real.log ((0 : ℕ) : ℝ)) ^ k = 0 := by
  rw [Nat.cast_zero, Real.log_zero, zero_pow hk.ne']

theorem summable_log_natCast_pow_mul_rpow_neg (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (Real.log n) ^ k * (n : ℝ) ^ (-σ)) := by
  refine (summable_abs_log_natCast_pow_mul_rpow_neg k σ hσ).congr fun n => ?_
  rw [abs_of_nonneg (Real.log_natCast_nonneg n)]

theorem tsum_log_natCast_pow_eq_eulerLogPowMass {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (Real.log n) ^ k * (n : ℝ) ^ (-σ)) = eulerLogPowMass k σ := by
  have hsum := summable_log_natCast_pow_mul_rpow_neg k hσ
  have hzero : (Real.log (0 : ℕ)) ^ k * ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
    rw [log_natCast_pow_zero k hk, zero_mul]
  have hshift := hsum.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one, hzero, zero_add] at hshift
  rw [eulerLogPowMass, tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => (Real.log n) ^ k * (n : ℝ) ^ (-σ))]
  exact hshift.symm

set_option maxHeartbeats 1000000 in
theorem ofReal_eulerLogPowMass_eq_LSeries_zetaJetA {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    ((eulerLogPowMass k σ : ℝ) : ℂ)
      = LSeries (⇑(GaloisForLFunctions.zetaJetA k)) ((σ : ℝ) : ℂ) := by
  have hf0 : (fun n : ℕ => (Real.log n) ^ k) 0 = 0 := log_natCast_pow_zero k hk
  calc ((eulerLogPowMass k σ : ℝ) : ℂ)
      = ((∑' n : ℕ, (Real.log n) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [tsum_log_natCast_pow_eq_eulerLogPowMass hk hσ]
    _ = LSeries (fun m : ℕ => ((((Real.log m) ^ k : ℝ)) : ℂ)) ((σ : ℝ) : ℂ) :=
        GaloisForLFunctions.HTGeometry.ofReal_tsum_eq_lseries
          (f := fun n : ℕ => (Real.log n) ^ k) hf0
    _ = LSeries (⇑(GaloisForLFunctions.zetaJetA k)) ((σ : ℝ) : ℂ) := by
        refine LSeries_congr (fun {n} hn => ?_) _
        by_cases hge : 2 ≤ n
        · rw [GaloisForLFunctions.zetaJetA_apply, if_pos hge, Complex.ofReal_pow]
        · have hn1 : n = 1 := by omega
          subst hn1
          rw [GaloisForLFunctions.zetaJetA_apply, if_neg hge, Nat.cast_one, Real.log_one,
            zero_pow hk.ne', Complex.ofReal_zero]

/-! ### The zeta jets on the real axis -/

theorem riemannZeta_ofReal_eq_eulerMass {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta ((σ : ℝ) : ℂ) = ((eulerMass σ : ℝ) : ℂ) := by
  have h := ofReal_eulerPositiveTotal_eq_riemannZeta hσ
  have hmass : eulerPositiveTotal σ = eulerMass σ := by
    rw [eulerPositiveTotal, eulerMass]
    exact tsum_congr fun n => rfl
  rw [← h, hmass]

theorem deriv_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    deriv riemannZeta ((σ : ℝ) : ℂ) = -((eulerLogMass σ : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have h := GaloisForLFunctions.iteratedDeriv_riemannZeta_eq 1 hre
  rw [iteratedDeriv_one] at h
  rw [h, if_neg (by omega : ¬ (1 : ℕ) = 0), zero_add,
    ← ofReal_eulerLogPowMass_eq_LSeries_zetaJetA (by omega : 0 < 1) hσ,
    eulerLogPowMass_one]
  ring

theorem deriv_deriv_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    deriv (deriv riemannZeta) ((σ : ℝ) : ℂ) = ((eulerLogPowMass 2 σ : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have h := GaloisForLFunctions.iteratedDeriv_riemannZeta_eq 2 hre
  have hiter : iteratedDeriv 2 riemannZeta = deriv (deriv riemannZeta) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter] at h
  rw [h, if_neg (by omega : ¬ (2 : ℕ) = 0), zero_add,
    ← ofReal_eulerLogPowMass_eq_LSeries_zetaJetA (by omega : 0 < 2) hσ]
  ring

/-! ### The Fisher metric as a variance -/

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
    (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  exact (hdiff.analyticOnNhd isOpen_compl_singleton) _ (by simpa using hs)

theorem zetaFisherMetric_eq_quotient {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    zetaFisherMetric s
      = (deriv (deriv riemannZeta) s * riemannZeta s
          - deriv riemannZeta s * deriv riemannZeta s) / riemannZeta s ^ 2 := by
  have hana := analyticAt_riemannZeta hs
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) s := hana.deriv.differentiableAt
  have hd0 : DifferentiableAt ℂ riemannZeta s := hana.differentiableAt
  have hfun : logDeriv riemannZeta = fun z : ℂ => deriv riemannZeta z / riemannZeta z := by
    funext z; exact logDeriv_apply _ _
  rw [zetaFisherMetric, hfun, deriv_fun_div hd1 hd0 hz]

/-- **The Fisher metric is the Gibbs variance of `log n`.** -/
theorem zetaFisherMetric_ofReal_eq_eulerLogVariance {σ : ℝ} (hσ : 1 < σ) :
    zetaFisherMetric ((σ : ℝ) : ℂ) = ((eulerLogVariance σ : ℝ) : ℂ) := by
  have hne : ((σ : ℝ) : ℂ) ≠ 1 := by
    simp only [Ne, Complex.ofReal_eq_one]
    exact ne_of_gt hσ
  have hmass : (0 : ℝ) < eulerMass σ := eulerMass_pos hσ
  have hz : riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
    rw [riemannZeta_ofReal_eq_eulerMass hσ, Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt hmass
  rw [zetaFisherMetric_eq_quotient hne hz, deriv_riemannZeta_ofReal hσ,
    deriv_deriv_riemannZeta_ofReal hσ, riemannZeta_ofReal_eq_eulerMass hσ,
    eulerLogVariance, eulerLogMean]
  have hmassC : ((eulerMass σ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hmass
  push_cast
  field_simp

/-- **Positivity of the Fisher metric right of the critical line.** -/
theorem zetaFisherReal_eq_eulerLogVariance {σ : ℝ} (hσ : 1 < σ) :
    zetaFisherReal σ = eulerLogVariance σ := by
  rw [zetaFisherReal, zetaFisherMetric_ofReal_eq_eulerLogVariance hσ, Complex.ofReal_re]

theorem zetaFisherReal_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ zetaFisherReal σ := by
  rw [zetaFisherReal_eq_eulerLogVariance hσ]
  exact eulerLogVariance_nonneg hσ

end RHTower
