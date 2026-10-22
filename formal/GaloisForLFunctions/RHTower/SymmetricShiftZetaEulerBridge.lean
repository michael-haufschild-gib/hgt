import GaloisForLFunctions.RHTower.SymmetricShiftEulerGlobalDiscrepancy
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist

/-!
# Symmetric-shift Euler discrepancy and the zeta product ratio

For a positive shift `a`, the symmetric-shift Euler-log discrepancy has Dirichlet coefficients
`(Λ(n) / log n) (n^a + n^(-a) - 2)`. For `Re s > 1 + a` its Dirichlet series equals
`log ζ(s - a) + log ζ(s + a) - 2 log ζ(s)` (canonical Euler logarithms), so its exponential is the
ratio `ζ(s - a) ζ(s + a) / ζ(s)^2`. On the real axis `σ > 1 + a` the sum of the global
prime-power discrepancy terms over all `(p, k)` is identified with this Dirichlet series, giving
`exp(Σ_(p,k) term) = Re(ζ(σ - a) ζ(σ + a) / ζ(σ)^2)`.

## Main results

- `symmetricShiftEulerLogDiscrepancyCoeff_apply`: the coefficient formula
  `(Λ(n) / log n)(n^a + n^(-a) - 2)`.
- `LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq`: the Dirichlet series is
  `log ζ(s - a) + log ζ(s + a) - 2 log ζ(s)` for `Re s > 1 + a`.
- `exp_LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq_zeta_product_ratio`: its exponential is
  `ζ(s - a) ζ(s + a) / ζ(s)^2`.
- `exp_tsum_symmetricShiftEulerGlobalDiscrepancyTerm_eq_zeta_product_ratio`: for real `σ > 1 + a`,
  the exponential of the total prime-power discrepancy equals `Re(ζ(σ - a) ζ(σ + a) / ζ(σ)^2)`.

## Hypotheses

Unconditional; the analytic statements assume only the convergence range `Re s > 1 + a`
(respectively `σ > 1 + a`), with `a > 0` built into the shift type.
-/

open Complex LSeries

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Dirichlet coefficients of the symmetric-shift Euler-log discrepancy: the Euler-log
coefficients twisted by `n^a` plus those twisted by `n^(-a)`, minus twice the untwisted ones. -/
def symmetricShiftEulerLogDiscrepancyCoeff
    (a : SymmetricPositiveShift) : ℕ → ℂ :=
  lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (a.1 : ℂ) +
    lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (-(a.1 : ℂ)) -
      RHTower.eulerLogDirichletCoeff - RHTower.eulerLogDirichletCoeff

/-- The discrepancy coefficient at `n` is `(Λ(n) / log n)(n^a + n^(-a) - 2)`. -/
theorem symmetricShiftEulerLogDiscrepancyCoeff_apply
    (a : SymmetricPositiveShift) (n : ℕ) :
    symmetricShiftEulerLogDiscrepancyCoeff a n =
      RHTower.eulerLogDirichletCoeff n *
        ((n : ℂ) ^ (a.1 : ℂ) + (n : ℂ) ^ (-(a.1 : ℂ)) - 2) := by
  simp only [symmetricShiftEulerLogDiscrepancyCoeff, Pi.add_apply, Pi.sub_apply,
    lseriesPowerTwistCoeff]
  ring_nf

/-- For `Re s > 1 + a`, the discrepancy Dirichlet series converges absolutely. -/
theorem symmetricShiftEulerLogDiscrepancyCoeff_summable
    (a : SymmetricPositiveShift) {s : ℂ} (hs : 1 + a.1 < s.re) :
    LSeriesSummable (symmetricShiftEulerLogDiscrepancyCoeff a) s := by
  have hminusRe : 1 < (s - (a.1 : ℂ)).re := by
    change 1 < s.re - a.1
    linarith
  have hplusRe : 1 < (s + (a.1 : ℂ)).re := by
    change 1 < s.re + a.1
    linarith [hs, a.2]
  have hbaseRe : 1 < s.re := by linarith [hs, a.2]
  have hminus := RHTower.canonicalEulerLogZeta_summable hminusRe
  have hplus := RHTower.canonicalEulerLogZeta_summable hplusRe
  have hbase := RHTower.canonicalEulerLogZeta_summable hbaseRe
  have htwistMinus : LSeriesSummable
      (lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (a.1 : ℂ)) s :=
    (LSeriesSummable_powerTwist _ _ _).mpr hminus
  have htwistPlus : LSeriesSummable
      (lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (-(a.1 : ℂ))) s := by
    apply (LSeriesSummable_powerTwist _ _ _).mpr
    simpa only [sub_neg_eq_add] using hplus
  exact ((htwistMinus.add htwistPlus).sub hbase).sub hbase

/-- For `Re s > 1 + a`, the discrepancy Dirichlet series equals
`log ζ(s - a) + log ζ(s + a) - 2 log ζ(s)` with the canonical Euler logarithm. -/
theorem LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq
    (a : SymmetricPositiveShift) {s : ℂ} (hs : 1 + a.1 < s.re) :
    LSeries (symmetricShiftEulerLogDiscrepancyCoeff a) s =
      RHTower.canonicalEulerLogZeta (s - (a.1 : ℂ)) +
        RHTower.canonicalEulerLogZeta (s + (a.1 : ℂ)) -
          RHTower.canonicalEulerLogZeta s - RHTower.canonicalEulerLogZeta s := by
  have hminusRe : 1 < (s - (a.1 : ℂ)).re := by
    change 1 < s.re - a.1
    linarith
  have hplusRe : 1 < (s + (a.1 : ℂ)).re := by
    change 1 < s.re + a.1
    linarith [hs, a.2]
  have hbaseRe : 1 < s.re := by linarith [hs, a.2]
  have hminus := RHTower.canonicalEulerLogZeta_summable hminusRe
  have hplus := RHTower.canonicalEulerLogZeta_summable hplusRe
  have hbase := RHTower.canonicalEulerLogZeta_summable hbaseRe
  have htwistMinus : LSeriesSummable
      (lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (a.1 : ℂ)) s :=
    (LSeriesSummable_powerTwist _ _ _).mpr hminus
  have htwistPlus : LSeriesSummable
      (lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff (-(a.1 : ℂ))) s := by
    apply (LSeriesSummable_powerTwist _ _ _).mpr
    simpa only [sub_neg_eq_add] using hplus
  have hadd := htwistMinus.add htwistPlus
  have hsub := hadd.sub hbase
  rw [symmetricShiftEulerLogDiscrepancyCoeff,
    LSeries_sub hsub hbase, LSeries_sub hadd hbase,
    LSeries_add htwistMinus htwistPlus,
    LSeries_powerTwist, LSeries_powerTwist]
  simp only [RHTower.canonicalEulerLogZeta, sub_neg_eq_add]

/-- For `Re s > 1 + a`, the exponential of the discrepancy Dirichlet series is
`ζ(s - a) ζ(s + a) / ζ(s)^2`. -/
theorem exp_LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq_zeta_product_ratio
    (a : SymmetricPositiveShift) {s : ℂ} (hs : 1 + a.1 < s.re) :
    Complex.exp (LSeries (symmetricShiftEulerLogDiscrepancyCoeff a) s) =
      riemannZeta (s - (a.1 : ℂ)) * riemannZeta (s + (a.1 : ℂ)) /
        riemannZeta s ^ 2 := by
  have hminusRe : 1 < (s - (a.1 : ℂ)).re := by
    change 1 < s.re - a.1
    linarith
  have hplusRe : 1 < (s + (a.1 : ℂ)).re := by
    change 1 < s.re + a.1
    linarith [hs, a.2]
  have hbaseRe : 1 < s.re := by linarith [hs, a.2]
  rw [LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq a hs,
    Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
    RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hminusRe,
    RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hplusRe,
    RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hbaseRe]
  ring_nf

/-- At the prime power `p^(k+1)` and real `σ`, the Dirichlet term of the discrepancy coefficients
equals the global prime-power discrepancy term indexed by `(p, k)`. -/
theorem term_symmetricShiftEulerLogDiscrepancyCoeff_prime_pow_eq_global
    (a : SymmetricPositiveShift) (sigma : ℝ) (p : Nat.Primes) (k : ℕ) :
    LSeries.term (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ)
        (p.1 ^ (k + 1)) =
      (symmetricShiftEulerGlobalDiscrepancyTerm a sigma (p, k) : ℂ) := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero _ p.property.ne_zero),
    symmetricShiftEulerLogDiscrepancyCoeff_apply,
    RHTower.eulerLogDirichletCoeff_prime_pow_succ p.1 k p.property]
  simp only [Nat.cast_pow]
  unfold symmetricShiftEulerGlobalDiscrepancyTerm
  dsimp [symmetricShiftAllPrimePowerEquiv]
  unfold symmetricShiftEulerPrimePowerDiscrepancyTerm
  unfold symmetricShiftEulerPrimePowerDiscrepancy
  unfold symmetricShiftEulerPrimeDiscrepancy
  rw [RHTower.exp_primePowerMu]
  dsimp [RHTower.primePowerWeight]
  push_cast
  rw [← Complex.natCast_cpow_natCast_mul, ← Complex.natCast_cpow_natCast_mul,
    ← Complex.natCast_cpow_natCast_mul]
  rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity),
    Complex.ofReal_cpow (by positivity)]
  push_cast
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  ring_nf

/-- For real `σ > 1 + a`, the sum of the global discrepancy terms over all `(p, k)` equals the
discrepancy Dirichlet series at `σ`. -/
theorem ofReal_tsum_symmetricShiftEulerGlobalDiscrepancyTerm_eq_LSeries
    (a : SymmetricPositiveShift) {sigma : ℝ} (hsigma : 1 + a.1 < sigma) :
    ((∑' z : Nat.Primes × ℕ,
        symmetricShiftEulerGlobalDiscrepancyTerm a sigma z : ℝ) : ℂ) =
      LSeries (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ) := by
  have hglobal : Summable (fun z : Nat.Primes × ℕ =>
      symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) :=
    summable_symmetricShiftEulerGlobalDiscrepancyTerm_of_lt a hsigma
  have hglobalC : Summable (fun z : Nat.Primes × ℕ =>
      (symmetricShiftEulerGlobalDiscrepancyTerm a sigma z : ℂ)) := by
    simpa using Complex.ofRealCLM.summable hglobal
  have hcoeff : LSeriesSummable (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ) := by
    apply symmetricShiftEulerLogDiscrepancyCoeff_summable a
    simpa using hsigma
  have hsupp : Function.support
      (LSeries.term (symmetricShiftEulerLogDiscrepancyCoeff a) (sigma : ℂ)) ⊆
        {n | IsPrimePow n} := by
    intro n hn
    by_contra hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        symmetricShiftEulerLogDiscrepancyCoeff_apply,
        RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp
  rw [LSeries, tsum_eq_tsum_primes_of_support_subset_prime_powers hcoeff hsupp,
    Complex.ofReal_tsum, hglobalC.tsum_prod]
  apply tsum_congr
  intro p
  apply tsum_congr
  intro k
  exact (term_symmetricShiftEulerLogDiscrepancyCoeff_prime_pow_eq_global a sigma p k).symm

/-- For real `σ > 1 + a`, `exp(Σ_(p,k) discrepancy term) = Re(ζ(σ - a) ζ(σ + a) / ζ(σ)^2)`. -/
theorem exp_tsum_symmetricShiftEulerGlobalDiscrepancyTerm_eq_zeta_product_ratio
    (a : SymmetricPositiveShift) {sigma : ℝ} (hsigma : 1 + a.1 < sigma) :
    Real.exp (∑' z : Nat.Primes × ℕ,
        symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) =
      (riemannZeta ((sigma - a.1 : ℝ) : ℂ) *
        riemannZeta ((sigma + a.1 : ℝ) : ℂ) /
          riemannZeta (sigma : ℂ) ^ 2).re := by
  have hexp := exp_LSeries_symmetricShiftEulerLogDiscrepancyCoeff_eq_zeta_product_ratio
    a (s := (sigma : ℂ)) (by simpa using hsigma)
  rw [← ofReal_tsum_symmetricShiftEulerGlobalDiscrepancyTerm_eq_LSeries a hsigma] at hexp
  have hre := congrArg Complex.re hexp
  have hcexp : Complex.exp (((∑' z : Nat.Primes × ℕ,
      symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) : ℝ) : ℂ) =
      (Real.exp (∑' z : Nat.Primes × ℕ,
        symmetricShiftEulerGlobalDiscrepancyTerm a sigma z) : ℂ) := by
    exact (Complex.ofReal_exp _).symm
  rw [hcexp] at hre
  simpa only [Complex.ofReal_re, Complex.ofReal_sub, Complex.ofReal_add] using hre

end


end GaloisForLFunctions.RHTower
