import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerBound

/-!
# Euler products at the square-root boundary

The quadratic modification has a prime-power-supported logarithm.
Root bounds give explicit logarithmic coefficient bounds; roots in the
closed disk of radius `p` give the Euler identity throughout `Re s > 1`.
-/

noncomputable section
open Complex
namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

@[simp] theorem eulerLogCoeff_zero {p : ℕ} (hp : p ≠ 0) (α β : ℂ) :
    eulerLogCoeff p α β 0 = 0 := by
  simp only [eulerLogCoeff, Pi.add_apply, RHTower.eulerLogDirichletCoeff_zero,
    powerLogCoeff_zero hp, add_zero]

@[simp] theorem eulerLogCoeff_one {p : ℕ} (hp : 1 < p) (α β : ℂ) :
    eulerLogCoeff p α β 1 = 0 := by
  simp only [eulerLogCoeff, Pi.add_apply, RHTower.eulerLogDirichletCoeff_one,
    powerLogCoeff_one hp, add_zero]

private theorem powerLogCoeff_eq_zero {p n : ℕ} (hn : ¬ ∃ k : ℕ, p ^ k = n) (α : ℂ) :
    powerLogCoeff p α n = 0 :=
  Function.extend_apply' _ _ _ hn

/-- The finite modification introduces no logarithmic support away from prime powers. -/
theorem eulerLogCoeff_primePower {p : ℕ} (hp : p.Prime) (α β : ℂ) {n : ℕ}
    (hn : eulerLogCoeff p α β n ≠ 0) : IsPrimePow n := by
  by_contra hnot
  have hc := RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hnot
  by_cases hpow : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hpow
    by_cases hk : k = 0
    · subst k
      exact hn (eulerLogCoeff_one hp.one_lt α β)
    · exact hnot ((isPrimePow_nat_iff _).mpr ⟨p, k, hp, Nat.pos_of_ne_zero hk, rfl⟩)
  · apply hn
    simp only [eulerLogCoeff, Pi.add_apply, hc, powerLogCoeff_eq_zero hpow, add_zero]

/-- The logarithmic coefficients as an arithmetic function. -/
def logarithmicCoeffs {p : ℕ} (hp : p.Prime) (α β : ℂ) : ArithmeticFunction ℂ :=
  ⟨eulerLogCoeff p α β, eulerLogCoeff_zero hp.ne_zero α β⟩

/-- A bound on the local roots gives a bound on every logarithmic coefficient. -/
theorem eulerLogCoeff_bound {p : ℕ} (hp : p.Prime) {α β : ℂ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hα : ‖α‖ ≤ (p : ℝ) ^ θ) (hβ : ‖β‖ ≤ (p : ℝ) ^ θ)
    {n : ℕ} (hn : n ≠ 0) :
    ‖eulerLogCoeff p α β n‖ ≤ 3 * (n : ℝ) ^ θ := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpn : 1 ≤ (p : ℝ) ^ θ := Real.one_le_rpow hpR hθ
  by_cases hpow : ∃ k : ℕ, p ^ k = n
  · obtain ⟨k, rfl⟩ := hpow
    by_cases hk : k = 0
    · subst k
      simp only [pow_zero, eulerLogCoeff_one hp.one_lt, norm_zero, Nat.cast_one, Real.one_rpow]
      norm_num
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hpoweq : ((p ^ k : ℕ) : ℝ) ^ θ = ((p : ℝ) ^ θ) ^ k := by
        rw [Nat.cast_pow, Real.rpow_def_of_pos (pow_pos (zero_lt_one.trans_le hpR) k),
          Real.log_pow, Real.rpow_def_of_pos (zero_lt_one.trans_le hpR), ← Real.exp_nat_mul]
        congr 1
        ring
      have hnum : ‖1 - α ^ k - β ^ k‖ ≤ 1 + 2 * ((p : ℝ) ^ θ) ^ k := by
        calc _ ≤ ‖1 - α ^ k‖ + ‖β ^ k‖ := norm_sub_le _ _
          _ ≤ (‖(1 : ℂ)‖ + ‖α ^ k‖) + ‖β ^ k‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
          _ = 1 + ‖α‖ ^ k + ‖β‖ ^ k := by rw [norm_one, norm_pow, norm_pow]
          _ ≤ 1 + ((p : ℝ) ^ θ) ^ k + ((p : ℝ) ^ θ) ^ k := by gcongr
          _ = _ := by ring
      have hpk : 1 ≤ ((p : ℝ) ^ θ) ^ k := one_le_pow₀ hpn
      rw [eulerLogCoeff_prime_pow hp α β hk, norm_div, Complex.norm_natCast, hpoweq]
      calc ‖1 - α ^ k - β ^ k‖ / (k : ℝ) ≤ ‖1 - α ^ k - β ^ k‖ :=
          div_le_self (norm_nonneg _) hk1
        _ ≤ 3 * ((p : ℝ) ^ θ) ^ k := by linarith only [hnum, hpk]
  · have heq : eulerLogCoeff p α β n = RHTower.eulerLogDirichletCoeff n := by
      simp only [eulerLogCoeff, Pi.add_apply, powerLogCoeff_eq_zero hpow, add_zero]
    rw [heq]
    have hnp : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hnR hθ
    exact (RHTower.norm_eulerLogDirichletCoeff_le_one n).trans (by linarith only [hnp])

private theorem local_log_converges {p : ℕ} (hp : p.Prime) {α s : ℂ}
    (hα : ‖α‖ ≤ p) (hs : 1 < s.re) : ‖α * (p : ℂ) ^ (-s)‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 < Real.log p := Real.log_pos hpR
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
    Real.rpow_def_of_pos (zero_lt_one.trans hpR)]
  calc ‖α‖ * Real.exp (Real.log p * -s.re) ≤
      (p : ℝ) * Real.exp (Real.log p * -s.re) :=
        mul_le_mul_of_nonneg_right hα (Real.exp_pos _).le
    _ = Real.exp (Real.log p * (1 - s.re)) := by
      conv_lhs => lhs; rw [← Real.exp_log (zero_lt_one.trans hpR)]
      rw [← Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hl (by linarith only [hs]))

/-- Roots in the disk of radius `p` give absolute convergence on the full Euler half-plane. -/
theorem logarithmicCoeffs_summable {p : ℕ} (hp : p.Prime) {α β s : ℂ}
    (hα : ‖α‖ ≤ p) (hβ : ‖β‖ ≤ p) (hs : 1 < s.re) :
    LSeriesSummable (logarithmicCoeffs hp α β) s :=
  (hasSum_eulerLogCoeff hp α β hs (local_log_converges hp hα hs)
    (local_log_converges hp hβ hs)).LSeriesSummable

/-- The prime-power-supported logarithm exponentiates to the finite-factor series. -/
theorem logarithmicCoeffs_exp {p : ℕ} (hp : p.Prime) {A : ℝ} {α β s : ℂ}
    (hadd : α + β = -(A : ℂ)) (hmul : α * β = p)
    (hα : ‖α‖ ≤ p) (hβ : ‖β‖ ≤ p) (hs : 1 < s.re) :
    Complex.exp (LSeries (logarithmicCoeffs hp α β) s) = localFactor p A s * riemannZeta s :=
  exp_lSeries_eulerLogCoeff hp hadd hmul hs (local_log_converges hp hα hs)
    (local_log_converges hp hβ hs)

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
