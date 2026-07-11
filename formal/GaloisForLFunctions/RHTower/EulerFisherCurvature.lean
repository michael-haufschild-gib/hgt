import GaloisForLFunctions.RHTower.FisherCurvatureMoment
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Global negative curvature of the Euler prime-power Fisher spectrum

This file specializes the abstract moment-determinant theorem in
`FisherCurvatureMoment` to the prime-power spectrum in the Euler expansion of
`log ζ(β)`, for `β > 1`.

The spectrum has energy `log (p^(k+1))`, weight
`(p^(k+1))^(-β) / (k+1)`, and moments `M_j = ∑ w x^j`.  Absolute convergence
through moment four follows from the corresponding logarithmically weighted
zeta Dirichlet series.  The energies `log 2` and `log 3` then force
`M₂ M₄ - M₃² > 0`, hence strict negativity of the associated scalar-curvature
expression.
-/

noncomputable section

open Complex LSeries

namespace RHTower

private lemma iterate_logMul_one (m n : ℕ) :
    (logMul^[m] (1 : ℕ → ℂ)) n = (Complex.log n) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change Complex.log n * (logMul^[m] (1 : ℕ → ℂ)) n = _
      rw [ih]
      ring

/-- Every logarithmically weighted real zeta Dirichlet series is absolutely summable to the
right of `β = 1`. -/
theorem summable_abs_log_natCast_pow_mul_rpow_neg
    (m : ℕ) (β : ℝ) (hβ : 1 < β) :
    Summable (fun n : ℕ => |Real.log n| ^ m * (n : ℝ) ^ (-β)) := by
  have hs : LSeriesSummable (logMul^[m] (1 : ℕ → ℂ)) (β : ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul, LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hβ
  have hsn := summable_norm_iff.mpr hs
  apply hsn.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : -β ≠ 0)]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    rw [iterate_logMul_one, norm_pow]
    change ‖Complex.log n‖ ^ m / ‖((n : ℝ) : ℂ) ^ (β : ℂ)‖ = _
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    rw [← Complex.natCast_log]
    simp only [Complex.norm_real, Complex.ofReal_re]
    rw [Real.rpow_neg (show 0 ≤ (n : ℝ) by positivity)]
    simp [Real.norm_eq_abs, div_eq_mul_inv, mul_comm]

/-- The natural number represented by a prime and a positive exponent. -/
def eulerPrimePowerNat (z : Nat.Primes × ℕ) : ℕ := z.1.1 ^ (z.2 + 1)

/-- Unique factorization makes the prime-positive-exponent parametrization injective. -/
theorem eulerPrimePowerNat_injective : Function.Injective eulerPrimePowerNat := by
  rintro ⟨p, k⟩ ⟨q, l⟩ h
  change p.1 ^ (k + 1) = q.1 ^ (l + 1) at h
  have hpdivpow : p.1 ∣ q.1 ^ (l + 1) := by
    rw [← h]
    exact dvd_pow_self p.1 (by omega)
  have hpdivq : p.1 ∣ q.1 := p.2.dvd_of_dvd_pow hpdivpow
  have hpq : p.1 = q.1 := (Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hpdivq
  have hkl : k + 1 = l + 1 := by
    apply Nat.pow_right_injective p.2.two_le
    simpa [hpq] using h
  cases Subtype.ext hpq
  simp_all

/-- Energy of an Euler prime-power mode. -/
def eulerPrimePowerEnergy (z : Nat.Primes × ℕ) : ℝ :=
  Real.log (eulerPrimePowerNat z)

/-- Positive Euler-cumulant weight at inverse temperature `β`. -/
def eulerPrimePowerWeight (β : ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  (eulerPrimePowerNat z : ℝ) ^ (-β) / (z.2 + 1 : ℝ)

/-- Absolute convergence of every Euler prime-power moment for `β > 1`. -/
theorem summable_abs_eulerPrimePower_moment
    (m : ℕ) (β : ℝ) (hβ : 1 < β) :
    Summable (fun z : Nat.Primes × ℕ =>
      |eulerPrimePowerWeight β z * eulerPrimePowerEnergy z ^ m|) := by
  have hsNat : Summable (fun n : ℕ => |Real.log n| ^ m * (n : ℝ) ^ (-β)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg m β hβ
  have hsComp : Summable (fun z : Nat.Primes × ℕ =>
      |Real.log (eulerPrimePowerNat z)| ^ m *
        (eulerPrimePowerNat z : ℝ) ^ (-β)) :=
    hsNat.comp_injective eulerPrimePowerNat_injective
  apply Summable.of_nonneg_of_le (fun z => abs_nonneg _) ?_ hsComp
  intro z
  rw [abs_of_nonneg]
  · dsimp [eulerPrimePowerWeight, eulerPrimePowerEnergy]
    have hden : 1 ≤ (z.2 + 1 : ℝ) := by norm_num
    have hpow : 0 ≤ (eulerPrimePowerNat z : ℝ) ^ (-β) := by positivity
    have hlog : 0 ≤ Real.log (eulerPrimePowerNat z) := Real.log_natCast_nonneg _
    rw [div_mul_eq_mul_div]
    simpa [abs_of_nonneg hlog, mul_comm] using
      (div_le_self (mul_nonneg hpow (pow_nonneg hlog m)) hden)
  · dsimp [eulerPrimePowerWeight, eulerPrimePowerEnergy]
    positivity

private def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The Euler prime-power Hankel determinant controlling the Fisher curvature is strictly
positive throughout the physical half-plane `β > 1`. -/
theorem eulerPrimePowerMoment_det_pos (β : ℝ) (hβ : 1 < β) :
    0 < fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
          fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
        fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2 := by
  apply fisherWeightedTsumMoment_det_pos
      (eulerPrimePowerWeight β) eulerPrimePowerEnergy
      (i := (primeTwo, 0)) (j := (primeThree, 0))
  · intro z
    dsimp [eulerPrimePowerWeight]
    positivity
  · exact summable_abs_eulerPrimePower_moment 2 β hβ
  · exact summable_abs_eulerPrimePower_moment 3 β hβ
  · exact summable_abs_eulerPrimePower_moment 4 β hβ
  · dsimp [eulerPrimePowerWeight, primeTwo, eulerPrimePowerNat]
    positivity
  · dsimp [eulerPrimePowerWeight, primeThree, eulerPrimePowerNat]
    positivity
  · dsimp [eulerPrimePowerEnergy, primeTwo, eulerPrimePowerNat]
    exact ne_of_gt (Real.log_pos (by norm_num))
  · dsimp [eulerPrimePowerEnergy, primeThree, eulerPrimePowerNat]
    exact ne_of_gt (Real.log_pos (by norm_num))
  · dsimp [eulerPrimePowerEnergy, primeTwo, primeThree, eulerPrimePowerNat]
    exact ne_of_lt (Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num))

/-- The second Euler prime-power moment, the Fisher conformal scale factor, is positive. -/
theorem eulerPrimePowerMoment_two_pos (β : ℝ) (hβ : 1 < β) :
    0 < fisherWeightedTsumMoment
      (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 := by
  have habs := summable_abs_eulerPrimePower_moment 2 β hβ
  have hsum : Summable (fun z : Nat.Primes × ℕ =>
      eulerPrimePowerWeight β z * eulerPrimePowerEnergy z ^ 2) :=
    Summable.of_norm (by simpa [Real.norm_eq_abs] using habs)
  refine hsum.tsum_pos ?_ (primeTwo, 0) ?_
  · intro z
    dsimp [eulerPrimePowerWeight, eulerPrimePowerEnergy]
    positivity
  · dsimp [eulerPrimePowerWeight, eulerPrimePowerEnergy, primeTwo, eulerPrimePowerNat]
    positivity

/-- Scalar-curvature expression for the conformal Euler Fisher metric. -/
def eulerFisherScalarCurvature (β : ℝ) : ℝ :=
  -(fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 *
      fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 4 -
      fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 3 ^ 2) /
    fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2 ^ 3

/-- The Euler Fisher scalar-curvature expression is globally strictly negative for `β > 1`. -/
theorem eulerFisherScalarCurvature_neg (β : ℝ) (hβ : 1 < β) :
    eulerFisherScalarCurvature β < 0 := by
  have hdet := eulerPrimePowerMoment_det_pos β hβ
  have hM2 := eulerPrimePowerMoment_two_pos β hβ
  dsimp [eulerFisherScalarCurvature]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hdet) (pow_pos hM2 3)

end RHTower
