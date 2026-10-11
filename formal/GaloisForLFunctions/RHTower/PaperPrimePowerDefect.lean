import GaloisForLFunctions.RHTower.RegularizedLogZetaAbscissa
import Mathlib.Data.Nat.Prime.Nth

/-!
# The native regularized coefficient rows on every prime-power layer

The DR and PBM coefficients have the same convergence abscissa, but their literal difference
retains every proper prime-power layer. No zero-location premise enters these identities.
-/

namespace RHTower
noncomputable section
open Filter
open scoped Topology

/-- The unregularized logarithmic coefficient, in the native shifted indexing. -/
def paperLogZetaRawCoeff (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n + 1) / Real.log ((n : ℝ) + 1)

/-- The common pole subtraction. -/
def paperPrimePoleCoeff (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 1))⁻¹

/-- The literal prime indicator in the native shifted indexing. -/
def paperPrimeIndicatorCoeff (n : ℕ) : ℝ := if (n + 1).Prime then 1 else 0

theorem paperLogZetaRawCoeff_bounds (n : ℕ) :
    0 ≤ paperLogZetaRawCoeff n ∧ paperLogZetaRawCoeff n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [paperLogZetaRawCoeff]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  refine ⟨div_nonneg ArithmeticFunction.vonMangoldt_nonneg hl.le, ?_⟩
  apply (div_le_one hl).2
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ArithmeticFunction.vonMangoldt_le_log (n := n + 1))

theorem paperPrimeIndicatorCoeff_bounds (n : ℕ) :
    0 ≤ paperPrimeIndicatorCoeff n ∧ paperPrimeIndicatorCoeff n ≤ 1 := by
  simp only [paperPrimeIndicatorCoeff]
  split_ifs <;> norm_num

theorem logZetaRegCoeff_eq_raw_sub_pole (n : ℕ) :
    logZetaRegCoeff n = paperLogZetaRawCoeff n - paperPrimePoleCoeff n := by
  simp only [logZetaRegCoeff, paperLogZetaRawCoeff, paperPrimePoleCoeff]
  ring

theorem primeRegCoeff_eq_indicator_sub_pole (n : ℕ) :
    primeRegCoeff n = paperPrimeIndicatorCoeff n - paperPrimePoleCoeff n := rfl

theorem logPrimePowerDefect_eq_raw_sub_indicator (n : ℕ) :
    logPrimePowerDefect n = paperLogZetaRawCoeff n - paperPrimeIndicatorCoeff n := rfl

private theorem raw_at_prime_power (p : Nat.Primes) {k : ℕ} (hk : 0 < k) :
    paperLogZetaRawCoeff ((p : ℕ) ^ k - 1) = (k : ℝ)⁻¹ := by
  have hp : 1 ≤ (p : ℕ) ^ k := one_le_pow₀ p.property.one_le
  have hl : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  unfold paperLogZetaRawCoeff
  have he : (((p : ℕ) ^ k - 1 : ℕ) : ℝ) + 1 = (p : ℝ) ^ k := by
    exact_mod_cast Nat.sub_add_cancel hp
  rw [Nat.sub_add_cancel hp, he, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime p.property, Real.log_pow]
  field_simp

theorem paperLogZetaRawCoeff_primePower (p : Nat.Primes) (k : ℕ) :
    paperLogZetaRawCoeff ((p : ℕ) ^ (k + 1) - 1) = ((k + 1 : ℕ) : ℝ)⁻¹ :=
  raw_at_prime_power p (Nat.succ_pos k)

theorem paperPrimeIndicatorCoeff_primePower (p : Nat.Primes) (k : ℕ) :
    paperPrimeIndicatorCoeff ((p : ℕ) ^ (k + 1) - 1) = if k = 0 then 1 else 0 := by
  unfold paperPrimeIndicatorCoeff
  rw [Nat.sub_add_cancel (one_le_pow₀ p.property.one_le)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [p.property]
  · rw [if_neg (Nat.Prime.not_prime_pow (by omega)), if_neg hk.ne']

theorem logPrimePowerDefect_primePower (p : Nat.Primes) (k : ℕ) :
    logPrimePowerDefect ((p : ℕ) ^ (k + 2) - 1) = ((k + 2 : ℕ) : ℝ)⁻¹ := by
  rw [logPrimePowerDefect_eq_raw_sub_indicator,
    show k + 2 = (k + 1) + 1 by omega,
    paperLogZetaRawCoeff_primePower, paperPrimeIndicatorCoeff_primePower]
  simp

/-- The largest prime-power defect is exactly the prime-square layer. -/
theorem logPrimePowerDefect_bounds (n : ℕ) :
    0 ≤ logPrimePowerDefect n ∧ logPrimePowerDefect n ≤ 1 / 2 := by
  refine ⟨(logPrimePowerDefect_nonneg_le n).1, ?_⟩
  by_cases hp : (n + 1).Prime
  · have hl : Real.log ((n : ℝ) + 1) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp [logPrimePowerDefect, hp, ArithmeticFunction.vonMangoldt_apply_prime hp,
      Nat.cast_add, Nat.cast_one, hl]
  by_cases hpow : IsPrimePow (n + 1)
  · obtain ⟨p, k, hpr, hk, he⟩ := (isPrimePow_nat_iff _).1 hpow
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst k
      simp only [pow_one] at he
      exact hp (he ▸ hpr)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    have hn : n = p ^ (2 + j) - 1 := by omega
    rw [hn, show 2 + j = j + 2 by omega,
      logPrimePowerDefect_primePower ⟨p, hpr⟩ j]
    have hj : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 2 j
    simpa only [one_div] using (inv_le_inv₀ (by linarith) (by norm_num)).2 hj
  · simp [logPrimePowerDefect, hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpow]

/-- An escaping enumeration of the `(k+1)`-st prime-power layer. -/
def paperPrimePowerIndex (k n : ℕ) : ℕ := (Nat.nth Nat.Prime n) ^ (k + 1) - 1

theorem tendsto_paperPrimePowerIndex (k : ℕ) :
    Tendsto (paperPrimePowerIndex k) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.2 ⟨b + 1, fun n hn => ?_⟩
  have hp := (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le n
  have he : Nat.nth Nat.Prime n ≤ (Nat.nth Nat.Prime n) ^ (k + 1) :=
    Nat.le_pow (Nat.succ_pos k)
  exact Nat.le_sub_of_add_le (hn.trans (hp.trans he))

theorem tendsto_paperPrimePoleCoeff : Tendsto paperPrimePoleCoeff atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hn)

theorem tendsto_logZetaRegCoeff_primePower (k : ℕ) :
    Tendsto (fun n => logZetaRegCoeff (paperPrimePowerIndex k n)) atTop
      (𝓝 (((k + 1 : ℕ) : ℝ)⁻¹)) := by
  have h := (tendsto_const_nhds (x := ((k + 1 : ℕ) : ℝ)⁻¹)).sub
    (tendsto_paperPrimePoleCoeff.comp (tendsto_paperPrimePowerIndex k))
  simpa only [sub_zero] using h.congr (fun n => by
    rw [logZetaRegCoeff_eq_raw_sub_pole]
    congr 1
    exact (paperLogZetaRawCoeff_primePower ⟨_, Nat.prime_nth_prime n⟩ k).symm)

theorem tendsto_primeRegCoeff_primePower (k : ℕ) :
    Tendsto (fun n => primeRegCoeff (paperPrimePowerIndex k n)) atTop
      (𝓝 (if k = 0 then 1 else 0)) := by
  have h := (tendsto_const_nhds (x := if k = 0 then (1 : ℝ) else 0)).sub
    (tendsto_paperPrimePoleCoeff.comp (tendsto_paperPrimePowerIndex k))
  simpa only [sub_zero] using h.congr (fun n => by
    rw [primeRegCoeff_eq_indicator_sub_pole]
    congr 1
    exact (paperPrimeIndicatorCoeff_primePower ⟨_, Nat.prime_nth_prime n⟩ k).symm)

end
end RHTower
