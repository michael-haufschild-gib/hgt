import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficient
import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization

/-!
# A uniform majorant for the shifted Selberg amplitude

The power-shifted Möbius–reciprocal convolution changes each active prime
factor by at most `p^(2|c|)`. Multiplicativity bounds the whole amplitude
by `n^(2|c|)` times the original absolute amplitude. Reciprocal-logarithmic
shifts therefore retain the existing summable correction majorant on a
finite cutoff.
-/

open ArithmeticFunction Finset
open RHTower.Sieve
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The Möbius coefficient with a real power shift. -/
def powerShiftedMoebius (c : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ c, by simp⟩

theorem powerShiftedMoebius_apply (c : ℝ) (n : ℕ) :
    powerShiftedMoebius c n = ((moebius n : ℤ) : ℝ) * (n : ℝ) ^ c := rfl

theorem isMultiplicative_powerShiftedMoebius (c : ℝ) :
    (powerShiftedMoebius c).IsMultiplicative := by
  constructor
  · simp [powerShiftedMoebius_apply]
  · intro m n hmn
    simp only [powerShiftedMoebius_apply,
      isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

/-- The shifted convolution furnishing the local Euler correction. -/
def powerShiftedReciprocalAmplitude (c : ℝ) : ArithmeticFunction ℝ :=
  powerShiftedMoebius c * reciprocalNatArithmetic

theorem isMultiplicative_powerShiftedReciprocalAmplitude (c : ℝ) :
    (powerShiftedReciprocalAmplitude c).IsMultiplicative :=
  (isMultiplicative_powerShiftedMoebius c).mul isMultiplicative_reciprocalNatArithmetic

theorem powerShiftedReciprocalAmplitude_zero :
    powerShiftedReciprocalAmplitude 0 = reciprocalMoebiusAmplitude := by
  have hm : powerShiftedMoebius 0 = ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) := by
    ext n
    simp only [powerShiftedMoebius_apply, Real.rpow_zero, mul_one, ArithmeticFunction.intCoe_apply]
  rw [powerShiftedReciprocalAmplitude, hm, reciprocalMoebiusAmplitude]

/-- Each fixed arithmetic coefficient is continuous in the power shift. -/
theorem continuous_powerShiftedReciprocalAmplitude (n : ℕ) :
    Continuous (fun c : ℝ => powerShiftedReciprocalAmplitude c n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  simp only [powerShiftedReciprocalAmplitude, ArithmeticFunction.mul_apply, powerShiftedMoebius_apply]
  apply continuous_finset_sum
  intro x hx
  have hxprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hx0 : x.1 ≠ 0 := by
    intro h
    apply hn
    rw [← hxprod, h, zero_mul]
  have hxR : (0 : ℝ) < x.1 := by exact_mod_cast Nat.pos_of_ne_zero hx0
  have hxne : (x.1 : ℝ) ≠ 0 := hxR.ne'
  fun_prop

/-- The full shifted prime-power coefficient has only two Möbius terms. -/
theorem powerShiftedReciprocalAmplitude_prime_pow (c : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    powerShiftedReciprocalAmplitude c (p ^ (k + 1)) =
      (1 - (p : ℝ) ^ (1 + c)) / (p : ℝ) ^ (k + 1) := by
  rw [powerShiftedReciprocalAmplitude, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => powerShiftedMoebius c i * reciprocalNatArithmetic j),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range k,
      powerShiftedMoebius c (p ^ (i + 1 + 1)) *
        reciprocalNatArithmetic (p ^ (k + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i hi
    rw [powerShiftedMoebius_apply, moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [Finset.sum_eq_zero hz]
  simp only [zero_add, powerShiftedMoebius_apply, pow_zero, moebius_apply_one,
    Nat.cast_one, Real.one_rpow, Int.cast_one, one_mul, Nat.div_one, pow_one,
    moebius_apply_prime hp, Int.cast_neg, neg_mul]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdiv : p ^ (k + 1) / p = p ^ k := by simp [pow_succ, hp.ne_zero]
  rw [hdiv,
    reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero),
    reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)]
  push_cast
  rw [Real.rpow_add hp0, Real.rpow_one, pow_succ]
  field_simp [hp0.ne'] <;> ring

/-- The shifted prime numerator is bounded by the original numerator times a small power. -/
theorem abs_one_sub_rpow_one_add_le {p : ℝ} (hp : 2 ≤ p) (c : ℝ) :
    |1 - p ^ (1 + c)| ≤ (p - 1) * p ^ (2 * |c|) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hp1 : 1 ≤ p := by linarith only [hp]
  let q : ℝ := p ^ |c|
  have hq : 1 ≤ q := Real.one_le_rpow hp1 (abs_nonneg c)
  have hy : 0 ≤ p ^ (1 + c) := Real.rpow_nonneg hp0.le _
  have hup : p ^ (1 + c) ≤ p * q := by
    calc
      _ ≤ p ^ (1 + |c|) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith only [le_abs_self c])
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_one]
  have hpq : 2 ≤ p * q := by
    simpa only [mul_one] using mul_le_mul hp hq zero_le_one hp0.le
  have habs : |1 - p ^ (1 + c)| ≤ p * q - 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hy, hup, hpq]
  have hprod : 0 ≤ (q - 1) * ((p - 1) * q - 1) := by
    have hpq' : 1 ≤ (p - 1) * q := by
      simpa only [one_mul] using mul_le_mul (show 1 ≤ p - 1 by linarith only [hp])
        hq zero_le_one (show 0 ≤ p - 1 by linarith only [hp])
    exact mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hpq')
  have hs : q ^ 2 = p ^ (2 * |c|) := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    congr 1
    ring
  calc
    _ ≤ p * q - 1 := habs
    _ ≤ (p - 1) * q ^ 2 := by nlinarith only [hprod]
    _ = _ := by rw [hs]

/-- A prime-power amplitude costs only the small power of its active prime. -/
theorem abs_powerShiftedReciprocalAmplitude_prime_pow_le (c : ℝ)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |powerShiftedReciprocalAmplitude c (p ^ (k + 1))| ≤
      (p : ℝ) ^ (2 * |c|) * |reciprocalMoebiusAmplitude (p ^ (k + 1))| := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hpR]
  rw [← powerShiftedReciprocalAmplitude_zero, powerShiftedReciprocalAmplitude_prime_pow c hp,
    powerShiftedReciprocalAmplitude_prime_pow 0 hp]
  simp only [add_zero, Real.rpow_one, abs_div, abs_of_pos (pow_pos hp0 _)]
  have hn : |1 - (p : ℝ)| = (p : ℝ) - 1 := by
    rw [abs_of_nonpos (by linarith only [hpR])]
    ring
  rw [hn]
  exact (div_le_div_of_nonneg_right (abs_one_sub_rpow_one_add_le hpR c)
    (pow_nonneg hp0.le _)).trans_eq (by ring)

/-- Every shifted amplitude is dominated by the original one times `n^(2|c|)`. -/
theorem abs_powerShiftedReciprocalAmplitude_le (c : ℝ) (n : ℕ) :
    |powerShiftedReciprocalAmplitude c n| ≤
      (n : ℝ) ^ (2 * |c|) * |reciprocalMoebiusAmplitude n| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [IsMultiplicative.multiplicative_factorization (powerShiftedReciprocalAmplitude c)
      (isMultiplicative_powerShiftedReciprocalAmplitude c) hn.ne',
    IsMultiplicative.multiplicative_factorization reciprocalMoebiusAmplitude
      isMultiplicative_reciprocalMoebiusAmplitude hn.ne',
    ← rpowArith_apply_of_ne_zero (2 * |c|) hn.ne',
    IsMultiplicative.multiplicative_factorization (rpowArith (2 * |c|))
      (isMultiplicative_rpowArith _) hn.ne']
  simp only [Finsupp.prod]
  rw [Finset.abs_prod, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact abs_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    have hk : 1 ≤ n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    obtain ⟨k, he⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [he, rpowArith_apply_of_ne_zero _ (pow_ne_zero _ hprime.ne_zero)]
    refine (abs_powerShiftedReciprocalAmplitude_prime_pow_le c hprime k).trans ?_
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.rpow_le_rpow (Nat.cast_nonneg p) _ (by positivity)
    exact_mod_cast (show p ≤ p ^ (k + 1) by
      simpa only [pow_one] using Nat.pow_le_pow_right hprime.pos (show 1 ≤ k + 1 by omega))

/-- On its finite cutoff, a reciprocal-logarithmic shift has a constant majorant. -/
theorem abs_powerShiftedReciprocalAmplitude_log_shift_le {N : ℕ} (hN : 1 < N)
    (c : ℝ) {n : ℕ} (hn : n ≤ N) :
    |powerShiftedReciprocalAmplitude (c / Real.log N) n| ≤
      Real.exp (2 * |c|) * |reciprocalMoebiusAmplitude n| := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : 0 < Real.log N := Real.log_pos hN1
  refine (abs_powerShiftedReciprocalAmplitude_le (c / Real.log N) n).trans ?_
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ (N : ℝ) ^ (2 * |c / Real.log N|) := Real.rpow_le_rpow (Nat.cast_nonneg n)
      (by exact_mod_cast hn) (by positivity)
    _ = Real.exp (2 * |c|) := by
      rw [Real.rpow_def_of_pos hN0, abs_div, abs_of_pos hlog]
      congr 1
      field_simp [hlog.ne'] <;> ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
