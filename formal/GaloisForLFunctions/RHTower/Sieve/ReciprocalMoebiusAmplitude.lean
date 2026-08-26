import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientResidueKernel

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Completely multiplicative reciprocal coefficient, extended by zero at zero. -/
def reciprocalNatArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1 / (n : ℝ), by simp⟩

theorem reciprocalNatArithmetic_apply {n : ℕ} (hn : n ≠ 0) :
    reciprocalNatArithmetic n = 1 / (n : ℝ) := by
  simp [reciprocalNatArithmetic, hn]

@[simp] theorem reciprocalNatArithmetic_one : reciprocalNatArithmetic 1 = 1 := by
  simp [reciprocalNatArithmetic]

theorem isMultiplicative_reciprocalNatArithmetic :
    reciprocalNatArithmetic.IsMultiplicative := by
  constructor
  · exact reciprocalNatArithmetic_one
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := by simpa [Nat.Coprime] using hmn
      subst hn
      simp [reciprocalNatArithmetic]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := by simpa [Nat.Coprime] using hmn
      subst hm1
      simp [reciprocalNatArithmetic]
    rw [reciprocalNatArithmetic_apply (Nat.mul_ne_zero hm.ne' hn.ne'),
      reciprocalNatArithmetic_apply hm.ne', reciprocalNatArithmetic_apply hn.ne']
    push_cast
    ring

/-- Möbius--reciprocal amplitude in the Euler correction. -/
def reciprocalMoebiusAmplitude : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
    reciprocalNatArithmetic

theorem isMultiplicative_reciprocalMoebiusAmplitude :
    reciprocalMoebiusAmplitude.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    isMultiplicative_reciprocalNatArithmetic

theorem zeta_mul_reciprocalMoebiusAmplitude :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
      reciprocalMoebiusAmplitude = reciprocalNatArithmetic := by
  rw [reciprocalMoebiusAmplitude, ← mul_assoc]
  have hzm :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) = 1 := by
    rw [mul_comm]
    exact ArithmeticFunction.coe_moebius_mul_coe_zeta
  rw [hzm, one_mul]

theorem sum_divisors_reciprocalMoebiusAmplitude (n : ℕ) :
    ∑ d ∈ n.divisors, reciprocalMoebiusAmplitude d = reciprocalNatArithmetic n := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, zeta_mul_reciprocalMoebiusAmplitude]

@[simp] theorem reciprocalMoebiusAmplitude_one : reciprocalMoebiusAmplitude 1 = 1 := by
  have h := sum_divisors_reciprocalMoebiusAmplitude 1
  simpa using h

/-- Prime-power coefficient of the Möbius--reciprocal amplitude. -/
theorem reciprocalMoebiusAmplitude_prime_pow {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    reciprocalMoebiusAmplitude (p ^ i) =
      1 / ((p : ℝ) ^ i) - 1 / ((p : ℝ) ^ (i - 1)) := by
  have hsum := sum_divisors_reciprocalMoebiusAmplitude (p ^ i)
  rw [Nat.sum_divisors_prime_pow hp,
    reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)] at hsum
  have hprev := sum_divisors_reciprocalMoebiusAmplitude (p ^ (i - 1))
  rw [Nat.sum_divisors_prime_pow hp,
    reciprocalNatArithmetic_apply (pow_ne_zero _ hp.ne_zero)] at hprev
  have hiEq : i - 1 + 1 = i := Nat.sub_add_cancel hi
  rw [hiEq] at hprev
  rw [Finset.sum_range_succ, hprev] at hsum
  push_cast at hsum
  linarith

theorem reciprocalMoebiusAmplitude_prime_pow_succ {p i : ℕ} (hp : p.Prime) :
    reciprocalMoebiusAmplitude (p ^ (i + 1)) =
      -(((p : ℝ) - 1) / (p : ℝ)) * (1 / (p : ℝ)) ^ i := by
  rw [reciprocalMoebiusAmplitude_prime_pow hp (by omega)]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [show i + 1 - 1 = i by omega, pow_succ]
  field_simp [hp0]
  have hpow : (p : ℝ) ^ i * ((p : ℝ)⁻¹) ^ i = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hp0, one_pow]
  calc
    1 - (p : ℝ) = -(p : ℝ) * 1 + 1 := by ring
    _ = -(p : ℝ) * ((p : ℝ) ^ i * ((p : ℝ)⁻¹) ^ i) +
        ((p : ℝ) ^ i * ((p : ℝ)⁻¹) ^ i) := by rw [hpow]
    _ = -((p : ℝ) * (p : ℝ) ^ i * ((p : ℝ)⁻¹) ^ i) +
        (p : ℝ) ^ i * ((p : ℝ)⁻¹) ^ i := by ring
    _ = -((p : ℝ) ^ i * ((p : ℝ) - 1) * (1 / (p : ℝ)) ^ i) := by
      rw [one_div]
      ring

private theorem reciprocal_prime_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖(1 / (p : ℝ))‖ < 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpR)]
  exact (div_lt_one hpR).mpr (by exact_mod_cast hp.one_lt)

theorem summable_abs_reciprocalMoebiusAmplitude_prime_pow {p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => |reciprocalMoebiusAmplitude (p ^ i)|) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hgeom : Summable (fun i : ℕ => (1 / (p : ℝ)) ^ i) :=
    summable_geometric_of_norm_lt_one (reciprocal_prime_norm_lt_one hp)
  have htail : Summable (fun i : ℕ =>
      |reciprocalMoebiusAmplitude (p ^ (i + 1))|) := by
    have hscaled := hgeom.mul_left (((p : ℝ) - 1) / (p : ℝ))
    apply hscaled.congr
    intro i
    rw [reciprocalMoebiusAmplitude_prime_pow_succ hp, abs_mul, abs_neg,
      abs_of_pos (by
        exact div_pos (sub_pos.mpr (by exact_mod_cast hp.one_lt)) hpR),
      abs_pow, abs_of_pos (one_div_pos.mpr hpR)]
  exact (summable_nat_add_iff 1).mp (by
    simpa only [Nat.add_comm] using htail)

theorem summable_reciprocalMoebiusAmplitude_prime_pow {p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => reciprocalMoebiusAmplitude (p ^ i)) := by
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using summable_abs_reciprocalMoebiusAmplitude_prime_pow hp

/-- Signed local correction amplitude has zero total mass at every prime. -/
theorem tsum_reciprocalMoebiusAmplitude_prime_pow {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, reciprocalMoebiusAmplitude (p ^ i)) = 0 := by
  let f : ℕ → ℝ := fun i => reciprocalMoebiusAmplitude (p ^ i)
  have hf : Summable f := summable_reciprocalMoebiusAmplitude_prime_pow hp
  have hsplit := hf.sum_add_tsum_nat_add 1
  have htail : (∑' i : ℕ, f (i + 1)) = -1 := by
    calc
      (∑' i : ℕ, f (i + 1)) =
          ∑' i : ℕ, (-(((p : ℝ) - 1) / (p : ℝ))) * (1 / (p : ℝ)) ^ i := by
        congr 1
        funext i
        exact reciprocalMoebiusAmplitude_prime_pow_succ hp
      _ = (-(((p : ℝ) - 1) / (p : ℝ))) *
          ∑' i : ℕ, (1 / (p : ℝ)) ^ i := tsum_mul_left
      _ = -1 := by
        rw [tsum_geometric_of_norm_lt_one (reciprocal_prime_norm_lt_one hp)]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
        field_simp [hp0, hp1]
  rw [show ∑ i ∈ Finset.range 1, f i = 1 by simp [f], htail] at hsplit
  linarith

/-- Absolute local correction amplitude has total mass two. -/
theorem tsum_abs_reciprocalMoebiusAmplitude_prime_pow {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, |reciprocalMoebiusAmplitude (p ^ i)|) = 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  let f : ℕ → ℝ := fun i => |reciprocalMoebiusAmplitude (p ^ i)|
  have hf : Summable f := summable_abs_reciprocalMoebiusAmplitude_prime_pow hp
  have hsplit := hf.sum_add_tsum_nat_add 1
  have htail : (∑' i : ℕ, f (i + 1)) = 1 := by
    calc
      (∑' i : ℕ, f (i + 1)) =
          ∑' i : ℕ, (((p : ℝ) - 1) / (p : ℝ)) * (1 / (p : ℝ)) ^ i := by
        congr 1
        funext i
        dsimp [f]
        rw [reciprocalMoebiusAmplitude_prime_pow_succ hp, abs_mul, abs_neg,
          abs_of_pos (by
            exact div_pos (sub_pos.mpr (by exact_mod_cast hp.one_lt)) hpR),
          abs_pow, abs_of_pos (one_div_pos.mpr hpR)]
      _ = (((p : ℝ) - 1) / (p : ℝ)) *
          ∑' i : ℕ, (1 / (p : ℝ)) ^ i := tsum_mul_left
      _ = 1 := by
        rw [tsum_geometric_of_norm_lt_one (reciprocal_prime_norm_lt_one hp)]
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
        field_simp [hp0, hp1]
  rw [show ∑ i ∈ Finset.range 1, f i = 1 by simp [f], htail] at hsplit
  linarith

end

end RHTower.Sieve
