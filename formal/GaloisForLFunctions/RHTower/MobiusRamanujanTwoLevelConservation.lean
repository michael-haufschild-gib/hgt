import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries

/-!
# Two-level primitive Fourier conservation of the literal Möbius source

Paper argument. Ramanujan inversion gives
`c_(p^(k+1))(n) = p^(k+1) 1_(p^(k+1)|n) - p^k 1_(p^k|n)`.
Multiplication by `mu(n)` kills either indicator when its exponent is at least two.
Thus all primitive sums at conductors `p^3,p^4,...` vanish. The two surviving
coefficients, at `p` and `p^2`, sum to `-mu(n)`. Finite summation preserves these
identities with arbitrary complex weights and without squaring the coefficients.

This is a classical Fourier bridge and an exact limit on an attempted averaged
rational-cusp replication mechanism, not an RH estimate. It concerns complete
primitive sums; neither individual Fourier values nor their energy must vanish.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

/-- Index `k` denotes the positive conductor `p^(k+1)`. -/
abbrev mobiusPrimePowerModulus (p : {p : ℕ // Nat.Prime p}) (k : ℕ) : CGLPositiveModulus :=
  ⟨(p : ℕ) ^ (k + 1), pow_pos p.property.pos _⟩

theorem ramanujanPrimePower_two_divisibility_layers
    (p : {p : ℕ // Nat.Prime p}) (k n : ℕ) :
    cglRamanujanAdditiveSum (mobiusPrimePowerModulus p k) n =
      (if (p : ℕ) ^ (k + 1) ∣ n then ((p : ℕ) ^ (k + 1) : ℂ) else 0) -
      (if (p : ℕ) ^ k ∣ n then ((p : ℕ) ^ k : ℂ) else 0) := by
  classical
  rcases p with ⟨p, hp⟩
  rw [cglRamanujanAdditiveSum_eq_mobiusDivisorFilter]
  dsimp only [mobiusPrimePowerModulus]
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have htail : (∑ j ∈ Finset.range k,
      ((ArithmeticFunction.moebius ((p : ℕ) ^ (j + 1 + 1)) : ℤ) : ℂ) *
        (if (p : ℕ) ^ (k + 1) / (p : ℕ) ^ (j + 1 + 1) ∣
            (n : ZMod ((p : ℕ) ^ (k + 1))).val
          then (((p : ℕ) ^ (k + 1) / (p : ℕ) ^ (j + 1 + 1) : ℕ) : ℂ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [htail]
  simp only [pow_zero, ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.div_one,
    one_mul, pow_one, ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg,
    zero_add, neg_mul]
  have hquot : (p : ℕ) ^ (k + 1) / (p : ℕ) = (p : ℕ) ^ k := by
    simpa using Nat.pow_div (x := p) (m := k + 1) (n := 1) (by omega) hp.pos
  rw [hquot]
  simp only [GaloisForLFunctions.RHTower.ccmRational_dvd_zmodVal_natCast_iff
      (Nat.pow_dvd_pow (p : ℕ) (Nat.le_succ k)),
    GaloisForLFunctions.RHTower.ccmRational_dvd_zmodVal_natCast_iff (dvd_refl _),
    Nat.cast_pow]
  ring

private theorem moebius_eq_zero_of_prime_square_dvd
    (p : {p : ℕ // Nat.Prime p}) {n : ℕ} (h : (p : ℕ) ^ 2 ∣ n) :
    ArithmeticFunction.moebius n = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  exact p.property.not_isUnit (hs p (by simpa [pow_two] using h))

private theorem moebius_mul_prime_indicator_vanish
    (p : {p : ℕ // Nat.Prime p}) (k n : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (if (p : ℕ) ^ (k + 2) ∣ n then ((p : ℕ) ^ (k + 2) : ℂ) else 0) = 0 := by
  split_ifs with h
  · have hz := moebius_eq_zero_of_prime_square_dvd p
      ((Nat.pow_dvd_pow (p : ℕ) (show 2 ≤ k + 2 by omega)).trans h)
    simp [hz]
  · simp

/-- Prime-power primitive coefficients vanish above exponent two, on the actual source. -/
theorem moebius_ramanujanPrimePower_high_vanish (p : {p : ℕ // Nat.Prime p}) (k n : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      cglRamanujanAdditiveSum (mobiusPrimePowerModulus p (k + 2)) n = 0 := by
  rw [ramanujanPrimePower_two_divisibility_layers, mul_sub]
  have htop := moebius_mul_prime_indicator_vanish p (k + 1) n
  have hlow := moebius_mul_prime_indicator_vanish p k n
  simp only [show k + 2 + 1 = k + 1 + 2 by omega, htop, hlow, sub_self]

/-- The first two primitive coefficient layers recover minus the original Möbius sign. -/
theorem moebius_ramanujanPrimePower_two_level (p : {p : ℕ // Nat.Prime p}) (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        cglRamanujanAdditiveSum (mobiusPrimePowerModulus p 0) n +
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        cglRamanujanAdditiveSum (mobiusPrimePowerModulus p 1) n =
      -((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  rw [ramanujanPrimePower_two_divisibility_layers,
    ramanujanPrimePower_two_divisibility_layers]
  simp only [zero_add, pow_zero, one_dvd, if_true, mul_sub]
  have hz := moebius_mul_prime_indicator_vanish p 0 n
  norm_num only at hz ⊢
  rw [hz]
  ring

/-- Complete primitive additive Fourier readout, retaining every unsquared source coefficient. -/
def mobiusPrimitivePrimePowerReadout (p : {p : ℕ // Nat.Prime p}) (k : ℕ)
    (s : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ a ∈ (Finset.univ : Finset (ZMod (mobiusPrimePowerModulus p k).value)).filter IsUnit,
    ∑ n ∈ s, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * w n *
      ZMod.stdAddChar (a * (n : ZMod (mobiusPrimePowerModulus p k).value))

theorem mobiusPrimitivePrimePowerReadout_eq_ramanujan
    (p : {p : ℕ // Nat.Prime p}) (k : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) :
    mobiusPrimitivePrimePowerReadout p k s w =
      ∑ n ∈ s, (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        cglRamanujanAdditiveSum (mobiusPrimePowerModulus p k) n) * w n := by
  unfold mobiusPrimitivePrimePowerReadout
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  unfold cglRamanujanAdditiveSum
  ring

/-- No tower of nonzero complete primitive sums exists past conductor `p²`. -/
theorem mobiusPrimitivePrimePowerReadout_high_vanish
    (p : {p : ℕ // Nat.Prime p}) (k : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) :
    mobiusPrimitivePrimePowerReadout p (k + 2) s w = 0 := by
  rw [mobiusPrimitivePrimePowerReadout_eq_ramanujan]
  apply Finset.sum_eq_zero
  intro n _
  rw [moebius_ramanujanPrimePower_high_vanish p k n, zero_mul]

/-- Exact two-level conservation, valid at every finite cutoff and for arbitrary complex weights. -/
theorem mobiusPrimitivePrimePowerReadout_two_level_reconstruction
    (p : {p : ℕ // Nat.Prime p}) (s : Finset ℕ) (w : ℕ → ℂ) :
    mobiusPrimitivePrimePowerReadout p 0 s w +
      mobiusPrimitivePrimePowerReadout p 1 s w =
        -∑ n ∈ s, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * w n := by
  rw [mobiusPrimitivePrimePowerReadout_eq_ramanujan,
    mobiusPrimitivePrimePowerReadout_eq_ramanujan, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← add_mul, moebius_ramanujanPrimePower_two_level]
  ring

end
end RHTower
