import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientDivisorIdentity
import GaloisForLFunctions.RHTower.SelbergPairingPrimeSquare
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.PNTPlus.Wiener
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The squarefree-totient residue kernel
-/

open ArithmeticFunction Finset

namespace RHTower.Sieve

/-- The numerator-normalized squarefree reciprocal-totient weight. -/
noncomputable def scaledSqfreeTotientInv : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * sqfreeTotientInv n, by simp⟩

@[simp] theorem scaledSqfreeTotientInv_apply (n : ℕ) :
    scaledSqfreeTotientInv n = (n : ℝ) * sqfreeTotientInv n := rfl

theorem isMultiplicative_scaledSqfreeTotientInv : scaledSqfreeTotientInv.IsMultiplicative := by
  constructor
  · simp [scaledSqfreeTotientInv_apply, sqfreeTotientInv_apply]
  · intro m n hmn
    rw [scaledSqfreeTotientInv_apply, scaledSqfreeTotientInv_apply,
      scaledSqfreeTotientInv_apply, isMultiplicative_sqfreeTotientInv.map_mul_of_coprime hmn]
    push_cast
    ring

/-- Möbius inverse of the numerator-normalized squarefree reciprocal-totient weight. -/
noncomputable def squarefreeTotientResidue : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) *
    scaledSqfreeTotientInv

theorem isMultiplicative_squarefreeTotientResidue : squarefreeTotientResidue.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    isMultiplicative_scaledSqfreeTotientInv

/-- Exact divisor inversion defining the residue kernel. -/
theorem zeta_mul_squarefreeTotientResidue :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
      squarefreeTotientResidue = scaledSqfreeTotientInv := by
  rw [squarefreeTotientResidue, ← mul_assoc]
  have hzm :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) = 1 := by
    rw [mul_comm]
    exact ArithmeticFunction.coe_moebius_mul_coe_zeta
  rw [hzm, one_mul]

theorem sum_divisors_squarefreeTotientResidue (n : ℕ) :
    ∑ d ∈ n.divisors, squarefreeTotientResidue d = scaledSqfreeTotientInv n := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, zeta_mul_squarefreeTotientResidue]

@[simp] theorem scaledSqfreeTotientInv_one : scaledSqfreeTotientInv 1 = 1 := by
  simp [scaledSqfreeTotientInv_apply, sqfreeTotientInv_apply]

theorem scaledSqfreeTotientInv_prime {p : ℕ} (hp : p.Prime) :
    scaledSqfreeTotientInv p = (p : ℝ) / ((p : ℝ) - 1) := by
  rw [scaledSqfreeTotientInv_apply, sqfreeTotientInv_apply, if_pos hp.squarefree,
    Nat.totient_prime hp]
  push_cast [Nat.cast_sub hp.one_lt.le]
  ring

theorem scaledSqfreeTotientInv_prime_pow_eq_zero {p i : ℕ} (hp : p.Prime) (hi : 2 ≤ i) :
    scaledSqfreeTotientInv (p ^ i) = 0 := by
  rw [scaledSqfreeTotientInv_apply, sqfreeTotientInv_apply, if_neg]
  · ring
  · intro hsq
    have hdvd : p * p ∣ p ^ i := by
      simpa [pow_two] using pow_dvd_pow p hi
    have hunit := hsq p hdvd
    rw [Nat.isUnit_iff] at hunit
    exact hp.ne_one hunit

@[simp] theorem squarefreeTotientResidue_one : squarefreeTotientResidue 1 = 1 := by
  have h := sum_divisors_squarefreeTotientResidue 1
  norm_num [scaledSqfreeTotientInv_apply, sqfreeTotientInv_apply] at h ⊢
  exact h

theorem squarefreeTotientResidue_prime {p : ℕ} (hp : p.Prime) :
    squarefreeTotientResidue p = 1 / ((p : ℝ) - 1) := by
  have h' := sum_divisors_squarefreeTotientResidue (p ^ 1)
  rw [Nat.sum_divisors_prime_pow hp] at h'
  rw [pow_one, scaledSqfreeTotientInv_prime hp] at h'
  have htwo : ∑ j ∈ Finset.range 2, squarefreeTotientResidue (p ^ j) =
      1 + squarefreeTotientResidue p := by
    norm_num [Finset.sum_range_succ]
  rw [htwo] at h'
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR)
  field_simp [hne] at h' ⊢
  linarith

theorem squarefreeTotientResidue_prime_sq {p : ℕ} (hp : p.Prime) :
    squarefreeTotientResidue (p ^ 2) = -(p : ℝ) / ((p : ℝ) - 1) := by
  have h := sum_divisors_squarefreeTotientResidue (p ^ 2)
  rw [Nat.sum_divisors_prime_pow hp, scaledSqfreeTotientInv_prime_pow_eq_zero hp (by omega)] at h
  have hthree : ∑ j ∈ Finset.range 3, squarefreeTotientResidue (p ^ j) =
      1 + squarefreeTotientResidue p + squarefreeTotientResidue (p ^ 2) := by
    norm_num [Finset.sum_range_succ]
  rw [hthree, squarefreeTotientResidue_prime hp] at h
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR)
  field_simp [hne] at h ⊢
  linarith

/-- The residue kernel vanishes beyond the prime-square layer. -/
theorem squarefreeTotientResidue_prime_pow_eq_zero {p i : ℕ} (hp : p.Prime) (hi : 3 ≤ i) :
    squarefreeTotientResidue (p ^ i) = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      have hsum := sum_divisors_squarefreeTotientResidue (p ^ i)
      rw [Nat.sum_divisors_prime_pow hp,
        scaledSqfreeTotientInv_prime_pow_eq_zero hp (by omega)] at hsum
      rw [Finset.sum_range_succ] at hsum
      have hhead : ∑ j ∈ Finset.range i, squarefreeTotientResidue (p ^ j) = 0 := by
        rw [show i = 3 + (i - 3) by omega]
        rw [Finset.sum_range_add]
        have hfirst : ∑ j ∈ Finset.range 3, squarefreeTotientResidue (p ^ j) = 0 := by
          have hthree : ∑ j ∈ Finset.range 3, squarefreeTotientResidue (p ^ j) =
              1 + squarefreeTotientResidue p + squarefreeTotientResidue (p ^ 2) := by
            norm_num [Finset.sum_range_succ]
          rw [hthree, squarefreeTotientResidue_prime hp,
            squarefreeTotientResidue_prime_sq hp]
          have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
          have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpR)
          field_simp [hne]
          ring
        rw [hfirst, zero_add]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finset.mem_range] at hj
        simpa [Nat.add_comm] using ih (j + 3) (by omega) (by omega)
      rw [hhead, zero_add] at hsum
      exact hsum

/-! ### The reciprocal residue kernel -/

/-- The residue kernel after the reciprocal weight required by harmonic divisor summation. -/
noncomputable def squarefreeTotientHarmonicResidue : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else squarefreeTotientResidue n / (n : ℝ), by simp⟩

theorem squarefreeTotientHarmonicResidue_apply_def (n : ℕ) :
    squarefreeTotientHarmonicResidue n =
      if n = 0 then 0 else squarefreeTotientResidue n / (n : ℝ) := rfl

theorem isMultiplicative_squarefreeTotientHarmonicResidue :
    squarefreeTotientHarmonicResidue.IsMultiplicative := by
  constructor
  · simp [squarefreeTotientHarmonicResidue]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := by simpa [Nat.Coprime] using hmn
      subst hn
      simp [squarefreeTotientHarmonicResidue]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := by simpa [Nat.Coprime] using hmn
      subst hm1
      simp [squarefreeTotientHarmonicResidue]
    have hm0 : m ≠ 0 := hm.ne'
    have hn0 : n ≠ 0 := hn.ne'
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
    rw [squarefreeTotientHarmonicResidue_apply_def,
      squarefreeTotientHarmonicResidue_apply_def,
      squarefreeTotientHarmonicResidue_apply_def,
      if_neg hmn0, if_neg hm0, if_neg hn0,
      isMultiplicative_squarefreeTotientResidue.map_mul_of_coprime hmn, Nat.cast_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

@[simp] theorem squarefreeTotientHarmonicResidue_zero :
  squarefreeTotientHarmonicResidue 0 = 0 := by
  simp [squarefreeTotientHarmonicResidue]

@[simp] theorem squarefreeTotientHarmonicResidue_one :
  squarefreeTotientHarmonicResidue 1 = 1 := by
  simp [squarefreeTotientHarmonicResidue]

theorem squarefreeTotientHarmonicResidue_apply {n : ℕ} (hn : n ≠ 0) :
    squarefreeTotientHarmonicResidue n = squarefreeTotientResidue n / (n : ℝ) := by
  change (if n = 0 then 0 else squarefreeTotientResidue n / (n : ℝ)) = _
  rw [if_neg hn]

theorem squarefreeTotientHarmonicResidue_prime {p : ℕ} (hp : p.Prime) :
    squarefreeTotientHarmonicResidue p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [squarefreeTotientHarmonicResidue_apply hp.ne_zero,
    squarefreeTotientResidue_prime hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

theorem squarefreeTotientHarmonicResidue_prime_sq {p : ℕ} (hp : p.Prime) :
    squarefreeTotientHarmonicResidue (p ^ 2) =
      -(1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  rw [squarefreeTotientHarmonicResidue_apply (pow_ne_zero _ hp.ne_zero),
    squarefreeTotientResidue_prime_sq hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  push_cast
  field_simp [hp0, hp1]

theorem squarefreeTotientHarmonicResidue_prime_pow_eq_zero {p i : ℕ}
    (hp : p.Prime) (hi : 3 ≤ i) :
    squarefreeTotientHarmonicResidue (p ^ i) = 0 := by
  rw [squarefreeTotientHarmonicResidue_apply (pow_ne_zero _ hp.ne_zero),
    squarefreeTotientResidue_prime_pow_eq_zero hp hi, zero_div]

theorem squarefreeTotientHarmonicResidue_prime_mass_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact one_div_pos.mpr (mul_pos hpR0 (sub_pos.mpr hpR1))

theorem summable_abs_squarefreeTotientHarmonicResidue_prime_pow {p : ℕ}
    (hp : p.Prime) :
    Summable (fun i : ℕ => |squarefreeTotientHarmonicResidue (p ^ i)|) := by
  apply summable_of_ne_finset_zero (s := {0, 1, 2})
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  rw [squarefreeTotientHarmonicResidue_prime_pow_eq_zero hp (by omega), abs_zero]

theorem tsum_abs_squarefreeTotientHarmonicResidue_prime_pow {p : ℕ}
    (hp : p.Prime) :
    (∑' i : ℕ, |squarefreeTotientHarmonicResidue (p ^ i)|) =
      1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [tsum_eq_sum (s := {0, 1, 2})]
  · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_singleton, pow_zero, pow_one,
      squarefreeTotientHarmonicResidue_one,
      squarefreeTotientHarmonicResidue_prime hp,
      squarefreeTotientHarmonicResidue_prime_sq hp]
    rw [abs_one, abs_of_pos (squarefreeTotientHarmonicResidue_prime_mass_pos hp),
      abs_neg, abs_of_pos (squarefreeTotientHarmonicResidue_prime_mass_pos hp)]
    ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [squarefreeTotientHarmonicResidue_prime_pow_eq_zero hp (by omega), abs_zero]

theorem tsum_squarefreeTotientHarmonicResidue_prime_pow {p : ℕ}
    (hp : p.Prime) :
    (∑' i : ℕ, squarefreeTotientHarmonicResidue (p ^ i)) = 1 := by
  rw [tsum_eq_sum (s := {0, 1, 2})]
  · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_singleton, pow_zero, pow_one,
      squarefreeTotientHarmonicResidue_one,
      squarefreeTotientHarmonicResidue_prime hp,
      squarefreeTotientHarmonicResidue_prime_sq hp]
    ring
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact squarefreeTotientHarmonicResidue_prime_pow_eq_zero hp (by omega)

theorem abs_squarefreeTotientHarmonicResidue_mul_of_coprime {m n : ℕ}
    (hmn : m.Coprime n) :
    |squarefreeTotientHarmonicResidue (m * n)| =
      |squarefreeTotientHarmonicResidue m| * |squarefreeTotientHarmonicResidue n| := by
  rw [isMultiplicative_squarefreeTotientHarmonicResidue.map_mul_of_coprime hmn, abs_mul]

theorem prod_primesBelow_abs_squarefreeTotientHarmonicResidue_le (N : ℕ) :
    (∏ p ∈ N.primesBelow, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ Real.exp 2 := by
  calc
    (∏ p ∈ N.primesBelow, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        ∏ p ∈ N.primesBelow, Real.exp (2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' := (Nat.mem_primesBelow.mp hp).2
        have hpos := squarefreeTotientHarmonicResidue_prime_mass_pos hp'
        rw [show 2 / ((p : ℝ) * ((p : ℝ) - 1)) =
          2 * (1 / ((p : ℝ) * ((p : ℝ) - 1))) by ring]
        linarith
      · intro p hp
        have hp' := (Nat.mem_primesBelow.mp hp).2
        have h := Real.add_one_le_exp (2 / ((p : ℝ) * ((p : ℝ) - 1)))
        simpa [add_comm] using h
    _ = Real.exp (∑ p ∈ N.primesBelow, 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp 2 := by
      rw [Real.exp_le_exp]
      calc
        (∑ p ∈ N.primesBelow, 2 / ((p : ℝ) * ((p : ℝ) - 1))) =
            2 * ∑ p ∈ N.primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ ≤ 2 := by
          nlinarith [RHTower.sum_primesBelow_inv_mul_sub_one_le N]

theorem sum_range_abs_squarefreeTotientHarmonicResidue_le (N : ℕ) :
    (∑ n ∈ Finset.range N, |squarefreeTotientHarmonicResidue n|) ≤ Real.exp 2 := by
  have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n : ℕ => |squarefreeTotientHarmonicResidue n|)
    (by simp)
    (fun {m n} hmn => abs_squarefreeTotientHarmonicResidue_mul_of_coprime hmn)
    (fun {p} hp => by
      simpa [Real.norm_eq_abs] using
        summable_abs_squarefreeTotientHarmonicResidue_prime_pow hp)
    N
  let e : {m // m ∈ Finset.Ico 1 N} ↪ N.smoothNumbers :=
    { toFun := fun m =>
        ⟨m, Nat.mem_smoothNumbers.mpr ⟨by
            exact Nat.ne_of_gt (Finset.mem_Ico.mp m.property).1,
          fun p hp => lt_of_le_of_lt (Nat.le_of_mem_primeFactorsList hp)
            (Finset.mem_Ico.mp m.property).2⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : N.smoothNumbers => (z : ℕ)) hab }
  let s : Finset N.smoothNumbers := (Finset.Ico 1 N).attach.map e
  have hfinite :
      (∑ m ∈ s, ‖|squarefreeTotientHarmonicResidue (m : ℕ)|‖) ≤
        ∏ p ∈ N.primesBelow, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    have hle := heuler.1.sum_le_tsum s
      (fun m _hm => norm_nonneg |squarefreeTotientHarmonicResidue (m : ℕ)|)
    have hle' :
        (∑ m ∈ s, |squarefreeTotientHarmonicResidue (m : ℕ)|) ≤
          ∑' m : N.smoothNumbers, |squarefreeTotientHarmonicResidue (m : ℕ)| := by
      simpa [Real.norm_eq_abs] using hle
    rw [heuler.2.tsum_eq] at hle'
    calc
      (∑ m ∈ s, ‖|squarefreeTotientHarmonicResidue (m : ℕ)|‖) =
          ∑ m ∈ s, |squarefreeTotientHarmonicResidue (m : ℕ)| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∏ p ∈ N.primesBelow,
          (∑' n : ℕ, |squarefreeTotientHarmonicResidue (p ^ n)|) := hle'
      _ = ∏ p ∈ N.primesBelow, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact tsum_abs_squarefreeTotientHarmonicResidue_prime_pow
          (Nat.mem_primesBelow.mp hp).2
  have hsumeq :
      (∑ m ∈ s, ‖|squarefreeTotientHarmonicResidue (m : ℕ)|‖) =
        ∑ n ∈ Finset.Ico 1 N, |squarefreeTotientHarmonicResidue n| := by
    simp only [s, Finset.sum_map]
    calc
      (∑ x ∈ (Finset.Ico 1 N).attach,
          ‖|squarefreeTotientHarmonicResidue ((e x : N.smoothNumbers) : ℕ)|‖) =
          ∑ x ∈ (Finset.Ico 1 N).attach,
            |squarefreeTotientHarmonicResidue (x : ℕ)| := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [e, Real.norm_eq_abs]
      _ = ∑ n ∈ Finset.Ico 1 N, |squarefreeTotientHarmonicResidue n| :=
        by
          simpa using Finset.sum_attach (Finset.Ico 1 N)
            (fun n : ℕ => |squarefreeTotientHarmonicResidue n|)
  have hrange :
      (∑ n ∈ Finset.Ico 1 N, |squarefreeTotientHarmonicResidue n|) =
        ∑ n ∈ Finset.range N, |squarefreeTotientHarmonicResidue n| := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
      exact hn.2
    · intro n hn hnIco
      simp only [Finset.mem_range] at hn
      have hn0 : n = 0 := by
        by_contra hn0
        apply hnIco
        exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn⟩
      subst n
      simp
  calc
    (∑ n ∈ Finset.range N, |squarefreeTotientHarmonicResidue n|) =
        ∑ n ∈ Finset.Ico 1 N, |squarefreeTotientHarmonicResidue n| := hrange.symm
    _ = ∑ m ∈ s, ‖|squarefreeTotientHarmonicResidue (m : ℕ)|‖ := hsumeq.symm
    _ ≤ ∏ p ∈ N.primesBelow, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := hfinite
    _ ≤ Real.exp 2 := prod_primesBelow_abs_squarefreeTotientHarmonicResidue_le N

theorem summable_abs_squarefreeTotientHarmonicResidue :
    Summable (fun n : ℕ => |squarefreeTotientHarmonicResidue n|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _)
  exact sum_range_abs_squarefreeTotientHarmonicResidue_le

theorem summable_squarefreeTotientHarmonicResidue :
    Summable (fun n : ℕ => squarefreeTotientHarmonicResidue n) := by
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using summable_abs_squarefreeTotientHarmonicResidue

theorem tsum_squarefreeTotientHarmonicResidue :
    (∑' n : ℕ, squarefreeTotientHarmonicResidue n) = 1 := by
  have hnorm : Summable (fun n : ℕ => ‖squarefreeTotientHarmonicResidue n‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_squarefreeTotientHarmonicResidue
  calc
    (∑' n : ℕ, squarefreeTotientHarmonicResidue n) =
        ∏' p : Nat.Primes,
          ∑' i : ℕ, squarefreeTotientHarmonicResidue ((p : ℕ) ^ i) :=
      (isMultiplicative_squarefreeTotientHarmonicResidue.eulerProduct_tprod hnorm).symm
    _ = ∏' _p : Nat.Primes, (1 : ℝ) := by
      congr 1
      funext p
      exact tsum_squarefreeTotientHarmonicResidue_prime_pow p.2
    _ = 1 := tprod_one

end RHTower.Sieve
