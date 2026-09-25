import Mathlib

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-!
# `φ(Nn) = φ(N) Σ_{e | n, (e,N)=1} μ(e) (n/e)`

`H_N(n) = Σ_{e | n, (e,N) = 1} μ(e)(n/e)` is the Dirichlet convolution `(μ χ_N) * id` (`Hf_eq`), hence multiplicative.
For coprime `a, b`, two instances of `φ(gcd(a,b)) φ(ab) = φ(a) φ(b) gcd(a,b)` give `φ(N) φ(Nab) = φ(Na) φ(Nb)`
(`totient_mul_coprime_split`); on prime powers both sides agree (`H_prime_pow`, `totient_mul_self_pow`). Induction over
coprime factorizations gives `φ(Nn) = φ(N) H_N(n)` (`totient_mul_eq`). This makes the constant term of the `Γ(N)`
Eisenstein series a product `ζ(2s-1) · Σ_{(e,N)=1} μ(e) e^{-2s}`.
-/

namespace GaloisForLFunctions.RHTower.TotientMulMoebius

/-- `H_N(n) = Σ_{e | n, (e,N)=1} μ(e) (n/e)`. -/
def H (N n : ℕ) : ℤ := ∑ e ∈ n.divisors.filter (fun e => e.Coprime N), μ e * ((n / e : ℕ) : ℤ)

theorem totient_mul_self_pow {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (k : ℕ) :
    (N * p ^ k).totient = p ^ k * N.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, mul_comm (N * p ^ k) p, Nat.totient_mul_of_prime_of_dvd hp
      (hpN.trans (Dvd.intro _ rfl)), ih]; ring

theorem H_prime_pow {N p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) :
    H N (p ^ k) = p ^ k - (if p.Coprime N then (p : ℤ) ^ (k - 1) else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold H
  rw [Nat.divisors_prime_pow hp, Finset.filter_map, Finset.sum_map, Finset.sum_filter]
  simp only [Function.Embedding.coeFn_mk, Function.comp_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hzero : ∀ j ∈ Finset.range k, (if (p ^ (j + 1 + 1)).Coprime N then μ (p ^ (j + 1 + 1)) *
      ((p ^ (k + 1) / p ^ (j + 1 + 1) : ℕ) : ℤ) else 0) = 0 := by
    intro j _
    split_ifs
    · rw [moebius_apply_prime_pow hp (Nat.succ_ne_zero _)]; simp
    · rfl
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hp1 : 1 < p := hp.one_lt
  have hdiv : p ^ (k + 1) / p ^ (0 + 1) = p ^ k := by
    rw [zero_add, pow_one, pow_succ, Nat.mul_div_cancel _ hp.pos]
  have hmu1 : μ (p ^ (0 + 1)) = -1 := by rw [zero_add, pow_one]; exact moebius_apply_prime hp
  rw [hmu1, hdiv]
  have hcop : (p ^ (0 + 1)).Coprime N ↔ p.Coprime N := by rw [zero_add, pow_one]
  simp only [pow_zero, Nat.coprime_one_left_eq_true, if_true, moebius_apply_one, Nat.div_one, Nat.add_sub_cancel]
  by_cases h : p.Coprime N
  · rw [if_pos (hcop.mpr h), if_pos h]; push_cast; ring
  · rw [if_neg (fun h' => h (hcop.mp h')), if_neg h]; push_cast; ring

/-- The coprimality indicator `χ_N(n) = [n ≠ 0, (n,N) = 1]`. -/
def chi (N : ℕ) : ArithmeticFunction ℤ := ⟨fun n => if n ≠ 0 ∧ n.Coprime N then 1 else 0, by simp⟩

theorem chi_mult (N : ℕ) : (chi N).IsMultiplicative := by
  refine ⟨by simp [chi], fun {m n} hmn => ?_⟩
  simp only [chi, ArithmeticFunction.coe_mk]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [ne_eq, hm, hn, hmn0, not_false_eq_true, true_and, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

/-- `H_N = (μ χ_N) * id` as an arithmetic function. -/
def Hf (N : ℕ) : ArithmeticFunction ℤ := (ArithmeticFunction.moebius.pmul (chi N)) * (ArithmeticFunction.id : ArithmeticFunction ℤ)

theorem Hf_mult (N : ℕ) : (Hf N).IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul (chi_mult N)).mul isMultiplicative_id.natCast

theorem Hf_eq (N n : ℕ) : Hf N n = H N n := by
  unfold Hf H
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun a b =>
    (ArithmeticFunction.moebius.pmul (chi N) : ArithmeticFunction ℤ) a * (ArithmeticFunction.id : ArithmeticFunction ℤ) b),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  simp only [ArithmeticFunction.pmul_apply, chi, ArithmeticFunction.coe_mk, ne_eq, he0, not_false_eq_true,
    true_and, ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  split_ifs <;> simp

theorem totient_mul_coprime_split {N a b : ℕ} (hN : 0 < N) (hab : a.Coprime b) :
    N.totient * (N * (a * b)).totient = (N * a).totient * (N * b).totient := by
  have hφ : 0 < N.totient := Nat.totient_pos.mpr hN
  have T1 := Nat.totient_gcd_mul_totient_mul (N * a) (N * b)
  rw [Nat.gcd_mul_left, hab, mul_one] at T1
  have T2 := Nat.totient_gcd_mul_totient_mul N (N * (a * b))
  rw [Nat.gcd_mul_right_right] at T2
  have e : N * a * (N * b) = N * (N * (a * b)) := by ring
  rw [e] at T1
  -- `φ(N²ab) = N φ(Nab)`
  have h2 : (N * (N * (a * b))).totient = (N * (a * b)).totient * N := by
    have := T2
    rw [mul_assoc] at this
    exact Nat.eq_of_mul_eq_mul_left hφ this
  rw [h2] at T1
  have : N.totient * (N * (a * b)).totient * N = (N * a).totient * (N * b).totient * N := by
    rw [← T1]; ring
  exact Nat.eq_of_mul_eq_mul_right hN this

/-- **`φ(Nn) = φ(N) · Σ_{e | n, (e,N)=1} μ(e) (n/e)`.** -/
theorem totient_mul_eq (N : ℕ) (hN : 0 < N) (n : ℕ) : ((N * n).totient : ℤ) = N.totient * H N n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [H_prime_pow hp k hk]
    by_cases hc : p.Coprime N
    · rw [if_pos hc, Nat.totient_mul (Nat.Coprime.pow_right k hc.symm), Nat.totient_prime_pow hp hk]
      have hp1 : 1 ≤ p := hp.one_lt.le
      push_cast [Nat.cast_sub hp1]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    · rw [if_neg hc, totient_mul_self_pow hp ((Nat.Prime.dvd_iff_not_coprime hp).mpr hc) k]
      push_cast; ring
  | zero => simp [H]
  | one =>
    have h1 : H N 1 = 1 := by
      unfold H
      rw [Nat.divisors_one, Finset.filter_singleton, if_pos (Nat.coprime_one_left N), Finset.sum_singleton,
        ArithmeticFunction.moebius_apply_one]
      norm_num
    rw [h1, mul_one, mul_one]
  | coprime a b _ _ hab iha ihb =>
    have hHm : H N (a * b) = H N a * H N b := by
      rw [← Hf_eq, ← Hf_eq, ← Hf_eq]; exact (Hf_mult N).map_mul_of_coprime hab
    have hφ : (0 : ℤ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr hN
    have key := totient_mul_coprime_split hN hab
    have keyZ : (N.totient : ℤ) * ((N * (a * b)).totient : ℤ) = ((N * a).totient : ℤ) * ((N * b).totient : ℤ) := by
      exact_mod_cast key
    rw [iha, ihb] at keyZ
    rw [hHm]
    have : (N.totient : ℤ) * ((N * (a * b)).totient : ℤ) = (N.totient : ℤ) * (N.totient * (H N a * H N b)) := by
      rw [keyZ]; ring
    exact mul_left_cancel₀ hφ.ne' this

end GaloisForLFunctions.RHTower.TotientMulMoebius
