import GaloisForLFunctions.SignedSuccessorArithmetic.TheOneThirdSuccessorFloor
import Mathlib.Tactic.NormNum.Prime

/-!
# The floor is attained at conductor three

The **conductor-three twins** are the completely multiplicative signs that agree with the
quadratic character `χ₃` modulo `3` away from `3`: `f(n) = ε^{v₃(n)} χ₃(n / 3^{v₃(n)})` with
`f(3) = ε ∈ {±1}`. Along the successor they have a rigid pattern:

* `f(3j+1) = 1`, `f(3j+2) = -1`, so the step `3j+1 → 3j+2` always flips;
* `f(3j+3) = ε f(j+1)` sits between `f(3j+2) = -1` and `f(3j+4) = 1`, so exactly one of the steps
  `3j+2 → 3j+3`, `3j+3 → 3j+4` keeps the sign.

Hence `A(3J+1) = J` exactly (`agreeCount_chi3Twin_three_mul_add_one`): one agreement per period,
with no error term. The doubled-agreement count vanishes identically
(`doubleAgreeCount_chi3Twin`), so the twins satisfy the two-scale identity with zero defect,
`C(2N+1) − σ(1) + C(N) = −N` at every `N`, and their logarithmic agreement mass is at most
`(1/3) log M + 1`. Together with the floor this proves that `1/3` is the optimal constant
(`one_third_floor_sharp`).

The twin with `ε = -1` agrees with the Liouville function at the primes `2, 3, 5` and first differs
at `7` (`chi3Twin_neg_one_vs_liouville`): no argument that uses only complete multiplicativity and
the prime values below `7` can move the successor floor of `λ` above `1/3`.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- The quadratic character modulo `3` on integers prime to `3`, as a sign. -/
def chi3Unit (n : ℕ) : ℤˣ := if n % 3 = 2 then -1 else 1

theorem chi3Unit_mul {m n : ℕ} (hm : ¬ 3 ∣ m) (hn : ¬ 3 ∣ n) :
    chi3Unit (m * n) = chi3Unit m * chi3Unit n := by
  have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn' : n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold chi3Unit
  rw [Nat.mul_mod]
  rcases hm' with h | h <;> rcases hn' with h' | h' <;> simp [h, h']

/-- The conductor-three twin with value `ε` at the prime `3`. -/
def chi3Twin (ε : ℤˣ) : CMSign where
  toFun n := ε ^ n.factorization 3 * chi3Unit (n / 3 ^ n.factorization 3)
  map_one' := by simp [chi3Unit]
  map_mul' := fun {m n} hm hn => by
    have hf : (m * n).factorization 3 = m.factorization 3 + n.factorization 3 := by
      rw [Nat.factorization_mul hm.ne' hn.ne']; rfl
    rw [Nat.ordCompl_mul, hf, chi3Unit_mul (Nat.not_dvd_ordCompl Nat.prime_three hm.ne')
      (Nat.not_dvd_ordCompl Nat.prime_three hn.ne')]
    exact (congrArg (· * _) (pow_add ε _ _)).trans (mul_mul_mul_comm _ _ _ _)

variable (ε : ℤˣ)

theorem chi3Twin_of_not_dvd {n : ℕ} (hn : ¬ 3 ∣ n) : chi3Twin ε n = chi3Unit n := by
  change ε ^ n.factorization 3 * chi3Unit (n / 3 ^ n.factorization 3) = _
  rw [Nat.factorization_eq_zero_of_not_dvd hn]
  simp

theorem chi3Twin_three : chi3Twin ε 3 = ε := by
  change ε ^ (3 : ℕ).factorization 3 * chi3Unit (3 / 3 ^ (3 : ℕ).factorization 3) = _
  rw [Nat.Prime.factorization_self Nat.prime_three]
  simp [chi3Unit]

theorem chi3Twin_three_mul {j : ℕ} (hj : 0 < j) : chi3Twin ε (3 * j) = ε * chi3Twin ε j := by
  rw [(chi3Twin ε).map_mul (by norm_num) hj, chi3Twin_three]

theorem chi3Twin_three_mul_add_one (j : ℕ) : chi3Twin ε (3 * j + 1) = 1 := by
  rw [chi3Twin_of_not_dvd ε (by omega)]; simp [chi3Unit]

theorem chi3Twin_three_mul_add_two (j : ℕ) : chi3Twin ε (3 * j + 2) = -1 := by
  rw [chi3Twin_of_not_dvd ε (by omega)]; simp [chi3Unit]

theorem chi3Twin_two : chi3Twin ε 2 = -1 := chi3Twin_three_mul_add_two ε 0

/-! ## The successor pattern of a twin -/

theorem succSign_chi3Twin_three_mul_add_one (j : ℕ) :
    succSign (chi3Twin ε) (3 * j + 1) = -1 := by
  rw [succSign, chi3Twin_three_mul_add_one, show 3 * j + 1 + 1 = 3 * j + 2 by omega,
    chi3Twin_three_mul_add_two, one_mul]

theorem succSign_chi3Twin_three_mul_add_two (j : ℕ) :
    succSign (chi3Twin ε) (3 * j + 2) = -(ε * chi3Twin ε (j + 1)) := by
  rw [succSign, chi3Twin_three_mul_add_two, show 3 * j + 2 + 1 = 3 * (j + 1) by omega,
    chi3Twin_three_mul ε j.succ_pos, neg_one_mul]

theorem succSign_chi3Twin_three_mul_add_three (j : ℕ) :
    succSign (chi3Twin ε) (3 * j + 3) = ε * chi3Twin ε (j + 1) := by
  rw [succSign, show 3 * j + 3 = 3 * (j + 1) by omega, chi3Twin_three_mul ε j.succ_pos,
    chi3Twin_three_mul_add_one, mul_one]

/-- The step `3j+1 → 3j+2` always flips the sign. -/
theorem agree_chi3Twin_three_mul_add_one (j : ℕ) : agree (chi3Twin ε) (3 * j + 1) = 0 := by
  rw [agree, succSign_chi3Twin_three_mul_add_one]; simp

/-- Exactly one of the steps `3j+2 → 3j+3 → 3j+4` keeps the sign. -/
theorem agree_chi3Twin_pair (j : ℕ) :
    agree (chi3Twin ε) (3 * j + 2) + agree (chi3Twin ε) (3 * j + 3) = 1 := by
  rw [agree, agree, succSign_chi3Twin_three_mul_add_two, succSign_chi3Twin_three_mul_add_three]
  rcases Int.units_eq_one_or (ε * chi3Twin ε (j + 1)) with h | h <;> simp [h]

theorem agreeCount_add_one (f : ℕ → ℤˣ) (N : ℕ) :
    agreeCount f (N + 1) = agreeCount f N + agree f (N + 1) := by
  rw [agreeCount, sum_Icc_succ_top (by omega), ← agreeCount]

/-- **Exact count.** The conductor-three twins keep their sign exactly once per period:
`A(3J+1) = J`. -/
theorem agreeCount_chi3Twin_three_mul_add_one (J : ℕ) :
    agreeCount (chi3Twin ε) (3 * J + 1) = J := by
  induction J with
  | zero => simpa [agreeCount] using agree_chi3Twin_three_mul_add_one ε 0
  | succ J ih =>
    have h1 := agree_chi3Twin_pair ε J
    have h2 := agree_chi3Twin_three_mul_add_one ε (J + 1)
    rw [show 3 * (J + 1) + 1 = 3 * J + 3 + 1 by omega, agreeCount_add_one,
      show 3 * J + 3 = 3 * J + 2 + 1 by omega, agreeCount_add_one, agreeCount_add_one,
      show 3 * J + 2 + 1 = 3 * J + 3 by omega, show 3 * J + 3 + 1 = 3 * (J + 1) + 1 by omega,
      show 3 * J + 1 + 1 = 3 * J + 2 by omega, ih, h2]
    omega

/-- `A(3J+2) = J + [ε f(J+1) = -1]`. -/
theorem agreeCount_chi3Twin_three_mul_add_two (J : ℕ) :
    agreeCount (chi3Twin ε) (3 * J + 2) =
      J + if ε * chi3Twin ε (J + 1) = -1 then 1 else 0 := by
  rw [show 3 * J + 2 = 3 * J + 1 + 1 by omega, agreeCount_add_one,
    agreeCount_chi3Twin_three_mul_add_one, show 3 * J + 1 + 1 = 3 * J + 2 by omega, agree,
    succSign_chi3Twin_three_mul_add_two]
  rcases Int.units_eq_one_or (ε * chi3Twin ε (J + 1)) with h | h <;> simp [h]

/-- `A(3J+3) = J + 1`. -/
theorem agreeCount_chi3Twin_three_mul_add_three (J : ℕ) :
    agreeCount (chi3Twin ε) (3 * J + 3) = J + 1 := by
  have h1 := agree_chi3Twin_pair ε J
  rw [show 3 * J + 3 = 3 * J + 1 + 1 + 1 by omega, agreeCount_add_one, agreeCount_add_one,
    agreeCount_chi3Twin_three_mul_add_one, show 3 * J + 1 + 1 = 3 * J + 2 by omega,
    show 3 * J + 2 + 1 = 3 * J + 3 by omega]
  omega

/-- The agreement count of a twin is `N/3` up to `+1/3` and `-2/3`. -/
theorem agreeCount_chi3Twin_bounds (N : ℕ) :
    N ≤ 3 * agreeCount (chi3Twin ε) N + 2 ∧ 3 * agreeCount (chi3Twin ε) N ≤ N + 1 := by
  obtain ⟨J, hJ⟩ : ∃ J, N = 3 * J + 1 ∨ N = 3 * J + 2 ∨ N = 3 * J + 3 ∨ N = 0 :=
    ⟨(N - 1) / 3, by omega⟩
  rcases hJ with rfl | rfl | rfl | rfl
  · rw [agreeCount_chi3Twin_three_mul_add_one]; omega
  · rw [agreeCount_chi3Twin_three_mul_add_two]; split_ifs <;> omega
  · rw [agreeCount_chi3Twin_three_mul_add_three]; omega
  · simp [agreeCount]

/-- **Zero doubling defect.** For the twins no `n` has `a(n) = a(2n) = 1`. -/
theorem agree_mul_agree_two_mul_chi3Twin {n : ℕ} (hn : 0 < n) :
    agree (chi3Twin ε) n * agree (chi3Twin ε) (2 * n) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, n = 3 * j ∨ n = 3 * j + 1 ∨ n = 3 * j + 2 := ⟨n / 3, by omega⟩
  rcases hj with rfl | rfl | rfl
  · have hj : 0 < j := by omega
    have s1 : succSign (chi3Twin ε) (3 * j) = ε * chi3Twin ε j := by
      rw [succSign, chi3Twin_three_mul ε hj, chi3Twin_three_mul_add_one, mul_one]
    have s2 : succSign (chi3Twin ε) (2 * (3 * j)) = -(ε * chi3Twin ε j) := by
      rw [succSign, show 2 * (3 * j) = 3 * (2 * j) by ring, chi3Twin_three_mul ε (by omega),
        chi3Twin_three_mul_add_one, mul_one, (chi3Twin ε).map_mul two_pos hj, chi3Twin_two,
        neg_one_mul, mul_neg]
    rw [agree, agree, s1, s2]
    rcases Int.units_eq_one_or (ε * chi3Twin ε j) with h | h <;> simp [h]
  · rw [agree_chi3Twin_three_mul_add_one, zero_mul]
  · rw [show 2 * (3 * j + 2) = 3 * (2 * j + 1) + 1 by ring, agree_chi3Twin_three_mul_add_one,
      mul_zero]

theorem doubleAgreeCount_chi3Twin (N : ℕ) : doubleAgreeCount (chi3Twin ε) N = 0 :=
  sum_eq_zero fun n hn => agree_mul_agree_two_mul_chi3Twin ε (by simp at hn; omega)

/-- **The twins attain the signed two-scale floor with equality at every scale.** -/
theorem signed_two_scale_identity_chi3Twin (N : ℕ) :
    succCorr (chi3Twin ε) (2 * N + 1) + succCorr (chi3Twin ε) N = -1 - N := by
  have h := signed_two_scale_identity (chi3Twin ε) N
  rw [doubleAgreeCount_chi3Twin, show (1 : ℕ) = 3 * 0 + 1 from rfl,
    succSign_chi3Twin_three_mul_add_one] at h
  push_cast at h
  linarith

theorem logAgree_add_one (f : ℕ → ℤˣ) (N : ℕ) :
    logAgree f (N + 1) = logAgree f N + (agree f (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  rw [logAgree, sum_Icc_succ_top (by omega), ← logAgree]

/-- The logarithmic agreement mass of a twin up to `3J+1`. -/
theorem logAgree_chi3Twin_three_mul_add_one_le (J : ℕ) :
    logAgree (chi3Twin ε) (3 * J + 1) ≤ (harmonic J : ℝ) / 3 + 1 / 3 - 1 / (3 * (J + 1)) := by
  induction J with
  | zero =>
    have := agree_chi3Twin_three_mul_add_one ε 0
    simp only [mul_zero, zero_add] at this
    simp [logAgree, this]
  | succ J ih =>
    have hpair := agree_chi3Twin_pair ε J
    have h0 := agree_chi3Twin_three_mul_add_one ε (J + 1)
    rw [show 3 * (J + 1) + 1 = 3 * J + 3 + 1 by omega, logAgree_add_one,
      show 3 * J + 3 = 3 * J + 2 + 1 by omega, logAgree_add_one,
      show 3 * J + 2 = 3 * J + 1 + 1 by omega, logAgree_add_one,
      show 3 * J + 1 + 1 + 1 + 1 = 3 * (J + 1) + 1 by omega, h0,
      show 3 * J + 1 + 1 + 1 = 3 * J + 3 by omega, show 3 * J + 1 + 1 = 3 * J + 2 by omega,
      harmonic_succ]
    have hpairR : (agree (chi3Twin ε) (3 * J + 2) : ℝ) + agree (chi3Twin ε) (3 * J + 3) = 1 := by
      exact_mod_cast hpair
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hb : (0 : ℝ) ≤ agree (chi3Twin ε) (3 * J + 3) := Nat.cast_nonneg _
    have e1 : (agree (chi3Twin ε) (3 * J + 2) : ℝ) / ((3 * J + 2 : ℕ) : ℝ) +
        (agree (chi3Twin ε) (3 * J + 3) : ℝ) / ((3 * J + 3 : ℕ) : ℝ) ≤ 1 / (3 * J + 2) := by
      push_cast
      have : (agree (chi3Twin ε) (3 * J + 3) : ℝ) / (3 * J + 3) ≤
          (agree (chi3Twin ε) (3 * J + 3) : ℝ) / (3 * J + 2) :=
        div_le_div_of_nonneg_left hb (by positivity) (by linarith)
      rw [← hpairR, add_div]
      linarith
    have e2 : (1 : ℝ) / (3 * J + 2) ≤
        2 / (3 * ((J : ℝ) + 1)) - 1 / (3 * ((J : ℝ) + 1 + 1)) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    have e3 : ((J : ℝ) + 1)⁻¹ / 3 = 1 / (3 * ((J : ℝ) + 1)) := by
      field_simp
    have e4 : (2 : ℝ) / (3 * ((J : ℝ) + 1)) = 1 / (3 * ((J : ℝ) + 1)) + 1 / (3 * ((J : ℝ) + 1)) := by
      ring
    push_cast at ih e1 ⊢
    simp only [zero_div, add_zero]
    rw [add_div, e3]
    linarith

/-- **Upper bound for the twins.** `Σ_{n ≤ M} a(n)/n ≤ (1/3) log M + 1`. -/
theorem logAgree_chi3Twin_le {M : ℕ} (hM : 0 < M) :
    logAgree (chi3Twin ε) M ≤ Real.log M / 3 + 1 := by
  set J := M / 3 + 1 with hJdef
  have hJ : 0 < J := by omega
  have hJM : J ≤ M := by omega
  have hmono := logAgree_mono (chi3Twin ε) (show M ≤ 3 * J + 1 by omega)
  have hb := logAgree_chi3Twin_three_mul_add_one_le ε J
  have hH := harmonic_le_one_add_log J
  have hlog : Real.log J ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast hJ) (by exact_mod_cast hJM)
  have : (0 : ℝ) ≤ 1 / (3 * ((J : ℝ) + 1)) := by positivity
  linarith

/-- **The one-third floor is sharp.** Every completely multiplicative sign has logarithmic
agreement mass at least `(1/3) log M − 1`, and the conductor-three twins have at most
`(1/3) log M + 1`. -/
theorem one_third_floor_sharp :
    (∀ f : CMSign, ∀ M : ℕ, 0 < M → Real.log M / 3 - 1 ≤ logAgree f M) ∧
      ∀ ε : ℤˣ, ∀ M : ℕ, 0 < M → logAgree (chi3Twin ε) M ≤ Real.log M / 3 + 1 :=
  ⟨fun f _ hM => one_third_log_floor f hM, fun ε _ hM => logAgree_chi3Twin_le ε hM⟩

theorem liouville_prime {p : ℕ} (hp : p.Prime) : CMSign.liouville p = -1 := by
  ext
  rw [CMSign.liouville_val hp.ne_zero, ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]
  simp

/-- The extremal twin with `ε = -1` agrees with the Liouville function at `2, 3, 5` and first
differs at `7`. -/
theorem chi3Twin_neg_one_vs_liouville :
    chi3Twin (-1) 2 = CMSign.liouville 2 ∧ chi3Twin (-1) 3 = CMSign.liouville 3 ∧
      chi3Twin (-1) 5 = CMSign.liouville 5 ∧ chi3Twin (-1) 7 ≠ CMSign.liouville 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chi3Twin_two, liouville_prime Nat.prime_two]
  · rw [chi3Twin_three, liouville_prime Nat.prime_three]
  · rw [show (5 : ℕ) = 3 * 1 + 2 from rfl, chi3Twin_three_mul_add_two,
      liouville_prime (by norm_num)]
  · rw [show (7 : ℕ) = 3 * 2 + 1 from rfl, chi3Twin_three_mul_add_one,
      liouville_prime (by norm_num)]
    decide

end GaloisForLFunctions.SignedSuccessorArithmetic
