import GaloisForLFunctions.ArithmeticEffectivityTheory.TheIntersectionOfTorsionOrbits

/-!
# The different of a torsion orbit

The self-intersection of the torsion orbit `O_n` (the primitive `n`-th roots of unity) is
`I(n, n) = Σ_{ζ ≠ η ∈ O_n} log |ζ − η| = log |disc Φ_n|` (AET `orbitIntersection_self`). Per point it is
an adjunction formula: the degree `log n` minus the tame part of the ramification,

    I(n, n)/φ(n) = log n − Σ_{p ∣ n} log p/(p − 1) = Σ_{p^a ∥ n} (a − 1/(p − 1)) log p

(`selfIntersection_eq`, `selfIntersection_eq_sum_local`). The local term `(a − 1/(p − 1)) log p` is the
exponent of the different of `ℚ_p(ζ_{p^a})/ℚ_p` per unit degree: the self-intersection of a torsion
orbit is the canonical degree of its cyclotomic field, summed over the places.

The proof is the logarithmic derivation of Dirichlet convolution. `log` is a derivation
(`pmul_log_mul`); from `φ * ζ = id` and `μ * log = Λ`,
`μ * (id · log) = φ · log + φ * Λ` (`moebius_mul_id_pmul_log`), and `(φ * Λ)(n) = φ(n) Σ_{p ∣ n} log p/(p − 1)`
(`totient_mul_vonMangoldt_eq`), since `Λ` lives on prime powers and `Σ_{j < k} φ(p^j) = p^{k−1}`.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### The logarithmic derivation -/

/-- **`log` is a derivation of Dirichlet convolution**: `(f * g)·log = (f·log) * g + f * (g·log)`. -/
theorem pmul_log_mul (f g : ArithmeticFunction ℝ) :
    (f * g).pmul log = f.pmul log * g + f * g.pmul log := by
  ext n
  simp only [pmul_apply, mul_apply, add_apply, log_apply, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hmul, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul (hmul.symm ▸ hn)
  have h2 : (x.2 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul (hmul.symm ▸ hn)
  rw [← hmul, Nat.cast_mul, Real.log_mul h1 h2]
  ring

/-- Euler's totient as a real arithmetic function. -/
def totientFn : ArithmeticFunction ℝ := ⟨fun n => (Nat.totient n : ℝ), by simp⟩

/-- The identity `n ↦ n` as a real arithmetic function. -/
def idFn : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ), by simp⟩

@[simp] theorem totientFn_apply (n : ℕ) : totientFn n = Nat.totient n := rfl

@[simp] theorem idFn_apply (n : ℕ) : idFn n = n := rfl

/-- `Σ_{d ∣ n} φ(d) = n`. -/
theorem totientFn_mul_zeta : totientFn * (ζ : ArithmeticFunction ℝ) = idFn := by
  ext n
  rw [coe_mul_zeta_apply]
  simp only [totientFn_apply, idFn_apply]
  exact_mod_cast Nat.sum_totient n

theorem zeta_pmul_log : (ζ : ArithmeticFunction ℝ).pmul log = log := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [pmul_apply, natCoe_apply, zeta_apply, hn]

/-- **`μ * (id · log) = φ · log + φ * Λ`.** -/
theorem moebius_mul_id_pmul_log :
    (μ : ArithmeticFunction ℝ) * idFn.pmul log = totientFn.pmul log + totientFn * Λ := by
  rw [← totientFn_mul_zeta, pmul_log_mul, zeta_pmul_log, mul_add, mul_left_comm,
    coe_moebius_mul_coe_zeta, mul_one, mul_left_comm, moebius_mul_log_eq_vonMangoldt]

/-- The Möbius transform of `k log k` is `φ(n) log n + Σ_{d ∣ n} φ(n/d) Λ(d)`. -/
theorem kLogKernel_eq (n : ℕ) :
    kLogKernel n = Nat.totient n * Real.log n +
      ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℝ) * Λ d := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) moebius_mul_id_pmul_log
  simp only [mul_apply, add_apply, pmul_apply, totientFn_apply, idFn_apply, log_apply,
    intCoe_apply] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => ((μ a : ℤ) : ℝ) * ((b : ℝ) * Real.log b)),
    Nat.sum_divisorsAntidiagonal' (fun a b => (Nat.totient a : ℝ) * Λ b)] at h
  rw [kLogKernel, h]

/-! ### The tame part of the ramification -/

/-- The tame part of the different per unit degree: `Σ_{p ∣ n} log p/(p − 1)`. -/
def tameDifferent (n : ℕ) : ℝ := ∑ p ∈ n.primeFactors, Real.log p / ((p : ℝ) - 1)

theorem tameDifferent_mul {a b : ℕ} (hab : a.Coprime b) :
    tameDifferent (a * b) = tameDifferent a + tameDifferent b := by
  rw [tameDifferent, hab.primeFactors_mul, sum_union hab.disjoint_primeFactors]
  rfl

theorem tameDifferent_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    tameDifferent (p ^ k) = Real.log p / ((p : ℝ) - 1) := by
  rw [tameDifferent, Nat.primeFactors_prime_pow hk hp, sum_singleton]

/-- `Σ_{j < k} φ(p^j) = p^{k−1}` for `k ≥ 1`. -/
theorem sum_range_totient_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ∑ j ∈ range k, (Nat.totient (p ^ j) : ℝ) = (p : ℝ) ^ (k - 1) := by
  have h := Nat.sum_totient (p ^ (k - 1))
  rw [Nat.sum_divisors_prime_pow hp, Nat.sub_add_cancel hk] at h
  exact_mod_cast h

/-- **`(φ * Λ)(n) = φ(n) Σ_{p ∣ n} log p/(p − 1)`.** -/
theorem totient_mul_vonMangoldt_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℝ) * Λ d = Nat.totient n * tameDifferent n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [tameDifferent]
  | one => simp [tameDifferent]
  | prime_pow p k hp hk =>
    rw [Nat.sum_divisors_prime_pow hp, sum_range_succ', tameDifferent_prime_pow hp hk.ne']
    simp only [pow_zero, vonMangoldt_apply_one, mul_zero, add_zero]
    have hΛ : ∀ j ∈ range k, (Nat.totient (p ^ k / p ^ (j + 1)) : ℝ) * Λ (p ^ (j + 1)) =
        (Nat.totient (p ^ (k - 1 - j)) : ℝ) * Real.log p := by
      intro j hj
      have hjk : j + 1 ≤ k := mem_range.mp hj
      rw [Nat.pow_div hjk hp.pos, vonMangoldt_apply_pow (Nat.succ_ne_zero j),
        vonMangoldt_apply_prime hp, show k - (j + 1) = k - 1 - j by omega]
    rw [sum_congr rfl hΛ, ← sum_mul, sum_range_reflect (fun j => (Nat.totient (p ^ j) : ℝ)) k,
      sum_range_totient_prime_pow hp hk, Nat.totient_prime_pow hp hk]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    push_cast
    rw [Nat.cast_sub hp.one_le]
    field_simp
    push_cast
    ring
  | coprime a b ha hb hab iha ihb =>
    have hfilter : ∀ m : ℕ, ∑ d ∈ m.divisors, (Nat.totient (m / d) : ℝ) * Λ d =
        ∑ d ∈ m.divisors with IsPrimePow d, (Nat.totient (m / d) : ℝ) * Λ d := by
      intro m
      rw [sum_filter]
      refine sum_congr rfl fun d _ => ?_
      split_ifs with h
      · rfl
      · rw [vonMangoldt_apply, if_neg h, mul_zero]
    rw [hfilter, Nat.mul_divisors_filter_prime_pow hab, filter_union,
      sum_union (Nat.disjoint_divisors_filter_isPrimePow hab)]
    have hA : ∀ d ∈ a.divisors with IsPrimePow d, (Nat.totient (a * b / d) : ℝ) * Λ d =
        Nat.totient b * ((Nat.totient (a / d) : ℝ) * Λ d) := by
      intro d hd
      have hda : d ∣ a := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      rw [Nat.mul_comm a b, Nat.mul_div_assoc b hda, Nat.mul_comm b,
        Nat.totient_mul (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hda))]
      push_cast; ring
    have hB : ∀ d ∈ b.divisors with IsPrimePow d, (Nat.totient (a * b / d) : ℝ) * Λ d =
        Nat.totient a * ((Nat.totient (b / d) : ℝ) * Λ d) := by
      intro d hd
      have hdb : d ∣ b := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
      rw [Nat.mul_div_assoc a hdb,
        Nat.totient_mul (hab.coprime_dvd_right (Nat.div_dvd_of_dvd hdb))]
      push_cast; ring
    rw [sum_congr rfl hA, sum_congr rfl hB, ← mul_sum, ← mul_sum, ← hfilter, ← hfilter, iha, ihb,
      tameDifferent_mul hab, Nat.totient_mul hab]
    push_cast; ring

/-! ### The self-intersection -/

/-- The **self-intersection per point** of the torsion orbit `O_n`: `I(n, n)/φ(n)`. -/
def selfIntersection (n : ℕ) : ℝ := orbitIntersection n n / Nat.totient n

/-- **Adjunction for torsion orbits**: `I(n, n)/φ(n) = log n − Σ_{p ∣ n} log p/(p − 1)`. -/
theorem selfIntersection_eq {n : ℕ} (hn : 0 < n) :
    selfIntersection n = Real.log n - tameDifferent n := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  rw [selfIntersection, orbitIntersection_self hn, kLogKernel_eq, totient_mul_vonMangoldt_eq]
  field_simp
  ring

/-- **The local form of adjunction**: `I(n, n)/φ(n) = Σ_{p^a ∥ n} (a − 1/(p − 1)) log p`, the different
of `ℚ(ζ_n)` per unit degree, place by place. -/
theorem selfIntersection_eq_sum_local {n : ℕ} (hn : 0 < n) :
    selfIntersection n =
      ∑ p ∈ n.primeFactors, ((n.factorization p : ℝ) - 1 / ((p : ℝ) - 1)) * Real.log p := by
  rw [selfIntersection_eq hn, Real.log_nat_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, tameDifferent, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- Each local term of the self-intersection is nonnegative, so `I(n, n) ≥ 0`. -/
theorem selfIntersection_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ selfIntersection n := by
  rw [selfIntersection_eq_sum_local hn]
  refine sum_nonneg fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hv : (1 : ℝ) ≤ n.factorization p := by
    exact_mod_cast (hpp.dvd_iff_one_le_factorization hn.ne').mp (Nat.dvd_of_mem_primeFactors hp)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))

end GaloisForLFunctions.ArithmeticIntersectionTheory
