import GaloisForLFunctions.RHTower.StepanovCharacterSum
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# Integrality produces linear counts

A **producer** is a construction that yields a one-sided count without assuming it. This module
records the two producers that exist and the precision each reaches, which is the gap the arithmetic
compressor of the programme has to close.

**Over `𝔽_q`: square-root precision for both parity classes** (`stepanov_parity_classes_upper`). For
`q = s²` odd and `h` squarefree, Stepanov's auxiliary polynomial bounds both Legendre parity classes
`{x : h(x)^{(q−1)/2} = ±1}` by `q/2 + (deg h + 1)√q`. The two classes are a curve and its quadratic
twist; the twist tower turns these upper counts into the Riemann hypothesis for the curve
(`unitary_iff_twistTower_upper`).

**Over `ℤ`: linear precision for the primes** (`sum_log_prime_Ioc_le`). The primes of `(n, 2n]` divide
`C(2n, n) ≤ 4^n`, so `Σ_{n<p≤2n} log p ≤ n log 4`: an integrality certificate gives an upper count for
the primes, a subset of the odd parity class, at relative precision `log 4` (summed dyadically this is
`Chebyshev.theta_le_log4_mul_x`). Integer polynomials on `[0, 1]` give the matching lower count
(`ArithmeticEffectivityTheory.log_inv_integral_le_psi`). The global law needs the odd class at
precision `x^{½+ε}` (`negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).

**One ledger for both rings.** Both producers are the same inequality: an auxiliary that vanishes to
order `m` on the counted set has size at least `m` times the counted mass.
* over `𝔽_q[X]` (`sum_le_natDegree_of_vanishing`): `Σ_{x∈T} m_x ≤ deg P`;
* over `ℤ` (`sum_mul_log_le_log_of_dvd`): `Σ_{p∈S} m_p log p ≤ log A`.
Stepanov's auxiliary has size `≈ ℓ q/2` and, through `x^q = x`, multiplicity `ℓ ≈ √q` at every counted
point, so the ledger divides out to `q/2 + O(√q)`. Chebyshev's auxiliary `C(2n, n)` has size `n log 4`
and multiplicity one on `(n, 2n]` (`sum_log_prime_Ioc_le`). Binomial auxiliaries cannot carry more:
`p^m ∣ C(N, k)` forces `p^m ≤ N` (`pow_le_of_dvd_choose`), so above `√N` every multiplicity is at most
one (`le_one_of_dvd_choose`). The producer problem over `ℤ` is an auxiliary integer of controlled size
whose multiplicity on the counted primes grows, as Frobenius makes Stepanov's grow.

**Divisibility sees prime powers, not parity.** Over `ℤ` an auxiliary "vanishes" at an integer `n`
when `n ∣ A`; vanishing on `S ⊆ [1, x]` is the single condition `lcm S ∣ A`, whose information
`log lcm S` is at most `ψ(x) = log lcm(1, …, x)` (`log_lcm_le_psi`). The odd Liouville class contains
every prime, so its information lies between `θ(x)` and `ψ(x)` (`theta_le_log_lcm_oddPoints`), which
differ by at most `2√x log x` (`abs_log_lcm_oddPoints_sub_theta_le`). At the square-root precision the
global law needs, vanishing at the primes, at the prime powers, and at one parity class are the same
divisibility condition: a producer that selects a parity class must vanish in a finer sense than
divisibility.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- **Stepanov's producer: both parity classes at square-root precision.** Over a finite field of
odd square order `q = s²`, for squarefree `h` of degree at most `s − 5`, each Legendre parity class
along `h` has at most `q/2 + (deg h + 1)√q` points. -/
theorem stepanov_parity_classes_upper {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    {p n : ℕ} [Fact p.Prime] [CharP E p] (hcard : Fintype.card E = p ^ n) {h : E[X]}
    (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree) {N s : ℕ} (hQ : p ^ n = 2 * N + 1)
    (hs : p ^ n = s ^ 2) (hsD : h.natDegree + 5 ≤ s) :
    2 * (univ.filter fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = 1).card ≤
        s ^ 2 + 2 * (h.natDegree + 1) * s ∧
      2 * (univ.filter fun x : E => h.eval x ≠ 0 ∧ h.eval x ^ N = -1).card ≤
        s ^ 2 + 2 * (h.natDegree + 1) * s :=
  ⟨RHTower.Stepanov.stepanov_bound hcard hsq hdeg hQ hs hsD 1,
    RHTower.Stepanov.stepanov_bound hcard hsq hdeg hQ hs hsD (-1)⟩

/-! ### The Bézout ledger -/

/-- **The ledger over a field.** A nonzero polynomial vanishing to order `m x` at every point `x` of
`T` has degree at least `Σ_{x∈T} m x`. -/
theorem sum_le_natDegree_of_vanishing {E : Type*} [Field E] {P : E[X]} (hP : P ≠ 0) (T : Finset E)
    (m : E → ℕ) (hvan : ∀ x ∈ T, (X - C x) ^ m x ∣ P) : ∑ x ∈ T, m x ≤ P.natDegree := by
  have hprod : (∏ x ∈ T, (X - C x) ^ m x) ∣ P :=
    Finset.prod_dvd_of_coprime (fun x _ y _ hxy =>
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow) hvan
  have hdeg : (∏ x ∈ T, (X - C x) ^ m x : E[X]).natDegree = ∑ x ∈ T, m x := by
    rw [natDegree_prod _ _ fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x)]
    simp [natDegree_pow]
  exact hdeg ▸ natDegree_le_of_dvd hprod hP

/-- **The ledger over `ℤ`.** A nonzero integer divisible by `p^{m p}` for every prime `p` of `S` has
`log A ≥ Σ_{p∈S} m p · log p`. -/
theorem sum_mul_log_le_log_of_dvd {A : ℕ} (hA : A ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (m : ℕ → ℕ) (hdvd : ∀ p ∈ S, p ^ m p ∣ A) :
    ∑ p ∈ S, (m p : ℝ) * Real.log p ≤ Real.log A := by
  have hprodZ : (∏ p ∈ S, (p : ℤ) ^ m p) ∣ (A : ℤ) :=
    Finset.prod_dvd_of_coprime (fun p hp q hq hpq =>
      (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)).pow)
      fun p hp => by exact_mod_cast hdvd p hp
  have hprod : (∏ p ∈ S, p ^ m p) ∣ A := by exact_mod_cast hprodZ
  have hle : ((∏ p ∈ S, p ^ m p : ℕ) : ℝ) ≤ A := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hA) hprod
  have hpos : ∀ p ∈ S, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hS p hp).pos
  push_cast at hle
  calc ∑ p ∈ S, (m p : ℝ) * Real.log p = Real.log (∏ p ∈ S, (p : ℝ) ^ m p) := by
        rw [Real.log_prod fun p hp => (pow_pos (hpos p hp) _).ne']
        exact sum_congr rfl fun p _ => (Real.log_pow _ _).symm
    _ ≤ Real.log A := Real.log_le_log (prod_pos fun p hp => pow_pos (hpos p hp) _) hle

/-- **Chebyshev's producer is a ledger.** Every prime of `(n, 2n]` divides `C(2n, n) ≤ 4^n`, so
`Σ_{n<p≤2n} log p ≤ n log 4`. -/
theorem sum_log_prime_Ioc_le (n : ℕ) :
    ∑ p ∈ (Ioc n (2 * n)).filter Nat.Prime, Real.log p ≤ n * Real.log 4 := by
  have h := sum_mul_log_le_log_of_dvd (Nat.centralBinom_ne_zero n)
    (S := (Ioc n (2 * n)).filter Nat.Prime) (fun p hp => (mem_filter.mp hp).2) (fun _ => 1) fun p hp => by
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      have h1 := (mem_Ioc.mp hpI).1
      have h2 := (mem_Ioc.mp hpI).2
      rw [pow_one, Nat.centralBinom_eq_two_mul_choose, two_mul]
      exact hpp.dvd_choose_add h1 h1 (by omega)
  simp only [Nat.cast_one, one_mul] at h
  refine h.trans ?_
  rw [← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast Nat.centralBinom_pos n)
    (by exact_mod_cast Nat.centralBinom_le_four_pow n)

/-- **Binomial multiplicities are capped.** If `p^m` divides `C(N, k)` with `k ≤ N`, then
`p^m ≤ N`. -/
theorem pow_le_of_dvd_choose {p N k m : ℕ} (hp : p.Prime) (hN : 0 < N) (hkN : k ≤ N)
    (hdvd : p ^ m ∣ N.choose k) : p ^ m ≤ N :=
  (Nat.pow_le_pow_right hp.pos
    ((hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkN).ne').mp hdvd)).trans
    (Nat.pow_factorization_choose_le hN)

/-- **Binomial auxiliaries vanish simply above the square root.** For a prime `p` with `N < p²`,
every power of `p` dividing `C(N, k)` is at most the first. -/
theorem le_one_of_dvd_choose {p N k m : ℕ} (hp : p.Prime) (hpN : N < p ^ 2) (hkN : k ≤ N)
    (hdvd : p ^ m ∣ N.choose k) : m ≤ 1 :=
  ((hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkN).ne').mp hdvd).trans
    (Nat.factorization_choose_le_one hpN)

/-! ### Divisibility sees prime powers, not parity -/

/-- The odd Liouville parity class in `[1, x]`. -/
def oddPoints (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => ArithmeticFunction.liouville n = -1

/-- **Vanishing at points of `[1, x]` carries at most `ψ(x)`.** An integer divisible by every point
of `S ⊆ [1, x]` is divisible by `lcm S`, and `log lcm S ≤ ψ(x)`. -/
theorem log_lcm_le_psi {S : Finset ℕ} {x : ℕ} (hS : S ⊆ Icc 1 x) :
    Real.log ((S.lcm id : ℕ) : ℝ) ≤ Chebyshev.psi x := by
  have hdvd : S.lcm id ∣ Nat.lcmUpto x := Finset.lcm_mono hS
  have hpos : 0 < S.lcm id :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero (Nat.lcmUpto_ne_zero x) hdvd)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  exact Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos x) hdvd)

/-- Every prime up to `x` lies in the odd parity class. -/
theorem primes_subset_oddPoints (x : ℕ) : (range (x + 1)).filter Nat.Prime ⊆ oddPoints x := by
  intro p hp
  obtain ⟨hpr, hpp⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.one_lt.le, Nat.lt_succ_iff.mp (mem_range.mp hpr)⟩, ?_⟩
  rw [ArithmeticFunction.liouville_apply hpp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hpp]
  norm_num

/-- **The divisibility information of the odd class.** `θ(x) ≤ log lcm(odd class ∩ [1, x]) ≤ ψ(x)`:
the primorial divides the lcm, which divides `lcm(1, …, x)`. -/
theorem theta_le_log_lcm_oddPoints (x : ℕ) :
    Chebyshev.theta x ≤ Real.log (((oddPoints x).lcm id : ℕ) : ℝ) ∧
      Real.log (((oddPoints x).lcm id : ℕ) : ℝ) ≤ Chebyshev.psi x := by
  refine ⟨?_, log_lcm_le_psi (filter_subset _ _)⟩
  have hprim : primorial x = ((range (x + 1)).filter Nat.Prime).lcm id := by
    have hcop : Set.Pairwise ((range (x + 1)).filter Nat.Prime : Set ℕ) (Nat.Coprime.onFun id) :=
      fun p hp q hq hpq => (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).mpr hpq
    rw [primorial, Finset.lcm_eq_prod hcop]
    rfl
  have hdvd : primorial x ∣ (oddPoints x).lcm id :=
    hprim ▸ Finset.lcm_mono (primes_subset_oddPoints x)
  have hup : (oddPoints x).lcm id ∣ Nat.lcmUpto x := Finset.lcm_mono (filter_subset _ _)
  have hpos : 0 < (oddPoints x).lcm id :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero (Nat.lcmUpto_ne_zero x) hup)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  exact Real.log_le_log (by exact_mod_cast primorial_pos x)
    (by exact_mod_cast Nat.le_of_dvd hpos hdvd)

/-- **Divisibility does not see parity.** At square-root precision, vanishing at the primes and at
the odd parity class are the same divisibility condition: their informations differ by at most
`2√x log x`. -/
theorem abs_log_lcm_oddPoints_sub_theta_le {x : ℕ} (hx : 1 ≤ x) :
    |Real.log (((oddPoints x).lcm id : ℕ) : ℝ) - Chebyshev.theta x| ≤ 2 * √x * Real.log x := by
  obtain ⟨h1, h2⟩ := theta_le_log_lcm_oddPoints x
  have := Chebyshev.psi_sub_theta_le (x := (x : ℝ)) (by exact_mod_cast hx)
  rw [abs_of_nonneg (by linarith)]
  linarith

end GaloisForLFunctions.ArithmeticKreinLangerTheory
