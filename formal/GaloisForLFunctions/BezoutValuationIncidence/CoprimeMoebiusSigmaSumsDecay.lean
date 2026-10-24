import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Decay of coprime Möbius–divisor-sum sums

Write `w(n) = μ(n)/σ(n)`. The coprime partial sums `T_δ(Y) = Σ_{a ≤ Y, (a,δ)=1} w(a)` and the
coprime pair sum `S(X) = Σ_{a,b ≤ X, (a,b)=1} w(a) w(b)` decay logarithmically:

* `exists_abs_coprimeMoebiusSigmaSum_le`: `|T_δ(Y)| ≤ C δ^{1/4} (1 + log Y)^{-2}`;
* `exists_abs_coprimePairMoebiusSigmaSum_le`: `|S(X)| ≤ C (1 + log X)^{-4}`.

Mechanism. On arguments coprime to `δ`, `w = β_δ * (μ/id)` with the nonnegative multiplicative
kernel `β_δ(p^k) = p^{-k}` for `p ∣ δ` and `p^{-k}/(p+1)` for `p ∤ δ`
(`coprimeSigmaKernel_mul_moebiusHarmonicKernel`), so `T_δ(Y) = Σ_{d ≤ Y} β_δ(d) m(⌊Y/d⌋)` with
`m(N) = Σ_{n ≤ N} μ(n)/n = O(log^{-4} N)` (`RHTower.Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow`).
The Rankin mass `Σ_d β_δ(d) d^{1/4}` is a finite Euler product `≤ K δ^{1/4}`. The coprimality sieve
gives `S(X) = Σ_δ μ(δ) (w(δ) T_δ(X/δ))²`.
-/

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The weight `μ/σ` and its coprime sums -/

/-- `w(n) = μ(n)/σ(n)`. -/
def moebiusSigma (n : ℕ) : ℝ := (moebius n : ℝ) / (ArithmeticFunction.sigma 1 n : ℝ)

/-- `T_δ(Y) = Σ_{a ≤ Y, (a,δ)=1} μ(a)/σ(a)`. -/
def coprimeMoebiusSigmaSum (δ Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, if Nat.Coprime a δ then moebiusSigma a else 0

/-- `S(X) = Σ_{a,b ≤ X, (a,b)=1} w(a) w(b)`. -/
def coprimePairMoebiusSigmaSum (X : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, if Nat.Coprime a b then moebiusSigma a * moebiusSigma b else 0

theorem sigma_one_pos {n : ℕ} (hn : n ≠ 0) : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := by
  have : 0 < ArithmeticFunction.sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
      ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact_mod_cast this

theorem le_sigma_one (n : ℕ) : (n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : n ≤ ArithmeticFunction.sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d) (Nat.mem_divisors_self n hn.ne')
  exact_mod_cast this

theorem abs_moebiusSigma_le (n : ℕ) : |moebiusSigma n| ≤ (n : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [moebiusSigma]
  have hσ := sigma_one_pos hn.ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold moebiusSigma
  rw [abs_div, abs_of_pos hσ]
  have hμ : |(moebius n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  calc |(moebius n : ℝ)| / (ArithmeticFunction.sigma 1 n : ℝ)
      ≤ 1 / (ArithmeticFunction.sigma 1 n : ℝ) := div_le_div_of_nonneg_right hμ hσ.le
    _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn' (le_sigma_one n)
    _ = (n : ℝ)⁻¹ := one_div _

theorem moebiusSigma_mul {m n : ℕ} (h : Nat.Coprime m n) :
    moebiusSigma (m * n) = moebiusSigma m * moebiusSigma n := by
  unfold moebiusSigma
  rw [isMultiplicative_moebius.map_mul_of_coprime h,
    isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [mul_div_mul_comm]

/-- Multiples of `δ` sharing a prime with their cofactor are not squarefree. -/
theorem moebiusSigma_mul_of_not_coprime {δ a : ℕ} (h : ¬ Nat.Coprime a δ) :
    moebiusSigma (δ * a) = 0 := by
  obtain ⟨p, hp, hpa, hpδ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hsq : ¬ Squarefree (δ * a) := by
    intro hs
    have := hs p (Nat.mul_dvd_mul hpδ hpa)
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  simp [moebiusSigma, moebius_eq_zero_of_not_squarefree hsq]

/-! ### The kernel -/

/-- `β_δ(n) = n⁻¹ ∏_{p ∣ n, p ∤ δ} (p+1)⁻¹`. -/
def coprimeSigmaKernel (δ : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹ * ∏ p ∈ n.primeFactors \ δ.primeFactors, ((p : ℝ) + 1)⁻¹, by simp⟩

theorem coprimeSigmaKernel_apply (δ n : ℕ) :
    coprimeSigmaKernel δ n = (n : ℝ)⁻¹ * ∏ p ∈ n.primeFactors \ δ.primeFactors, ((p : ℝ) + 1)⁻¹ :=
  rfl

theorem coprimeSigmaKernel_nonneg (δ n : ℕ) : 0 ≤ coprimeSigmaKernel δ n := by
  rw [coprimeSigmaKernel_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (prod_nonneg fun p _ => inv_nonneg.mpr (by positivity))

theorem isMultiplicative_coprimeSigmaKernel (δ : ℕ) : (coprimeSigmaKernel δ).IsMultiplicative := by
  refine ⟨by simp [coprimeSigmaKernel], fun {m n} h => ?_⟩
  simp only [coprimeSigmaKernel_apply]
  rw [Nat.Coprime.primeFactors_mul h, union_sdiff_distrib,
    prod_union (Disjoint.mono sdiff_subset sdiff_subset (Nat.Coprime.disjoint_primeFactors h))]
  push_cast
  rw [mul_inv]
  ring

/-- `μ(n)/n`. -/
def moebiusHarmonicKernel : ArithmeticFunction ℝ :=
  ⟨fun n => (moebius n : ℝ) / n, by simp⟩

theorem moebiusHarmonicKernel_apply (n : ℕ) : moebiusHarmonicKernel n = (moebius n : ℝ) / n := rfl

theorem isMultiplicative_moebiusHarmonicKernel : moebiusHarmonicKernel.IsMultiplicative := by
  refine ⟨by simp [moebiusHarmonicKernel], fun {m n} h => ?_⟩
  simp only [moebiusHarmonicKernel_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  rw [mul_div_mul_comm]

/-- `w·1_{(·,δ)=1}`. -/
def coprimeMoebiusSigma (δ : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n δ then moebiusSigma n else 0, by simp [moebiusSigma]⟩

theorem coprimeMoebiusSigma_apply (δ n : ℕ) :
    coprimeMoebiusSigma δ n = if Nat.Coprime n δ then moebiusSigma n else 0 := rfl

theorem isMultiplicative_coprimeMoebiusSigma (δ : ℕ) : (coprimeMoebiusSigma δ).IsMultiplicative := by
  refine ⟨by simp [coprimeMoebiusSigma, moebiusSigma], fun {m n} h => ?_⟩
  rw [coprimeMoebiusSigma_apply, coprimeMoebiusSigma_apply, coprimeMoebiusSigma_apply]
  by_cases hm : Nat.Coprime m δ <;> by_cases hn : Nat.Coprime n δ
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, moebiusSigma_mul h]
  · rw [if_neg (fun hc => hn (Nat.Coprime.coprime_mul_left hc)), if_neg hn, mul_zero]
  · rw [if_neg (fun hc => hm (Nat.Coprime.coprime_mul_right hc)), if_neg hm, zero_mul]
  · rw [if_neg (fun hc => hm (Nat.Coprime.coprime_mul_right hc)), if_neg hm, zero_mul]

theorem coprimeSigmaKernel_prime_pow (δ : ℕ) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    coprimeSigmaKernel δ (p ^ k) =
      ((p : ℝ) ^ k)⁻¹ * (if p ∈ δ.primeFactors then 1 else ((p : ℝ) + 1)⁻¹) := by
  rw [coprimeSigmaKernel_apply, Nat.primeFactors_prime_pow hk hp]
  push_cast
  congr 1
  by_cases h : p ∈ δ.primeFactors
  · rw [if_pos h, show ({p} : Finset ℕ) \ δ.primeFactors = ∅ by simp [h], prod_empty]
  · rw [if_neg h, show ({p} : Finset ℕ) \ δ.primeFactors = {p} by simp [h], prod_singleton]

theorem moebiusHarmonicKernel_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    moebiusHarmonicKernel (p ^ k) =
      if k = 0 then 1 else if k = 1 then -(p : ℝ)⁻¹ else 0 := by
  rw [moebiusHarmonicKernel_apply]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [if_neg hk.ne', moebius_apply_prime_pow hp hk.ne']
  by_cases h1 : k = 1
  · subst h1; simp [div_eq_mul_inv]
  · simp [h1]

/-- **The kernel identity** `β_δ * (μ/id) = w·1_{(·,δ)=1}` for `δ ≠ 0`. -/
theorem coprimeSigmaKernel_mul_moebiusHarmonicKernel {δ : ℕ} (hδ : δ ≠ 0) :
    coprimeSigmaKernel δ * moebiusHarmonicKernel = coprimeMoebiusSigma δ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_coprimeSigmaKernel δ).mul isMultiplicative_moebiusHarmonicKernel) _
    (isMultiplicative_coprimeMoebiusSigma δ)).mpr ?_
  intro p k hp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => coprimeSigmaKernel δ x *
    moebiusHarmonicKernel y), Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ j ∈ range (k + 1), p ^ k / p ^ j = p ^ (k - j) := fun j hj =>
    Nat.pow_div (Nat.lt_succ_iff.mp (mem_range.mp hj)) hp.pos
  rw [sum_congr rfl fun j hj => by rw [hdiv j hj]]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coprimeMoebiusSigma_apply, moebiusSigma, moebiusHarmonicKernel_apply,
      coprimeSigmaKernel_apply]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ j ∈ range k, coprimeSigmaKernel δ (p ^ j) * moebiusHarmonicKernel (p ^ (k + 1 - j))
      = 0 := sum_eq_zero fun j hj => by
    have hj := mem_range.mp hj
    rw [moebiusHarmonicKernel_prime_pow hp, if_neg (by omega), if_neg (by omega), mul_zero]
  rw [hzero, zero_add, show k + 1 - k = 1 by omega, Nat.sub_self,
    moebiusHarmonicKernel_prime_pow hp, moebiusHarmonicKernel_prime_pow hp,
    if_neg one_ne_zero, if_pos rfl, if_pos rfl, mul_one,
    coprimeSigmaKernel_prime_pow δ hp (Nat.succ_ne_zero k), coprimeMoebiusSigma_apply]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcop : Nat.Coprime (p ^ (k + 1)) δ ↔ p ∉ δ.primeFactors := by
    rw [Nat.coprime_pow_left_iff (Nat.succ_pos k), Nat.Prime.coprime_iff_not_dvd hp,
      Nat.mem_primeFactors]
    simp [hp, hδ]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the prime itself
    simp only [zero_add, pow_one, pow_zero] at hcop ⊢
    simp only [coprimeSigmaKernel_apply, Nat.cast_one, inv_one, Nat.primeFactors_one,
      empty_sdiff, prod_empty, mul_one, one_mul]
    by_cases h : p ∈ δ.primeFactors
    · rw [if_pos h, if_neg (fun hc => hcop.mp hc h)]
      field_simp
      ring
    · rw [if_neg h, if_pos (hcop.mpr h)]
      have hσp : (ArithmeticFunction.sigma 1 p : ℝ) = p + 1 := by
        have h1 := sigma_one_apply_prime_pow (i := 1) hp
        rw [pow_one] at h1
        rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        push_cast
        ring
      unfold moebiusSigma
      rw [moebius_apply_prime hp, hσp]
      push_cast
      field_simp
      ring
  · rw [coprimeSigmaKernel_prime_pow δ hp hk1.ne']
    have hμ : moebiusSigma (p ^ (k + 1)) = 0 := by
      unfold moebiusSigma
      rw [moebius_apply_prime_pow hp (Nat.succ_ne_zero k), if_neg (by omega)]
      simp
    rw [hμ, ite_self]
    split_ifs <;> (rw [pow_succ]; field_simp; ring)

/-! ### The kernel representation of the coprime sums -/

/-- `m(N) = Σ_{n ≤ N} μ(n)/n`. -/
def moebiusHarmonicSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (moebius n : ℝ) / n

theorem coprimeMoebiusSigmaSum_eq_kernel {δ : ℕ} (hδ : δ ≠ 0) (Y : ℕ) :
    coprimeMoebiusSigmaSum δ Y =
      ∑ d ∈ Icc 1 Y, coprimeSigmaKernel δ d * moebiusHarmonicSum (Y / d) := by
  have h := RHTower.sum_Icc_mul_apply (coprimeSigmaKernel δ) moebiusHarmonicKernel Y
  rw [coprimeSigmaKernel_mul_moebiusHarmonicKernel hδ] at h
  simpa [coprimeMoebiusSigmaSum, moebiusHarmonicSum, coprimeMoebiusSigma_apply,
    moebiusHarmonicKernel_apply] using h

/-! ### Logarithmic weights -/

/-- `(1 + log x)² ≤ 64 x^{1/4}`. -/
theorem one_add_log_sq_le_rpow_quarter {x : ℝ} (hx : 1 ≤ x) : (1 + Real.log x) ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have he := Real.add_one_le_exp (Real.log x / 8)
  have hpow : Real.exp (Real.log x / 8) = x ^ (1 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  have h1 : 1 + Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by rw [← hpow]; linarith
  have h2 : (x ^ (1 / 8 : ℝ)) ^ 2 = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  calc (1 + Real.log x) ^ 2 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 2 := by gcongr
    _ = 64 * x ^ (1 / 4 : ℝ) := by rw [mul_pow, h2]; norm_num

/-- `(1 + log x)⁴ ≤ 16⁴ x^{1/4}`. -/
theorem one_add_log_pow_four_le_rpow_quarter {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 4 ≤ 65536 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have he := Real.add_one_le_exp (Real.log x / 16)
  have hpow : Real.exp (Real.log x / 16) = x ^ (1 / 16 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  have h1 : 1 + Real.log x ≤ 16 * x ^ (1 / 16 : ℝ) := by rw [← hpow]; linarith
  have h2 : (x ^ (1 / 16 : ℝ)) ^ 4 = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  calc (1 + Real.log x) ^ 4 ≤ (16 * x ^ (1 / 16 : ℝ)) ^ 4 := by gcongr
    _ = 65536 * x ^ (1 / 4 : ℝ) := by rw [mul_pow, h2]; norm_num

/-- Splitting a logarithm at a divisor: `1 + log Y ≤ 2 (1 + log ⌊Y/d⌋)(1 + log d)` for `1 ≤ d ≤ Y`. -/
theorem one_add_log_le_two_mul_log_div {Y d : ℕ} (hd : 1 ≤ d) (hdY : d ≤ Y) :
    1 + Real.log Y ≤ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) * (1 + Real.log d) := by
  have hq : 1 ≤ Y / d := (Nat.one_le_div_iff (by omega)).mpr hdY
  have hqR : (1 : ℝ) ≤ ((Y / d : ℕ) : ℝ) := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlt : Y < (Y / d + 1) * d := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
  have hle : (Y : ℝ) ≤ 2 * ((Y / d : ℕ) : ℝ) * d := by
    have : Y ≤ 2 * (Y / d) * d := by nlinarith
    exact_mod_cast this
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlog : Real.log Y ≤ Real.log 2 + Real.log ((Y / d : ℕ) : ℝ) + Real.log d := by
    rw [← Real.log_mul (by norm_num) (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log hY0 hle
  have hu := Real.log_nonneg hqR
  have hv := Real.log_nonneg hdR
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  nlinarith

/-! ### The Rankin mass of the kernel -/

/-- `β_δ(n) n^{1/4}`. -/
def coprimeSigmaKernelRankin (δ : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => coprimeSigmaKernel δ n * (n : ℝ) ^ (1 / 4 : ℝ), by simp⟩

theorem coprimeSigmaKernelRankin_apply (δ n : ℕ) :
    coprimeSigmaKernelRankin δ n = coprimeSigmaKernel δ n * (n : ℝ) ^ (1 / 4 : ℝ) := rfl

theorem coprimeSigmaKernelRankin_nonneg (δ n : ℕ) : 0 ≤ coprimeSigmaKernelRankin δ n :=
  mul_nonneg (coprimeSigmaKernel_nonneg δ n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem isMultiplicative_coprimeSigmaKernelRankin (δ : ℕ) :
    (coprimeSigmaKernelRankin δ).IsMultiplicative := by
  refine ⟨by simp [coprimeSigmaKernelRankin_apply, (isMultiplicative_coprimeSigmaKernel δ).map_one],
    fun {m n} h => ?_⟩
  simp only [coprimeSigmaKernelRankin_apply]
  rw [(isMultiplicative_coprimeSigmaKernel δ).map_mul_of_coprime h, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- `(x^k)⁻¹ (x^k)^{1/4} = (x^{-3/4})^k`. -/
theorem inv_pow_mul_rpow_quarter {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (x ^ k)⁻¹ * (x ^ k) ^ (1 / 4 : ℝ) = (x ^ (-(3 / 4 : ℝ))) ^ k := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_natCast (x ^ (-(3 / 4 : ℝ))) k,
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  ring_nf

/-- The local ratio `r_p = p^{-3/4}`. -/
abbrev rankinRatio (p : ℕ) : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))

/-- The local weight `c_p = 1` for `p ∣ δ`, `(p+1)⁻¹` otherwise. -/
abbrev rankinWeight (δ p : ℕ) : ℝ := if p ∈ δ.primeFactors then 1 else ((p : ℝ) + 1)⁻¹

theorem rankinRatio_nonneg (p : ℕ) : 0 ≤ rankinRatio p := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem rankinRatio_le {p : ℕ} (hp : p.Prime) : rankinRatio p ≤ 3 / 5 := by
  have h2 : rankinRatio p ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)
  have h4 : ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ 4 = 1 / 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h0 : 0 ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 5 := by
    rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0), h4]; norm_num
  linarith

theorem coprimeSigmaKernelRankin_prime_pow (δ : ℕ) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    coprimeSigmaKernelRankin δ (p ^ k) = rankinWeight δ p * rankinRatio p ^ k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [coprimeSigmaKernelRankin_apply, coprimeSigmaKernel_prime_pow δ hp hk, Nat.cast_pow]
  rw [show ((p : ℝ) ^ k)⁻¹ * rankinWeight δ p * ((p : ℝ) ^ k) ^ (1 / 4 : ℝ) =
    rankinWeight δ p * (((p : ℝ) ^ k)⁻¹ * ((p : ℝ) ^ k) ^ (1 / 4 : ℝ)) by ring,
    inv_pow_mul_rpow_quarter hpR]

/-- The local Euler factor `Σ_k β_δ(p^k) p^{k/4} = 1 + c_p r_p/(1 - r_p)`. -/
theorem hasSum_coprimeSigmaKernelRankin_prime_pow (δ : ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => coprimeSigmaKernelRankin δ (p ^ k))
      (1 + rankinWeight δ p * (rankinRatio p / (1 - rankinRatio p))) := by
  have hr1 : rankinRatio p < 1 := by have := rankinRatio_le hp; linarith
  have hg := (hasSum_geometric_of_lt_one (rankinRatio_nonneg p) hr1).mul_left
    (rankinWeight δ p * rankinRatio p)
  refine (hasSum_nat_add_iff' 1).mp ?_
  have e1 : (fun k => coprimeSigmaKernelRankin δ (p ^ (k + 1))) =
      fun i => rankinWeight δ p * rankinRatio p * rankinRatio p ^ i := by
    funext k
    rw [coprimeSigmaKernelRankin_prime_pow δ hp (Nat.succ_ne_zero k), pow_succ]
    ring
  have e2 : 1 + rankinWeight δ p * (rankinRatio p / (1 - rankinRatio p)) -
      ∑ i ∈ range 1, coprimeSigmaKernelRankin δ (p ^ i) =
      rankinWeight δ p * rankinRatio p * (1 - rankinRatio p)⁻¹ := by
    rw [sum_range_one, pow_zero, (isMultiplicative_coprimeSigmaKernelRankin δ).map_one]
    ring
  rw [e1, e2]
  exact hg

/-- Partial sums of the Rankin kernel are bounded by the finite Euler product. -/
theorem sum_Icc_coprimeSigmaKernelRankin_le_prod (δ Y : ℕ) :
    ∑ n ∈ Icc 1 Y, coprimeSigmaKernelRankin δ n ≤
      ∏ p ∈ range (Y + 1) with p.Prime,
        (1 + rankinWeight δ p * (rankinRatio p / (1 - rankinRatio p))) := by
  classical
  set f := coprimeSigmaKernelRankin δ
  have hm := isMultiplicative_coprimeSigmaKernelRankin δ
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖f (p ^ k)‖) := fun hp => by
    simp only [f, Real.norm_eq_abs]
    exact (hasSum_coprimeSigmaKernelRankin_prime_pow δ hp).summable.abs
  have hhas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n => f n) hm.map_one (fun h => hm.map_mul_of_coprime h) hnorm (range (Y + 1))).2
  have hsub : ∀ n ∈ Icc 1 Y, n ∈ Nat.factoredNumbers (range (Y + 1)) := by
    intro n hn
    rw [mem_Icc] at hn
    refine Nat.mem_factoredNumbers.mpr ⟨by omega, fun q hq => ?_⟩
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactorsList hq).trans hn.2))
  have hle : ∑ n ∈ Icc 1 Y, f n ≤ ∏ p ∈ range (Y + 1) with p.Prime, ∑' k : ℕ, f (p ^ k) := by
    rw [← sum_subtype_of_mem (fun n => f n) hsub]
    exact sum_le_hasSum _ (fun n _ => coprimeSigmaKernelRankin_nonneg δ n) hhas
  refine hle.trans (le_of_eq (prod_congr rfl fun p hp => ?_))
  exact (hasSum_coprimeSigmaKernelRankin_prime_pow δ (mem_filter.mp hp).2).tsum_eq

/-! ### Bounding the Euler factors -/

/-- The local factor: at most `(1 - r_p)⁻¹ (1 + 3p^{-7/4})` for `p ∣ δ`, `1 + 3p^{-7/4}` otherwise. -/
theorem localRankin_le (δ : ℕ) {p : ℕ} (hp : p.Prime) :
    1 + rankinWeight δ p * (rankinRatio p / (1 - rankinRatio p)) ≤
      (if p ∈ δ.primeFactors then (1 - rankinRatio p)⁻¹ else 1) *
        (1 + 3 * (p : ℝ) ^ (-(7 / 4 : ℝ))) := by
  have hr0 := rankinRatio_nonneg p
  have hr := rankinRatio_le hp
  have h1r : 0 < 1 - rankinRatio p := by linarith
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : 0 ≤ 3 * (p : ℝ) ^ (-(7 / 4 : ℝ)) := by positivity
  have h3 : (1 - rankinRatio p)⁻¹ ≤ 5 / 2 := by
    rw [inv_le_comm₀ h1r (by norm_num)]; norm_num; linarith
  by_cases h : p ∈ δ.primeFactors
  · simp only [rankinWeight, if_pos h, one_mul]
    have he : 1 + rankinRatio p / (1 - rankinRatio p) = (1 - rankinRatio p)⁻¹ := by
      field_simp; ring
    rw [he]
    have hinv : 0 ≤ (1 - rankinRatio p)⁻¹ := inv_nonneg.mpr h1r.le
    nlinarith
  · simp only [rankinWeight, if_neg h, one_mul]
    have hsplit : (p : ℝ) ^ (-(7 / 4 : ℝ)) = rankinRatio p * (p : ℝ)⁻¹ := by
      rw [rankinRatio, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
    rw [hsplit]
    have hpi : ((p : ℝ) + 1)⁻¹ ≤ (p : ℝ)⁻¹ := inv_anti₀ hp0 (by linarith)
    have hpi0 : 0 ≤ ((p : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
    have key : ((p : ℝ) + 1)⁻¹ * (rankinRatio p / (1 - rankinRatio p)) ≤
        3 * (rankinRatio p * (p : ℝ)⁻¹) := by
      rw [div_eq_mul_inv]
      calc ((p : ℝ) + 1)⁻¹ * (rankinRatio p * (1 - rankinRatio p)⁻¹)
          ≤ (p : ℝ)⁻¹ * (rankinRatio p * (5 / 2)) := by
            apply mul_le_mul hpi _ (mul_nonneg hr0 (inv_nonneg.mpr h1r.le)) hinv0
            exact mul_le_mul_of_nonneg_left h3 hr0
        _ ≤ 3 * (rankinRatio p * (p : ℝ)⁻¹) := by nlinarith
    linarith

/-- `(1 - p^{-3/4})⁻¹ ≤ p^{1/4}` for `p ≥ 5`, and `≤ 5/2` always. -/
theorem inv_one_sub_rankinRatio_le {p : ℕ} (hp : p.Prime) :
    (1 - rankinRatio p)⁻¹ ≤ (if p ≤ 3 then 5 / 2 else 1) * (p : ℝ) ^ (1 / 4 : ℝ) := by
  have hr := rankinRatio_le hp
  have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_nonneg p]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hx1 : 1 ≤ (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hpR (by norm_num)
  split_ifs with h3
  · have : (1 - rankinRatio p)⁻¹ ≤ 5 / 2 := by
      rw [inv_le_comm₀ h1r (by norm_num)]; norm_num; linarith
    nlinarith
  · have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast (show 5 ≤ p by omega)
    have hp0 : (0 : ℝ) < p := by linarith
    set x := (p : ℝ) ^ (1 / 4 : ℝ) with hx
    have hx0 : 0 < x := by positivity
    have hx4 : x ^ 4 = p := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    have hx3 : rankinRatio p = (x ^ 3)⁻¹ := by
      rw [rankinRatio, hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        ← Real.rpow_neg hp0.le]
      norm_num
    have hxge : 149 / 100 ≤ x := by
      by_contra hlt
      push Not at hlt
      have : x ^ 4 < (149 / 100) ^ 4 := pow_lt_pow_left₀ hlt hx0.le (by norm_num)
      nlinarith
    have hx2 : (x ^ 2)⁻¹ ≤ 49 / 100 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have hden : 0 < 1 - (x ^ 3)⁻¹ := by rw [← hx3]; exact h1r
    have key : 1 ≤ x * (1 - (x ^ 3)⁻¹) := by
      have : x * (1 - (x ^ 3)⁻¹) = x - (x ^ 2)⁻¹ := by field_simp
      rw [this]; linarith
    rw [one_mul, hx3, ← one_div, div_le_iff₀ hden]
    linarith

/-- A product of factors at least one over a superset is at least the product over the subset. -/
theorem prod_le_prod_of_subset_of_one_le_real {s t : Finset ℕ} (h : s ⊆ t) {g : ℕ → ℝ}
    (hg : ∀ i ∈ t, 1 ≤ g i) : ∏ i ∈ s, g i ≤ ∏ i ∈ t, g i := by
  rw [← prod_sdiff h]
  have h1 : 1 ≤ ∏ i ∈ t \ s, g i := by
    have := prod_le_prod (s := t \ s) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      (fun i hi => hg i (mem_sdiff.mp hi).1)
    simpa using this
  have h0 : 0 ≤ ∏ i ∈ s, g i := prod_nonneg fun i hi => zero_le_one.trans (hg i (h hi))
  exact le_mul_of_one_le_left h0 h1

theorem prod_inv_one_sub_rankinRatio_le {δ : ℕ} (hδ : δ ≠ 0) :
    ∏ p ∈ δ.primeFactors, (1 - rankinRatio p)⁻¹ ≤ 25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) := by
  have hle : ∏ p ∈ δ.primeFactors, (1 - rankinRatio p)⁻¹ ≤
      ∏ p ∈ δ.primeFactors, ((if p ≤ 3 then (5 / 2 : ℝ) else 1) * (p : ℝ) ^ (1 / 4 : ℝ)) :=
    prod_le_prod (fun p hp => inv_nonneg.mpr (by
        linarith [rankinRatio_le (Nat.prime_of_mem_primeFactors hp)]))
      fun p hp => inv_one_sub_rankinRatio_le (Nat.prime_of_mem_primeFactors hp)
  rw [prod_mul_distrib] at hle
  refine hle.trans ?_
  have hA : ∏ p ∈ δ.primeFactors, (if p ≤ 3 then (5 / 2 : ℝ) else 1) ≤ 25 / 4 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    have hcard : #(δ.primeFactors.filter (· ≤ 3)) ≤ 2 := by
      calc #(δ.primeFactors.filter (· ≤ 3)) ≤ #({2, 3} : Finset ℕ) := card_le_card fun p hp => by
            simp only [mem_filter] at hp
            have := (Nat.prime_of_mem_primeFactors hp.1).two_le
            simp only [mem_insert, mem_singleton]
            omega
        _ = 2 := rfl
    calc (5 / 2 : ℝ) ^ #(δ.primeFactors.filter (· ≤ 3)) ≤ (5 / 2) ^ 2 :=
          pow_le_pow_right₀ (by norm_num) hcard
      _ = 25 / 4 := by norm_num
  have hB : ∏ p ∈ δ.primeFactors, (p : ℝ) ^ (1 / 4 : ℝ) ≤ (δ : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    apply Real.rpow_le_rpow (prod_nonneg fun _ _ => Nat.cast_nonneg _) _ (by norm_num)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hδ) (Nat.prod_primeFactors_dvd δ)
    rw [← Nat.cast_prod]
    exact_mod_cast this
  have hB0 : 0 ≤ ∏ p ∈ δ.primeFactors, (p : ℝ) ^ (1 / 4 : ℝ) :=
    prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact mul_le_mul hA hB hB0 (by norm_num)

/-- `K = (25/4) exp(3 Σ n^{-7/4})`. -/
def kernelRankinConstant : ℝ := 25 / 4 * Real.exp (3 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ)))

/-- **Rankin mass of the kernel.** `Σ_{n ≤ Y} β_δ(n) n^{1/4} ≤ K δ^{1/4}`. -/
theorem sum_Icc_coprimeSigmaKernelRankin_le {δ : ℕ} (hδ : δ ≠ 0) (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, coprimeSigmaKernelRankin δ n ≤ kernelRankinConstant * (δ : ℝ) ^ (1 / 4 : ℝ) := by
  refine (sum_Icc_coprimeSigmaKernelRankin_le_prod δ Y).trans ?_
  set P := (range (Y + 1)).filter Nat.Prime
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(7 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h1 : ∏ p ∈ P, (1 + rankinWeight δ p * (rankinRatio p / (1 - rankinRatio p))) ≤
      ∏ p ∈ P, ((if p ∈ δ.primeFactors then (1 - rankinRatio p)⁻¹ else 1) *
        (1 + 3 * (p : ℝ) ^ (-(7 / 4 : ℝ)))) := by
    refine prod_le_prod (fun p hp => ?_) fun p hp => localRankin_le δ (mem_filter.mp hp).2
    have hp' := (mem_filter.mp hp).2
    have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp']
    have : 0 ≤ rankinWeight δ p := by unfold rankinWeight; split_ifs <;> positivity
    have : 0 ≤ rankinRatio p / (1 - rankinRatio p) := div_nonneg (rankinRatio_nonneg p) h1r.le
    positivity
  rw [prod_mul_distrib] at h1
  have h2 : ∏ p ∈ P, (if p ∈ δ.primeFactors then (1 - rankinRatio p)⁻¹ else 1) ≤
      25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) := by
    rw [prod_ite_mem]
    refine (prod_le_prod_of_subset_of_one_le_real inter_subset_right fun p hp => ?_).trans
      (prod_inv_one_sub_rankinRatio_le hδ)
    have hp' := Nat.prime_of_mem_primeFactors hp
    have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp']
    rw [le_inv_comm₀ zero_lt_one h1r, inv_one]
    linarith [rankinRatio_nonneg p]
  have h3 : ∏ p ∈ P, (1 + 3 * (p : ℝ) ^ (-(7 / 4 : ℝ))) ≤
      Real.exp (3 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
    calc ∏ p ∈ P, (1 + 3 * (p : ℝ) ^ (-(7 / 4 : ℝ)))
        ≤ ∏ p ∈ P, Real.exp (3 * (p : ℝ) ^ (-(7 / 4 : ℝ))) :=
          prod_le_prod (fun p _ => by positivity) fun p _ => by
            linarith [Real.add_one_le_exp (3 * (p : ℝ) ^ (-(7 / 4 : ℝ)))]
      _ = Real.exp (∑ p ∈ P, 3 * (p : ℝ) ^ (-(7 / 4 : ℝ))) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (3 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
          rw [Real.exp_le_exp, ← mul_sum]
          exact mul_le_mul_of_nonneg_left
            (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
  have hA0 : 0 ≤ ∏ p ∈ P, (if p ∈ δ.primeFactors then (1 - rankinRatio p)⁻¹ else 1) :=
    prod_nonneg fun p hp => by
      split_ifs
      · exact inv_nonneg.mpr (by linarith [rankinRatio_le (mem_filter.mp hp).2])
      · exact zero_le_one
  calc _ ≤ _ := h1
    _ ≤ (25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ)) * Real.exp (3 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) :=
        mul_le_mul h2 h3 (prod_nonneg fun p _ => by positivity) (by positivity)
    _ = kernelRankinConstant * (δ : ℝ) ^ (1 / 4 : ℝ) := by unfold kernelRankinConstant; ring

/-! ### Decay of the coprime sums -/

/-- Conditional on a log-power rate for `m`, `|T_δ(Y)| ≤ 256 C K δ^{1/4} (1 + log Y)^{-2}`. -/
theorem abs_coprimeMoebiusSigmaSum_le_of {C : ℝ}
    (hC : ∀ N : ℕ, 1 ≤ N → |moebiusHarmonicSum N| ≤ C / (1 + Real.log N) ^ 4)
    {δ : ℕ} (hδ : δ ≠ 0) {Y : ℕ} (hY : 1 ≤ Y) :
    |coprimeMoebiusSigmaSum δ Y| ≤
      256 * C * kernelRankinConstant * (δ : ℝ) ^ (1 / 4 : ℝ) / (1 + Real.log Y) ^ 2 := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hYR
  have hLY : 0 < (1 + Real.log Y) ^ 2 := by positivity
  rw [coprimeMoebiusSigmaSum_eq_kernel hδ]
  have hpt : ∀ d ∈ Icc 1 Y, |coprimeSigmaKernel δ d * moebiusHarmonicSum (Y / d)| ≤
      256 * C / (1 + Real.log Y) ^ 2 * coprimeSigmaKernelRankin δ d := by
    intro d hd
    obtain ⟨hd1, hdY⟩ := mem_Icc.mp hd
    have hq : 1 ≤ Y / d := (Nat.one_le_div_iff (by omega)).mpr hdY
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hqR : (1 : ℝ) ≤ ((Y / d : ℕ) : ℝ) := by exact_mod_cast hq
    have hlq : 0 ≤ Real.log ((Y / d : ℕ) : ℝ) := Real.log_nonneg hqR
    have hld : 0 ≤ Real.log d := Real.log_nonneg hdR
    have hsplit := one_add_log_le_two_mul_log_div hd1 hdY
    have hm := hC (Y / d) hq
    have hβ := coprimeSigmaKernel_nonneg δ d
    have hlog2 := one_add_log_sq_le_rpow_quarter hdR
    rw [abs_mul, abs_of_nonneg hβ, coprimeSigmaKernelRankin_apply]
    have hstep : C / (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 ≤
        4 * C * (1 + Real.log d) ^ 2 / (1 + Real.log Y) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hLY]
      have hA : (1 + Real.log Y) ^ 2 ≤
          4 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 2 * (1 + Real.log d) ^ 2 := by
        have h0 : 0 ≤ 1 + Real.log Y := by linarith
        nlinarith
      have hB : (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 2 ≤ (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 := by
        have : 1 ≤ (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 2 := by nlinarith
        nlinarith
      have hAB : (1 + Real.log Y) ^ 2 ≤
          4 * (1 + Real.log d) ^ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 :=
        calc (1 + Real.log Y) ^ 2
            ≤ 4 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 2 * (1 + Real.log d) ^ 2 := hA
          _ = 4 * (1 + Real.log d) ^ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 2 := by ring
          _ ≤ 4 * (1 + Real.log d) ^ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 :=
            mul_le_mul_of_nonneg_left hB (by positivity)
      calc C * (1 + Real.log Y) ^ 2
          ≤ C * (4 * (1 + Real.log d) ^ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4) :=
            mul_le_mul_of_nonneg_left hAB hC0
        _ = 4 * C * (1 + Real.log d) ^ 2 * (1 + Real.log ((Y / d : ℕ) : ℝ)) ^ 4 := by ring
    calc coprimeSigmaKernel δ d * |moebiusHarmonicSum (Y / d)|
        ≤ coprimeSigmaKernel δ d * (4 * C * (1 + Real.log d) ^ 2 / (1 + Real.log Y) ^ 2) :=
          mul_le_mul_of_nonneg_left (hm.trans hstep) hβ
      _ ≤ coprimeSigmaKernel δ d * (4 * C * (64 * (d : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log Y) ^ 2) := by
          gcongr
      _ = 256 * C / (1 + Real.log Y) ^ 2 * (coprimeSigmaKernel δ d * (d : ℝ) ^ (1 / 4 : ℝ)) := by
          ring
  calc |∑ d ∈ Icc 1 Y, coprimeSigmaKernel δ d * moebiusHarmonicSum (Y / d)|
      ≤ ∑ d ∈ Icc 1 Y, |coprimeSigmaKernel δ d * moebiusHarmonicSum (Y / d)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 Y, 256 * C / (1 + Real.log Y) ^ 2 * coprimeSigmaKernelRankin δ d :=
        sum_le_sum hpt
    _ = 256 * C / (1 + Real.log Y) ^ 2 * ∑ d ∈ Icc 1 Y, coprimeSigmaKernelRankin δ d := by
        rw [mul_sum]
    _ ≤ 256 * C / (1 + Real.log Y) ^ 2 * (kernelRankinConstant * (δ : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_coprimeSigmaKernelRankin_le hδ Y) (by positivity)
    _ = _ := by ring

/-! ### The coprime pair sum -/

theorem sum_divisors_moebius_real_eq_ite (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => ((f n : ℤ) : ℝ)) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  push_cast at h
  rw [h]

/-- Multiples of `δ` reindex the coprime sums: `Σ_{a ≤ X, δ ∣ a} w(a) = w(δ) T_δ(X/δ)`. -/
theorem sum_multiples_moebiusSigma {δ : ℕ} (hδ : 0 < δ) (X : ℕ) :
    ∑ a ∈ Icc 1 X, (if δ ∣ a then moebiusSigma a else 0) =
      moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ) := by
  have hbij : (Icc 1 X).filter (fun a => δ ∣ a) = (Icc 1 (X / δ)).image (fun j => δ * j) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hk1, hkX⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · omega
        · exact hj
      exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hδ).mpr (by linarith)⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjX⟩, rfl⟩
      have hle := (Nat.le_div_iff_mul_le hδ).mp hjX
      exact ⟨⟨Nat.mul_pos hδ hj1, by linarith⟩, dvd_mul_right δ j⟩
  rw [← sum_filter, hbij, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hδ h),
    coprimeMoebiusSigmaSum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hc : Nat.Coprime j δ
  · rw [if_pos hc, moebiusSigma_mul hc.symm]
  · rw [if_neg hc, mul_zero, moebiusSigma_mul_of_not_coprime hc]

/-- **The coprimality sieve.** `S(X) = Σ_{δ ≤ X} μ(δ) (w(δ) T_δ(X/δ))²`. -/
theorem coprimePairMoebiusSigmaSum_eq (X : ℕ) :
    coprimePairMoebiusSigmaSum X = ∑ δ ∈ Icc 1 X,
      (moebius δ : ℝ) * (moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ)) ^ 2 := by
  have hind : ∀ a ∈ Icc 1 X, ∀ b ∈ Icc 1 X, (if Nat.Coprime a b then (1 : ℝ) else 0) =
      ∑ δ ∈ Icc 1 X, if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0 := by
    intro a ha b hb
    obtain ⟨ha1, haX⟩ := mem_Icc.mp ha
    have hdiv : (Nat.gcd a b).divisors = (Icc 1 X).filter (fun δ => δ ∣ a ∧ δ ∣ b) := by
      ext δ
      simp only [Nat.mem_divisors, mem_filter, mem_Icc, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hda, hdb⟩, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hda (by omega), (Nat.le_of_dvd (by omega) hda).trans haX⟩,
          hda, hdb⟩
      · rintro ⟨-, hda, hdb⟩
        exact ⟨⟨hda, hdb⟩, Nat.gcd_ne_zero_left (by omega)⟩
    rw [← sum_filter, ← hdiv, sum_divisors_moebius_real_eq_ite]
  have hS : coprimePairMoebiusSigmaSum X = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ δ ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (moebiusSigma a * moebiusSigma b) := by
    unfold coprimePairMoebiusSigmaSum
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    rw [← sum_mul, ← hind a ha b hb]
    split_ifs <;> ring
  rw [hS]
  have hswap : ∀ a ∈ Icc 1 X, (∑ b ∈ Icc 1 X, ∑ δ ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (moebiusSigma a * moebiusSigma b)) =
      ∑ δ ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (moebiusSigma a * moebiusSigma b) :=
    fun a _ => sum_comm
  rw [sum_congr rfl hswap, sum_comm]
  refine sum_congr rfl fun δ hδ => ?_
  have hδ0 : 0 < δ := (mem_Icc.mp hδ).1
  set A : ℕ → ℝ := fun a => if δ ∣ a then moebiusSigma a else 0 with hA
  have hpt : ∀ a b : ℕ, (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) *
      (moebiusSigma a * moebiusSigma b) = (moebius δ : ℝ) * (A a * A b) := by
    intro a b
    simp only [hA]
    by_cases ha : δ ∣ a <;> by_cases hb : δ ∣ b <;> simp [ha, hb]
  calc ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (moebiusSigma a * moebiusSigma b)
      = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (moebius δ : ℝ) * (A a * A b) := by simp_rw [hpt]
    _ = (moebius δ : ℝ) * ((∑ a ∈ Icc 1 X, A a) * ∑ b ∈ Icc 1 X, A b) := by
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
    _ = _ := by
        rw [show (∑ a ∈ Icc 1 X, A a) = moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ) from
          sum_multiples_moebiusSigma hδ0 X, sq]

/-- `(x⁻¹)² (x^{1/4})³ = x^{-5/4}`. -/
theorem inv_sq_mul_rpow_quarter_cube {x : ℝ} (hx : 0 < x) :
    (x⁻¹) ^ 2 * (x ^ (1 / 4 : ℝ)) ^ 3 = x ^ (-(5 / 4 : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 3, ← Real.rpow_mul hx.le, inv_pow,
    ← Real.rpow_natCast x 2, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  norm_num

/-- Conditional on `|T_δ(Y)| ≤ C δ^{1/4} (1 + log Y)^{-2}`, the pair sum decays like
`(1 + log X)^{-4}`. -/
theorem abs_coprimePairMoebiusSigmaSum_le_of {C : ℝ}
    (hC : ∀ δ : ℕ, δ ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusSigmaSum δ Y| ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) / (1 + Real.log Y) ^ 2)
    {X : ℕ} (hX : 1 ≤ X) :
    |coprimePairMoebiusSigmaSum X| ≤
      16 * 65536 * C ^ 2 * (∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ))) / (1 + Real.log X) ^ 4 := by
  rw [coprimePairMoebiusSigmaSum_eq]
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlX := Real.log_nonneg hXR
  have hLX : 0 < (1 + Real.log X) ^ 4 := by positivity
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hpt : ∀ δ ∈ Icc 1 X,
      |(moebius δ : ℝ) * (moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ)) ^ 2| ≤
        16 * 65536 * C ^ 2 / (1 + Real.log X) ^ 4 * (δ : ℝ) ^ (-(5 / 4 : ℝ)) := by
    intro δ hδ
    obtain ⟨hδ1, hδX⟩ := mem_Icc.mp hδ
    have hq : 1 ≤ X / δ := (Nat.one_le_div_iff (by omega)).mpr hδX
    have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ1
    have hδ0 : (0 : ℝ) < δ := by linarith
    have hqR : (1 : ℝ) ≤ ((X / δ : ℕ) : ℝ) := by exact_mod_cast hq
    have hlq := Real.log_nonneg hqR
    have hlδ := Real.log_nonneg hδR
    set T := coprimeMoebiusSigmaSum δ (X / δ)
    set L := 1 + Real.log ((X / δ : ℕ) : ℝ)
    have hL : 1 ≤ L := by simp only [L]; linarith
    have hT := hC δ (by omega) (X / δ) hq
    have hT2 : T ^ 2 ≤ (C * (δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / L ^ 4 := by
      rw [← sq_abs]
      calc |T| ^ 2 ≤ (C * (δ : ℝ) ^ (1 / 4 : ℝ) / L ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hT 2
        _ = _ := by rw [div_pow, ← pow_mul]
    have hden : 1 / L ^ 4 ≤ 16 * (1 + Real.log δ) ^ 4 / (1 + Real.log X) ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) hLX]
      have h4 : (1 + Real.log X) ^ 4 ≤ (2 * L * (1 + Real.log δ)) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (one_add_log_le_two_mul_log_div hδ1 hδX) 4
      calc 1 * (1 + Real.log X) ^ 4 ≤ (2 * L * (1 + Real.log δ)) ^ 4 := by rw [one_mul]; exact h4
        _ = 16 * (1 + Real.log δ) ^ 4 * L ^ 4 := by ring
    have hl4 := one_add_log_pow_four_le_rpow_quarter hδR
    have hw2 : moebiusSigma δ ^ 2 ≤ ((δ : ℝ)⁻¹) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_moebiusSigma_le δ) 2
    have hμ : |(moebius δ : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hP : 0 ≤ (δ : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hδ0.le _
    have hT2' : T ^ 2 ≤ C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        (16 * (65536 * (δ : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log X) ^ 4) := by
      calc T ^ 2 ≤ (C * (δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / L ^ 4 := hT2
        _ = C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (1 / L ^ 4) := by ring
        _ ≤ C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (16 * (1 + Real.log δ) ^ 4 / (1 + Real.log X) ^ 4) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
            (16 * (65536 * (δ : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log X) ^ 4) := by gcongr
    rw [abs_mul, mul_pow, abs_of_nonneg (mul_nonneg (sq_nonneg (moebiusSigma δ)) (sq_nonneg T))]
    calc |(moebius δ : ℝ)| * (moebiusSigma δ ^ 2 * T ^ 2)
        ≤ 1 * (((δ : ℝ)⁻¹) ^ 2 * (C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
            (16 * (65536 * (δ : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log X) ^ 4))) := by
          apply mul_le_mul hμ _ (by positivity) zero_le_one
          exact mul_le_mul hw2 hT2' (sq_nonneg _) (sq_nonneg _)
      _ = 16 * 65536 * C ^ 2 / (1 + Real.log X) ^ 4 *
            (((δ : ℝ)⁻¹) ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 3) := by ring
      _ = _ := by rw [inv_sq_mul_rpow_quarter_cube hδ0]
  calc |∑ δ ∈ Icc 1 X, (moebius δ : ℝ) * (moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ)) ^ 2|
      ≤ ∑ δ ∈ Icc 1 X, |(moebius δ : ℝ) * (moebiusSigma δ * coprimeMoebiusSigmaSum δ (X / δ)) ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ δ ∈ Icc 1 X, 16 * 65536 * C ^ 2 / (1 + Real.log X) ^ 4 * (δ : ℝ) ^ (-(5 / 4 : ℝ)) :=
        sum_le_sum hpt
    _ = 16 * 65536 * C ^ 2 / (1 + Real.log X) ^ 4 * ∑ δ ∈ Icc 1 X, (δ : ℝ) ^ (-(5 / 4 : ℝ)) := by
        rw [mul_sum]
    _ ≤ 16 * 65536 * C ^ 2 / (1 + Real.log X) ^ 4 * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (by positivity)
    _ = _ := by ring

/-! ### Unconditional decay -/

theorem moebiusHarmonicSum_eq_deningerHarmonicPartial (N : ℕ) :
    moebiusHarmonicSum N = RHTower.deningerHarmonicPartial N := by
  have h : range (N + 1) = insert 0 (Icc 1 N) := by
    ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [moebiusHarmonicSum, RHTower.deningerHarmonicPartial, h, sum_insert (by simp)]
  simp

/-- The Möbius harmonic sums decay like `(1 + log N)^{-4}` uniformly in `N ≥ 1`. -/
theorem exists_abs_moebiusHarmonicSum_le :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |moebiusHarmonicSum N| ≤ C / (1 + Real.log N) ^ 4 := by
  obtain ⟨C0, hC0, hev⟩ :=
    RHTower.Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow 4 (by norm_num)
  obtain ⟨B, hB⟩ := RHTower.deningerHarmonicPartial_bounded
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 3))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨max (16 * C0) (B * (1 + Real.log N0) ^ 4), fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN := Real.log_nonneg hNR
  have hL : 0 < (1 + Real.log N) ^ 4 := by positivity
  rw [moebiusHarmonicSum_eq_deningerHarmonicPartial, le_div_iff₀ hL]
  by_cases hN' : N0 ≤ N
  · obtain ⟨h1, h3⟩ := hN0 N hN'
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have : (3 : ℝ) ≤ N := by exact_mod_cast h3
      linarith [Real.exp_one_lt_d9]
    have hl4 : 0 < Real.log N ^ 4 := by positivity
    rw [le_div_iff₀ hl4] at h1
    have h16 : (1 + Real.log N) ^ 4 ≤ 16 * Real.log N ^ 4 := by
      have : 1 + Real.log N ≤ 2 * Real.log N := by linarith
      calc (1 + Real.log N) ^ 4 ≤ (2 * Real.log N) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * Real.log N ^ 4 := by ring
    have hm0 := abs_nonneg (RHTower.deningerHarmonicPartial N)
    calc |RHTower.deningerHarmonicPartial N| * (1 + Real.log N) ^ 4
        ≤ |RHTower.deningerHarmonicPartial N| * (16 * Real.log N ^ 4) :=
          mul_le_mul_of_nonneg_left h16 hm0
      _ = 16 * (|RHTower.deningerHarmonicPartial N| * Real.log N ^ 4) := by ring
      _ ≤ 16 * C0 := by linarith
      _ ≤ _ := le_max_left _ _
  · have hNN : (N : ℝ) ≤ N0 := by exact_mod_cast (by omega : N ≤ N0)
    have hlog : Real.log N ≤ Real.log N0 := Real.log_le_log (by positivity) hNN
    have h4 : (1 + Real.log N) ^ 4 ≤ (1 + Real.log N0) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    calc |RHTower.deningerHarmonicPartial N| * (1 + Real.log N) ^ 4
        ≤ B * (1 + Real.log N0) ^ 4 := mul_le_mul (hB N) h4 hL.le hB0
      _ ≤ _ := le_max_right _ _

/-- **Coprime decay.** `|T_δ(Y)| ≤ C δ^{1/4} (1 + log Y)^{-2}` for all `δ, Y ≥ 1`. -/
theorem exists_abs_coprimeMoebiusSigmaSum_le :
    ∃ C : ℝ, ∀ δ : ℕ, δ ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusSigmaSum δ Y| ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) / (1 + Real.log Y) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_moebiusHarmonicSum_le
  exact ⟨256 * C * kernelRankinConstant, fun δ hδ Y hY => abs_coprimeMoebiusSigmaSum_le_of hC hδ hY⟩

/-- **Pair decay.** `|S(X)| ≤ C (1 + log X)^{-4}` for all `X ≥ 1`. -/
theorem exists_abs_coprimePairMoebiusSigmaSum_le :
    ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → |coprimePairMoebiusSigmaSum X| ≤ C / (1 + Real.log X) ^ 4 := by
  obtain ⟨C, hC⟩ := exists_abs_coprimeMoebiusSigmaSum_le
  exact ⟨16 * 65536 * C ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)),
    fun X hX => abs_coprimePairMoebiusSigmaSum_le_of hC hX⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
