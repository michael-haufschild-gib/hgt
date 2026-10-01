import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization
import GaloisForLFunctions.RHTower.Sieve.RoughPairSieve
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Selberg's weights for the twisted gcd form of the mollified mean square

The diagonal main term of the mollified mean square on `Re s = ½ − d` is the form
`Σ_{h,k ≤ N} a_h a_k (h,k)^{s₀}/(hk)`, `s₀ = 1 + 2d`.  Selberg's `Λ²` sieve with density
`ν(n) = n^{−s}` (`twistedSieve`) and level `N²` gives weights `γ` with `γ 1 = 1`, `|γ| ≤ 1`, support
in `[1, N]`, and main sum `1/S` with `S ≥ Σ_{m ≤ N} m^{−s}`.  With `a_h = γ_h h^{1−s}`:

* `twistedWeight_one`, `abs_twistedWeight_le` (`s ≥ 1`);
* `gcdForm_twistedWeight_le`: for `0 ≤ s₀ ≤ s`,
  `Σ_{h,k ≤ N} a_h a_k (h,k)^{s₀}/(hk) ≤ 1/Σ_{m ≤ N} m^{−s}`.

The exponents compare through the monotonicity of the kernel `g_s = μ ∗ n^s` in `s`
(`gcdPowKernel_mono`, `sum_gcd_rpow_div_mono`) and the diagonalisation
`sum_gcd_rpow_div_eq_kernel_diagonal`.  The weights, the main sum and the bounding-sum
estimate are mathlib's and PNT+'s Selberg sieve.
-/

open Finset ArithmeticFunction BoundingSieve

namespace RHTower.Sieve

noncomputable section

/-! ## Monotonicity of the gcd kernel in the exponent -/

theorem gcdPowKernel_prime_pow_eq_mul {s : ℝ} {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    gcdPowKernel s (p ^ k) = ((p : ℝ) ^ s) ^ (k - 1) * ((p : ℝ) ^ s - 1) := by
  rw [gcdPowKernel_prime_pow s hp hk]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  push_cast
  rw [Real.mul_rpow (pow_nonneg hp0 _) hp0, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hp0, ← Real.rpow_mul hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
  simp only [Nat.add_sub_cancel]
  ring

/-- `g_s(n) ≤ g_{s'}(n)` for `0 ≤ s ≤ s'`. -/
theorem gcdPowKernel_mono {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (n : ℕ) :
    gcdPowKernel s n ≤ gcdPowKernel s' n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [IsMultiplicative.multiplicative_factorization (gcdPowKernel s)
      (isMultiplicative_gcdPowKernel s) hn.ne',
    IsMultiplicative.multiplicative_factorization (gcdPowKernel s')
      (isMultiplicative_gcdPowKernel s') hn.ne']
  apply Finset.prod_le_prod
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    have hk : 1 ≤ n.factorization p := Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
    exact gcdPowKernel_prime_pow_nonneg hs hpp hk
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    have hk : 1 ≤ n.factorization p := Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero
    rw [gcdPowKernel_prime_pow_eq_mul hpp hk, gcdPowKernel_prime_pow_eq_mul hpp hk]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have h1 : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs
    have h2 : (p : ℝ) ^ s ≤ (p : ℝ) ^ s' := Real.rpow_le_rpow_of_exponent_le hp1 hss
    have h0 : (0 : ℝ) ≤ (p : ℝ) ^ s := by linarith
    exact mul_le_mul (pow_le_pow_left₀ h0 h2 _) (by linarith) (by linarith)
      (pow_nonneg (by linarith) _)

/-- **The gcd forms are monotone in the exponent.** -/
theorem sum_gcd_rpow_div_mono (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ) {s s' : ℝ}
    (hs : 0 ≤ s) (hss : s ≤ s') :
    ∑ p ∈ S ×ˢ S, a p.1 * a p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      ≤ ∑ p ∈ S ×ˢ S, a p.1 * a p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s' / ((p.1 : ℝ) * p.2) := by
  rw [sum_gcd_rpow_div_eq_kernel_diagonal S hS a s, sum_gcd_rpow_div_eq_kernel_diagonal S hS a s']
  exact Finset.sum_le_sum fun e _ =>
    mul_le_mul_of_nonneg_right (gcdPowKernel_mono hs hss e) (sq_nonneg _)

/-! ## The twisted Selberg sieve -/

theorem rpowArith_neg_pos {s : ℝ} {p : ℕ} (hp : p.Prime) : 0 < rpowArith (-s) p := by
  rw [rpowArith_apply_of_ne_zero _ hp.ne_zero]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

theorem rpowArith_neg_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ} (hp : p.Prime) :
    rpowArith (-s) p < 1 := by
  rw [rpowArith_apply_of_ne_zero _ hp.ne_zero]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- Selberg's sieve with density `ν(n) = n^{−s}`, sifting primes up to `N²`, level `N²`. -/
def twistedSieve {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) : SelbergSieve where
  support := ∅
  prodPrimes := rangePrimorial 1 (N ^ 2)
  prodPrimes_squarefree := rangePrimorial_squarefree 1 (N ^ 2)
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := rpowArith (-s)
  nu_mult := isMultiplicative_rpowArith (-s)
  nu_pos_of_prime := fun _ hp _ => rpowArith_neg_pos hp
  nu_lt_one_of_prime := fun _ hp _ => rpowArith_neg_lt_one hs hp
  level := (N : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith

/-- The twisted Selberg weight `a_h = γ_h h^{1−s}`. -/
def twistedWeight {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) (h : ℕ) : ℝ :=
  SelbergSieve.selbergWeights (twistedSieve hs hN) h * (h : ℝ) ^ (1 - s)

theorem twistedWeight_one {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    twistedWeight hs hN 1 = 1 := by
  rw [twistedWeight, SelbergSieve.weight_one_of_selberg, Nat.cast_one, Real.one_rpow, mul_one]

theorem abs_twistedWeight_le {s : ℝ} (hs : 1 ≤ s) {N : ℕ} (hN : 1 ≤ N) {h : ℕ} (hh : 1 ≤ h) :
    |twistedWeight (lt_of_lt_of_le one_pos hs) hN h| ≤ 1 := by
  rw [twistedWeight, abs_mul]
  have h1 := SelbergSieve.selberg_bound_weights (twistedSieve (lt_of_lt_of_le one_pos hs) hN) h
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h2 : (h : ℝ) ^ (1 - s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hh1 (by linarith)
  have h3 : 0 ≤ (h : ℝ) ^ (1 - s) := Real.rpow_nonneg (by linarith) _
  rw [abs_of_nonneg h3]
  calc |SelbergSieve.selbergWeights (twistedSieve (lt_of_lt_of_le one_pos hs) hN) h|
        * (h : ℝ) ^ (1 - s) ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
    _ = 1 := one_mul 1

theorem twistedWeight_eq_zero_of_lt {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) {h : ℕ}
    (hh : N < h) : twistedWeight hs hN h = 0 := by
  rw [twistedWeight, SelbergSieve.selbergWeights_eq_zero (twistedSieve hs hN) h, zero_mul]
  change ¬ ((h : ℝ) ^ 2 ≤ (N : ℝ) ^ 2)
  have : (N : ℝ) < h := by exact_mod_cast hh
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

theorem twistedWeight_eq_zero_of_not_dvd {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) {h : ℕ}
    (hh : ¬ h ∣ rangePrimorial 1 (N ^ 2)) : twistedWeight hs hN h = 0 := by
  rw [twistedWeight, SelbergSieve.selbergWeights_eq_zero_of_not_dvd (twistedSieve hs hN) hh,
    zero_mul]

/-- **The form at the sieve exponent is `1/S`.** -/
theorem gcdForm_twistedWeight_eq {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, twistedWeight hs hN p.1 * twistedWeight hs hN p.2
        * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2)
      = (SelbergSieve.selbergBoundingSum (twistedSieve hs hN))⁻¹ := by
  classical
  set σ := twistedSieve hs hN with hσ
  set P := rangePrimorial 1 (N ^ 2) with hP
  set γ := SelbergSieve.selbergWeights σ with hγ
  have hP0 : P ≠ 0 := (rangePrimorial_squarefree 1 (N ^ 2)).ne_zero
  -- the common support
  set T := (Icc 1 N).filter (· ∣ P) with hT
  have hsupp : ∀ d, γ d ≠ 0 → d ∈ T := by
    intro d hd
    have hdvd : d ∣ P := by
      by_contra h
      exact hd (SelbergSieve.selbergWeights_eq_zero_of_not_dvd σ h)
    have hdN : d ≤ N := by
      by_contra h
      apply hd
      refine SelbergSieve.selbergWeights_eq_zero σ d ?_
      change ¬ ((d : ℝ) ^ 2 ≤ (N : ℝ) ^ 2)
      have : (N : ℝ) < d := by exact_mod_cast (lt_of_not_ge h)
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h0 => by
      subst h0; exact hP0 (Nat.eq_zero_of_zero_dvd hdvd))
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, hdN⟩, hdvd⟩
  -- the summand in both forms
  set F : ℕ × ℕ → ℝ := fun p => γ p.1 * γ p.2 * (Nat.gcd p.1 p.2 : ℝ) ^ s
    * (((p.1 : ℝ) * p.2) ^ s)⁻¹ with hF
  have hF0 : ∀ p : ℕ × ℕ, p ∉ T ×ˢ T → F p = 0 := by
    intro p hp
    rw [mem_product, not_and_or] at hp
    rcases hp with h | h
    · have : γ p.1 = 0 := by by_contra h'; exact h (hsupp _ h')
      simp [hF, this]
    · have : γ p.2 = 0 := by by_contra h'; exact h (hsupp _ h')
      simp [hF, this]
  -- left side
  have hL : ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, twistedWeight hs hN p.1 * twistedWeight hs hN p.2
        * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2) = ∑ p ∈ T ×ˢ T, F p := by
    have hTsub : T ×ˢ T ⊆ Icc 1 N ×ˢ Icc 1 N :=
      product_subset_product (filter_subset _ _) (filter_subset _ _)
    have e1 : ∀ p ∈ Icc 1 N ×ˢ Icc 1 N, twistedWeight hs hN p.1 * twistedWeight hs hN p.2
        * (Nat.gcd p.1 p.2 : ℝ) ^ s / ((p.1 : ℝ) * p.2) = F p := by
      intro p hp
      obtain ⟨h1, h2⟩ := mem_product.mp hp
      have hp1 : (0 : ℝ) < p.1 := by exact_mod_cast (mem_Icc.mp h1).1
      have hp2 : (0 : ℝ) < p.2 := by exact_mod_cast (mem_Icc.mp h2).1
      simp only [hF, twistedWeight]
      rw [Real.mul_rpow hp1.le hp2.le, Real.rpow_sub hp1, Real.rpow_sub hp2, Real.rpow_one,
        Real.rpow_one]
      field_simp
    rw [Finset.sum_congr rfl e1]
    exact (Finset.sum_subset hTsub fun p _ hp => hF0 p hp).symm
  -- right side: PNT+'s main sum
  have hR : SelbergSieve.mainSum (s := σ.toBoundingSieve) (SelbergSieve.selbergMuPlus σ)
      = ∑ p ∈ T ×ˢ T, F p := by
    rw [SelbergSieve.selbergMuPlus, SelbergSieve.lambdaSquared_mainSum_eq_quad_form,
      ← Finset.sum_product']
    have hTsub : T ×ˢ T ⊆ P.divisors ×ˢ P.divisors := by
      refine product_subset_product ?_ ?_ <;>
      · intro d hd
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hP0⟩
    have e1 : ∀ p ∈ P.divisors ×ˢ P.divisors,
        σ.nu p.1 * γ p.1 * σ.nu p.2 * γ p.2 * (σ.nu (p.1.gcd p.2))⁻¹ = F p := by
      intro p hp
      obtain ⟨h1, h2⟩ := mem_product.mp hp
      have hp1 : p.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors h1)
      have hp2 : p.2 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors h2)
      have hg : p.1.gcd p.2 ≠ 0 := Nat.gcd_ne_zero_left hp1
      change rpowArith (-s) p.1 * γ p.1 * rpowArith (-s) p.2 * γ p.2
        * (rpowArith (-s) (p.1.gcd p.2))⁻¹ = F p
      rw [rpowArith_apply_of_ne_zero _ hp1, rpowArith_apply_of_ne_zero _ hp2,
        rpowArith_apply_of_ne_zero _ hg]
      have hp1' : (0 : ℝ) < p.1 := by exact_mod_cast Nat.pos_of_ne_zero hp1
      have hp2' : (0 : ℝ) < p.2 := by exact_mod_cast Nat.pos_of_ne_zero hp2
      have hg' : (0 : ℝ) < (p.1.gcd p.2 : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hg
      simp only [hF]
      rw [Real.rpow_neg hp1'.le, Real.rpow_neg hp2'.le, Real.rpow_neg hg'.le,
        Real.mul_rpow hp1'.le hp2'.le, inv_inv]
      ring
    rw [Finset.sum_congr rfl e1]
    exact (Finset.sum_subset hTsub fun p _ hp => hF0 p hp).symm
  rw [hL, ← hR]
  exact SelbergSieve.selberg_bound_simple_mainSum σ

/-- `S ≥ Σ_{m ≤ N} m^{−s}`. -/
theorem sum_rpow_neg_le_selbergBoundingSum {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Icc 1 N, (m : ℝ) ^ (-s) ≤ SelbergSieve.selbergBoundingSum (twistedSieve hs hN) := by
  have h := _root_.Sieve.selbergBoundingSum_ge_sum_div (twistedSieve hs hN) ?_ ?_ ?_ ?_
  · have hfl : Nat.floor (Real.sqrt (twistedSieve hs hN).level) = N := by
      change Nat.floor (Real.sqrt ((N : ℝ) ^ 2)) = N
      rw [Real.sqrt_sq (Nat.cast_nonneg _), Nat.floor_natCast]
    rw [hfl] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun m hm => ?_
    change (m : ℝ) ^ (-s) = rpowArith (-s) m
    rw [rpowArith_apply_of_ne_zero _ (by have := (mem_Icc.mp hm).1; omega)]
  · intro p hp hple
    change p ∣ rangePrimorial 1 (N ^ 2)
    apply Finset.dvd_prod_of_mem
    rw [rangePrimes, mem_filter, mem_Icc]
    refine ⟨⟨hp.two_le, ?_⟩, hp⟩
    change (p : ℝ) ≤ (N : ℝ) ^ 2 at hple
    exact_mod_cast hple
  · refine ⟨?_, fun a b => ?_⟩
    · change rpowArith (-s) 1 = 1
      rw [rpowArith_apply_of_ne_zero _ one_ne_zero, Nat.cast_one, Real.one_rpow]
    · change rpowArith (-s) (a * b) = rpowArith (-s) a * rpowArith (-s) b
      by_cases ha : a = 0
      · simp [ha, rpowArith_apply]
      by_cases hb : b = 0
      · simp [hb, rpowArith_apply]
      rw [rpowArith_apply_of_ne_zero _ (mul_ne_zero ha hb), rpowArith_apply_of_ne_zero _ ha,
        rpowArith_apply_of_ne_zero _ hb, Nat.cast_mul]
      exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    change 0 ≤ rpowArith (-s) n
    rw [rpowArith_apply]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · intro p hp _
    exact rpowArith_neg_lt_one hs hp

/-- **The twisted gcd form with Selberg's weights.**  For `1 ≤ s` and `0 ≤ s₀ ≤ s`,
`Σ_{h,k ≤ N} a_h a_k (h,k)^{s₀}/(hk) ≤ 1/Σ_{m ≤ N} m^{−s}`. -/
theorem gcdForm_twistedWeight_le {s s₀ : ℝ} (hs : 1 ≤ s) (hs₀ : 0 ≤ s₀) (hss : s₀ ≤ s)
    {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ Icc 1 N ×ˢ Icc 1 N,
        twistedWeight (lt_of_lt_of_le one_pos hs) hN p.1
          * twistedWeight (lt_of_lt_of_le one_pos hs) hN p.2
          * (Nat.gcd p.1 p.2 : ℝ) ^ s₀ / ((p.1 : ℝ) * p.2)
      ≤ 1 / ∑ m ∈ Icc 1 N, (m : ℝ) ^ (-s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hpos : ∀ m ∈ Icc 1 N, 0 < m := fun m hm => (mem_Icc.mp hm).1
  have hmono := sum_gcd_rpow_div_mono (Icc 1 N) hpos (twistedWeight hs0 hN) hs₀ hss
  rw [gcdForm_twistedWeight_eq hs0 hN] at hmono
  have hsum := sum_rpow_neg_le_selbergBoundingSum hs0 hN
  have hpos1 : 0 < ∑ m ∈ Icc 1 N, (m : ℝ) ^ (-s) := by
    have h1 : (1 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun m _ =>
      Real.rpow_nonneg (Nat.cast_nonneg m) _) h1)
    simp
  refine hmono.trans ?_
  rw [one_div]
  exact inv_anti₀ hpos1 hsum

end

end RHTower.Sieve
