import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMoebiusSigmaSumsDecay

/-!
# Decay of coprime Möbius harmonic sums

For `f ≥ 1` let `m_f(Y) = Σ_{a ≤ Y, (a,f)=1} μ(a)/a` and, for `g ≥ 1`,
`S'_g(X) = Σ_{a,b ≤ X, (a,b)=1, (ab,g)=1} μ(a)μ(b)/(ab)`. With the Rankin product
`Π(f) = ∏_{p ∣ f} (1 - p^{-3/4})^{-1}`:

* `exists_abs_coprimeMoebiusHarmonicSum_le`: `|m_f(Y)| ≤ C Π(f) (1 + log Y)^{-2}`;
* `exists_abs_coprimePairMoebiusHarmonicSum_le`: `|S'_g(X)| ≤ C Π(g)² (1 + log X)^{-4}`;
* `exists_sum_rankinProduct_sq_div_le`: `Σ_{g ≤ N} μ(g)² Π(g)²/g ≤ C (1 + log N)`.

Mechanism. `μ/id · 1_{(·,f)=1} = κ_f * (μ/id)` with `κ_f(k) = 1/k` on integers whose primes divide
`f` (`smoothHarmonicKernel_mul_moebiusHarmonicKernel`); the Rankin mass of `κ_f` is exactly the
Euler product `Π(f)`. The coprimality sieve writes `S'_g(X) = Σ_{(δ,g)=1} μ(δ)(μ(δ) m_{δg}(X/δ)/δ)²`.
On squarefree `g`, `Π(g)² = Σ_{d ∣ g} h(d)` with `h(p) = (1-p^{-3/4})^{-2} - 1 = O(p^{-3/4})`, so
`Π²` has bounded harmonic mean.
-/

open Finset Filter Topology ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The smooth kernel -/

/-- `κ_f(k) = 1/k` if every prime factor of `k` divides `f`, else `0`. -/
def smoothHarmonicKernel (f : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k.primeFactors ⊆ f.primeFactors then (k : ℝ)⁻¹ else 0, by simp⟩

theorem smoothHarmonicKernel_apply (f k : ℕ) :
    smoothHarmonicKernel f k = if k.primeFactors ⊆ f.primeFactors then (k : ℝ)⁻¹ else 0 := rfl

theorem smoothHarmonicKernel_nonneg (f k : ℕ) : 0 ≤ smoothHarmonicKernel f k := by
  rw [smoothHarmonicKernel_apply]; split_ifs <;> positivity

theorem isMultiplicative_smoothHarmonicKernel (f : ℕ) :
    (smoothHarmonicKernel f).IsMultiplicative := by
  refine ⟨by simp [smoothHarmonicKernel_apply], fun {m n} h => ?_⟩
  simp only [smoothHarmonicKernel_apply]
  rw [Nat.Coprime.primeFactors_mul h, union_subset_iff]
  by_cases hm : m.primeFactors ⊆ f.primeFactors <;> by_cases hn : n.primeFactors ⊆ f.primeFactors
  · rw [if_pos ⟨hm, hn⟩, if_pos hm, if_pos hn]; push_cast; rw [mul_inv]
  · rw [if_neg (fun h' => hn h'.2), if_neg hn, mul_zero]
  · rw [if_neg (fun h' => hm h'.1), if_neg hm, zero_mul]
  · rw [if_neg (fun h' => hm h'.1), if_neg hm, zero_mul]

theorem smoothHarmonicKernel_prime_pow (f : ℕ) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    smoothHarmonicKernel f (p ^ k) = if p ∈ f.primeFactors then ((p : ℝ) ^ k)⁻¹ else 0 := by
  rw [smoothHarmonicKernel_apply, Nat.primeFactors_prime_pow hk hp, singleton_subset_iff]
  push_cast
  rfl

/-- `μ/id · 1_{(·,f)=1}`. -/
def coprimeMoebiusHarmonic (f : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n f then (moebius n : ℝ) / n else 0, by simp⟩

theorem coprimeMoebiusHarmonic_apply (f n : ℕ) :
    coprimeMoebiusHarmonic f n = if Nat.Coprime n f then (moebius n : ℝ) / n else 0 := rfl

theorem isMultiplicative_coprimeMoebiusHarmonic (f : ℕ) :
    (coprimeMoebiusHarmonic f).IsMultiplicative := by
  refine ⟨by simp [coprimeMoebiusHarmonic_apply], fun {m n} h => ?_⟩
  have hk := isMultiplicative_moebiusHarmonicKernel.map_mul_of_coprime h
  simp only [moebiusHarmonicKernel_apply] at hk
  rw [coprimeMoebiusHarmonic_apply, coprimeMoebiusHarmonic_apply, coprimeMoebiusHarmonic_apply]
  by_cases hm : Nat.Coprime m f <;> by_cases hn : Nat.Coprime n f
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, hk]
  · rw [if_neg (fun hc => hn (Nat.Coprime.coprime_mul_left hc)), if_neg hn, mul_zero]
  · rw [if_neg (fun hc => hm (Nat.Coprime.coprime_mul_right hc)), if_neg hm, zero_mul]
  · rw [if_neg (fun hc => hm (Nat.Coprime.coprime_mul_right hc)), if_neg hm, zero_mul]

/-- **The smooth kernel identity** `κ_f * (μ/id) = μ/id · 1_{(·,f)=1}` for `f ≠ 0`. -/
theorem smoothHarmonicKernel_mul_moebiusHarmonicKernel {f : ℕ} (hf : f ≠ 0) :
    smoothHarmonicKernel f * moebiusHarmonicKernel = coprimeMoebiusHarmonic f := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_smoothHarmonicKernel f).mul isMultiplicative_moebiusHarmonicKernel) _
    (isMultiplicative_coprimeMoebiusHarmonic f)).mpr ?_
  intro p k hp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => smoothHarmonicKernel f x *
    moebiusHarmonicKernel y), Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hdiv : ∀ j ∈ range (k + 1), p ^ k / p ^ j = p ^ (k - j) := fun j hj =>
    Nat.pow_div (Nat.lt_succ_iff.mp (mem_range.mp hj)) hp.pos
  rw [sum_congr rfl fun j hj => by rw [hdiv j hj]]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coprimeMoebiusHarmonic_apply, moebiusHarmonicKernel_apply, smoothHarmonicKernel_apply]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ j ∈ range k, smoothHarmonicKernel f (p ^ j) *
      moebiusHarmonicKernel (p ^ (k + 1 - j)) = 0 := sum_eq_zero fun j hj => by
    have hj := mem_range.mp hj
    rw [moebiusHarmonicKernel_prime_pow hp, if_neg (by omega), if_neg (by omega), mul_zero]
  rw [hzero, zero_add, show k + 1 - k = 1 by omega, Nat.sub_self,
    moebiusHarmonicKernel_prime_pow hp, moebiusHarmonicKernel_prime_pow hp,
    if_neg one_ne_zero, if_pos rfl, if_pos rfl, mul_one,
    smoothHarmonicKernel_prime_pow f hp (Nat.succ_ne_zero k), coprimeMoebiusHarmonic_apply]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcop : Nat.Coprime (p ^ (k + 1)) f ↔ p ∉ f.primeFactors := by
    rw [Nat.coprime_pow_left_iff (Nat.succ_pos k), Nat.Prime.coprime_iff_not_dvd hp,
      Nat.mem_primeFactors]
    simp [hp, hf]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [zero_add, pow_one, pow_zero] at hcop ⊢
    simp only [smoothHarmonicKernel_apply, Nat.primeFactors_one, empty_subset, if_true,
      Nat.cast_one, inv_one, one_mul]
    by_cases h : p ∈ f.primeFactors
    · rw [if_pos h, if_neg (fun hc => hcop.mp hc h)]
      field_simp
      ring
    · rw [if_neg h, if_pos (hcop.mpr h), moebius_apply_prime hp]
      push_cast
      ring
  · rw [smoothHarmonicKernel_prime_pow f hp hk1.ne']
    have hμ : (moebius (p ^ (k + 1)) : ℝ) / ((p ^ (k + 1) : ℕ) : ℝ) = 0 := by
      rw [moebius_apply_prime_pow hp (Nat.succ_ne_zero k), if_neg (by omega)]
      simp
    rw [hμ, ite_self]
    split_ifs <;> (try rw [pow_succ]) <;> field_simp <;> ring

/-! ### Coprime harmonic sums -/

/-- `m_f(Y) = Σ_{a ≤ Y, (a,f)=1} μ(a)/a`. -/
def coprimeMoebiusHarmonicSum (f Y : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 Y, if Nat.Coprime a f then (moebius a : ℝ) / a else 0

theorem coprimeMoebiusHarmonicSum_eq_kernel {f : ℕ} (hf : f ≠ 0) (Y : ℕ) :
    coprimeMoebiusHarmonicSum f Y =
      ∑ d ∈ Icc 1 Y, smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d) := by
  have h := RHTower.sum_Icc_mul_apply (smoothHarmonicKernel f) moebiusHarmonicKernel Y
  rw [smoothHarmonicKernel_mul_moebiusHarmonicKernel hf] at h
  simpa [coprimeMoebiusHarmonicSum, moebiusHarmonicSum, coprimeMoebiusHarmonic_apply,
    moebiusHarmonicKernel_apply] using h

/-- The Rankin product `Π(f) = ∏_{p ∣ f} (1 - p^{-3/4})^{-1}`. -/
def rankinProduct (f : ℕ) : ℝ := ∏ p ∈ f.primeFactors, (1 - rankinRatio p)⁻¹

theorem one_le_rankinProduct (f : ℕ) : 1 ≤ rankinProduct f := by
  unfold rankinProduct
  refine one_le_prod₀ fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp']
  rw [le_inv_comm₀ zero_lt_one h1r, inv_one]
  linarith [rankinRatio_nonneg p]

theorem rankinProduct_mul {m n : ℕ} (h : Nat.Coprime m n) :
    rankinProduct (m * n) = rankinProduct m * rankinProduct n := by
  unfold rankinProduct
  rw [Nat.Coprime.primeFactors_mul h, prod_union (Nat.Coprime.disjoint_primeFactors h)]

theorem rankinProduct_le {f : ℕ} (hf : f ≠ 0) :
    rankinProduct f ≤ 25 / 4 * (f : ℝ) ^ (1 / 4 : ℝ) := prod_inv_one_sub_rankinRatio_le hf

/-- `κ_f(k) k^{1/4}`. -/
def smoothHarmonicKernelRankin (f : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => smoothHarmonicKernel f k * (k : ℝ) ^ (1 / 4 : ℝ), by simp⟩

theorem smoothHarmonicKernelRankin_apply (f k : ℕ) :
    smoothHarmonicKernelRankin f k = smoothHarmonicKernel f k * (k : ℝ) ^ (1 / 4 : ℝ) := rfl

theorem smoothHarmonicKernelRankin_nonneg (f k : ℕ) : 0 ≤ smoothHarmonicKernelRankin f k :=
  mul_nonneg (smoothHarmonicKernel_nonneg f k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem isMultiplicative_smoothHarmonicKernelRankin (f : ℕ) :
    (smoothHarmonicKernelRankin f).IsMultiplicative := by
  refine ⟨by simp [smoothHarmonicKernelRankin_apply,
    (isMultiplicative_smoothHarmonicKernel f).map_one], fun {m n} h => ?_⟩
  simp only [smoothHarmonicKernelRankin_apply]
  rw [(isMultiplicative_smoothHarmonicKernel f).map_mul_of_coprime h, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The local factor of the Rankin kernel: `(1 - r_p)⁻¹` for `p ∣ f`, `1` otherwise. -/
theorem hasSum_smoothHarmonicKernelRankin_prime_pow (f : ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => smoothHarmonicKernelRankin f (p ^ k))
      (if p ∈ f.primeFactors then (1 - rankinRatio p)⁻¹ else 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hval : ∀ k : ℕ, smoothHarmonicKernelRankin f (p ^ k) =
      if p ∈ f.primeFactors then rankinRatio p ^ k else if k = 0 then 1 else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [(isMultiplicative_smoothHarmonicKernelRankin f).map_one]
    · rw [smoothHarmonicKernelRankin_apply, smoothHarmonicKernel_prime_pow f hp hk.ne',
        if_neg hk.ne', Nat.cast_pow]
      split_ifs
      · exact inv_pow_mul_rpow_quarter hpR k
      · exact zero_mul _
  simp_rw [hval]
  split_ifs with h
  · exact hasSum_geometric_of_lt_one (rankinRatio_nonneg p) (by linarith [rankinRatio_le hp])
  · exact hasSum_ite_eq 0 1

/-- **Rankin mass of the smooth kernel.** `Σ_{k ≤ Y} κ_f(k) k^{1/4} ≤ Π(f)`. -/
theorem sum_Icc_smoothHarmonicKernelRankin_le (f Y : ℕ) :
    ∑ k ∈ Icc 1 Y, smoothHarmonicKernelRankin f k ≤ rankinProduct f := by
  classical
  set R := smoothHarmonicKernelRankin f
  have hm := isMultiplicative_smoothHarmonicKernelRankin f
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖R (p ^ k)‖) := fun hp => by
    simp only [R, Real.norm_eq_abs]
    exact (hasSum_smoothHarmonicKernelRankin_prime_pow f hp).summable.abs
  have hhas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n => R n) hm.map_one (fun h => hm.map_mul_of_coprime h) hnorm (range (Y + 1))).2
  have hsub : ∀ n ∈ Icc 1 Y, n ∈ Nat.factoredNumbers (range (Y + 1)) := by
    intro n hn
    rw [mem_Icc] at hn
    refine Nat.mem_factoredNumbers.mpr ⟨by omega, fun q hq => ?_⟩
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactorsList hq).trans hn.2))
  have hle : ∑ n ∈ Icc 1 Y, R n ≤ ∏ p ∈ range (Y + 1) with p.Prime, ∑' k : ℕ, R (p ^ k) := by
    rw [← sum_subtype_of_mem (fun n => R n) hsub]
    exact sum_le_hasSum _ (fun n _ => smoothHarmonicKernelRankin_nonneg f n) hhas
  refine hle.trans ?_
  rw [prod_congr rfl fun p hp =>
    (hasSum_smoothHarmonicKernelRankin_prime_pow f (mem_filter.mp hp).2).tsum_eq, prod_ite_mem]
  refine prod_le_prod_of_subset_of_one_le_real inter_subset_right fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp']
  rw [le_inv_comm₀ zero_lt_one h1r, inv_one]
  linarith [rankinRatio_nonneg p]

/-- Conditional on a log-power rate for `m`, `|m_f(Y)| ≤ 256 C Π(f) (1 + log Y)^{-2}`. -/
theorem abs_coprimeMoebiusHarmonicSum_le_of {C : ℝ}
    (hC : ∀ N : ℕ, 1 ≤ N → |moebiusHarmonicSum N| ≤ C / (1 + Real.log N) ^ 4)
    {f : ℕ} (hf : f ≠ 0) {Y : ℕ} (hY : 1 ≤ Y) :
    |coprimeMoebiusHarmonicSum f Y| ≤ 256 * C * rankinProduct f / (1 + Real.log Y) ^ 2 := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hYR
  have hLY : 0 < (1 + Real.log Y) ^ 2 := by positivity
  rw [coprimeMoebiusHarmonicSum_eq_kernel hf]
  have hpt : ∀ d ∈ Icc 1 Y, |smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)| ≤
      256 * C / (1 + Real.log Y) ^ 2 * smoothHarmonicKernelRankin f d := by
    intro d hd
    obtain ⟨hd1, hdY⟩ := mem_Icc.mp hd
    have hq : 1 ≤ Y / d := (Nat.one_le_div_iff (by omega)).mpr hdY
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hqR : (1 : ℝ) ≤ ((Y / d : ℕ) : ℝ) := by exact_mod_cast hq
    have hlq : 0 ≤ Real.log ((Y / d : ℕ) : ℝ) := Real.log_nonneg hqR
    have hld : 0 ≤ Real.log d := Real.log_nonneg hdR
    have hsplit := one_add_log_le_two_mul_log_div hd1 hdY
    have hm := hC (Y / d) hq
    have hβ := smoothHarmonicKernel_nonneg f d
    have hlog2 := one_add_log_sq_le_rpow_quarter hdR
    rw [abs_mul, abs_of_nonneg hβ, smoothHarmonicKernelRankin_apply]
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
    calc smoothHarmonicKernel f d * |moebiusHarmonicSum (Y / d)|
        ≤ smoothHarmonicKernel f d * (4 * C * (1 + Real.log d) ^ 2 / (1 + Real.log Y) ^ 2) :=
          mul_le_mul_of_nonneg_left (hm.trans hstep) hβ
      _ ≤ smoothHarmonicKernel f d *
            (4 * C * (64 * (d : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log Y) ^ 2) := by gcongr
      _ = 256 * C / (1 + Real.log Y) ^ 2 * (smoothHarmonicKernel f d * (d : ℝ) ^ (1 / 4 : ℝ)) := by
          ring
  calc |∑ d ∈ Icc 1 Y, smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)|
      ≤ ∑ d ∈ Icc 1 Y, |smoothHarmonicKernel f d * moebiusHarmonicSum (Y / d)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 Y, 256 * C / (1 + Real.log Y) ^ 2 * smoothHarmonicKernelRankin f d :=
        sum_le_sum hpt
    _ = 256 * C / (1 + Real.log Y) ^ 2 * ∑ d ∈ Icc 1 Y, smoothHarmonicKernelRankin f d := by
        rw [mul_sum]
    _ ≤ 256 * C / (1 + Real.log Y) ^ 2 * rankinProduct f :=
        mul_le_mul_of_nonneg_left (sum_Icc_smoothHarmonicKernelRankin_le f Y) (by positivity)
    _ = _ := by ring

/-- **Coprime harmonic decay.** `|m_f(Y)| ≤ C Π(f) (1 + log Y)^{-2}`. -/
theorem exists_abs_coprimeMoebiusHarmonicSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ C * rankinProduct f / (1 + Real.log Y) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_moebiusHarmonicSum_le
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  exact ⟨256 * C, by positivity, fun f hf Y hY => abs_coprimeMoebiusHarmonicSum_le_of hC hf hY⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
