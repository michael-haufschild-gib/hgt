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
  rw [Nat.Coprime.primeFactors_mul h]
  by_cases hm : m.primeFactors ⊆ f.primeFactors <;> by_cases hn : n.primeFactors ⊆ f.primeFactors
  · rw [if_pos (union_subset hm hn), if_pos hm, if_pos hn]; push_cast; rw [mul_inv]
  · rw [if_neg (fun h' => hn (subset_union_right.trans h')), if_neg hn, mul_zero]
  · rw [if_neg (fun h' => hm (subset_union_left.trans h')), if_neg hm, zero_mul]
  · rw [if_neg (fun h' => hm (subset_union_left.trans h')), if_neg hm, zero_mul]

theorem smoothHarmonicKernel_prime_pow (f : ℕ) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    smoothHarmonicKernel f (p ^ k) = if p ∈ f.primeFactors then ((p : ℝ) ^ k)⁻¹ else 0 := by
  rw [smoothHarmonicKernel_apply, Nat.primeFactors_prime_pow hk hp]
  simp only [singleton_subset_iff]
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
  have h := prod_le_prod (s := f.primeFactors) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
    (fun p hp => by
      have hp' := Nat.prime_of_mem_primeFactors hp
      have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp']
      rw [le_inv_comm₀ zero_lt_one h1r, inv_one]
      linarith [rankinRatio_nonneg p])
  simpa using h

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

/-! ### The coprime pair sum -/

/-- `S'_g(X) = Σ_{a,b ≤ X, (a,b)=1, (ab,g)=1} μ(a)μ(b)/(ab)`. -/
def coprimePairMoebiusHarmonicSum (g X : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if Nat.Coprime a b ∧ Nat.Coprime (a * b) g then
      (moebius a : ℝ) / a * ((moebius b : ℝ) / b) else 0

theorem moebiusHarmonic_mul {m n : ℕ} (h : Nat.Coprime m n) :
    (moebius (m * n) : ℝ) / ((m * n : ℕ) : ℝ) = (moebius m : ℝ) / m * ((moebius n : ℝ) / n) := by
  have := isMultiplicative_moebiusHarmonicKernel.map_mul_of_coprime h
  simpa only [moebiusHarmonicKernel_apply] using this

theorem moebiusHarmonic_mul_of_not_coprime {δ a : ℕ} (h : ¬ Nat.Coprime a δ) :
    (moebius (δ * a) : ℝ) / ((δ * a : ℕ) : ℝ) = 0 := by
  obtain ⟨p, hp, hpa, hpδ⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hsq : ¬ Squarefree (δ * a) := fun hs =>
    hp.one_lt.ne' (Nat.isUnit_iff.mp (hs p (Nat.mul_dvd_mul hpδ hpa)))
  simp [moebius_eq_zero_of_not_squarefree hsq]

/-- Multiples of `δ` prime to `g`: `Σ_{a ≤ X, δ ∣ a, (a,g)=1} μ(a)/a = [(δ,g)=1] μ(δ)/δ · m_{δg}(X/δ)`. -/
theorem sum_multiples_coprimeMoebiusHarmonic {δ : ℕ} (hδ : 0 < δ) (g X : ℕ) :
    ∑ a ∈ Icc 1 X, (if δ ∣ a ∧ Nat.Coprime a g then (moebius a : ℝ) / a else 0) =
      if Nat.Coprime δ g then
        (moebius δ : ℝ) / δ * coprimeMoebiusHarmonicSum (δ * g) (X / δ) else 0 := by
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
  have hsplit : ∑ a ∈ Icc 1 X, (if δ ∣ a ∧ Nat.Coprime a g then (moebius a : ℝ) / a else 0) =
      ∑ a ∈ (Icc 1 X).filter (fun a => δ ∣ a),
        (if Nat.Coprime a g then (moebius a : ℝ) / a else 0) := by
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : δ ∣ a <;> by_cases h2 : Nat.Coprime a g <;> simp [h1, h2]
  rw [hsplit, hbij, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hδ h)]
  by_cases hδg : Nat.Coprime δ g
  · rw [if_pos hδg, coprimeMoebiusHarmonicSum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : Nat.Coprime j (δ * g)
    · obtain ⟨hjδ, hjg⟩ := Nat.coprime_mul_iff_right.mp hj
      rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hδg, hjg⟩), if_pos hj, moebiusHarmonic_mul hjδ.symm]
    · rw [if_neg hj, mul_zero]
      by_cases hjg : Nat.Coprime j g
      · have hjδ : ¬ Nat.Coprime j δ := fun h => hj (Nat.Coprime.mul_right h hjg)
        rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hδg, hjg⟩), moebiusHarmonic_mul_of_not_coprime hjδ]
      · rw [if_neg (fun h => hjg (Nat.coprime_mul_iff_left.mp h).2)]
  · rw [if_neg hδg]
    exact sum_eq_zero fun j _ => by rw [if_neg (fun h => hδg (Nat.coprime_mul_iff_left.mp h).1)]

/-- **The coprimality sieve.** `S'_g(X) = Σ_{δ ≤ X} μ(δ) ([(δ,g)=1] μ(δ) m_{δg}(X/δ)/δ)²`. -/
theorem coprimePairMoebiusHarmonicSum_eq (g X : ℕ) :
    coprimePairMoebiusHarmonicSum g X = ∑ δ ∈ Icc 1 X, (moebius δ : ℝ) *
      (if Nat.Coprime δ g then
        (moebius δ : ℝ) / δ * coprimeMoebiusHarmonicSum (δ * g) (X / δ) else 0) ^ 2 := by
  set u : ℕ → ℝ := fun a => if Nat.Coprime a g then (moebius a : ℝ) / a else 0 with hu
  have hind : ∀ a ∈ Icc 1 X, ∀ b ∈ Icc 1 X, (if Nat.Coprime a b then (1 : ℝ) else 0) =
      ∑ δ ∈ Icc 1 X, if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0 := by
    intro a ha b hb
    obtain ⟨ha1, haX⟩ := mem_Icc.mp ha
    have hdiv : (Nat.gcd a b).divisors = (Icc 1 X).filter (fun δ => δ ∣ a ∧ δ ∣ b) := by
      ext δ
      simp only [Nat.mem_divisors, mem_filter, mem_Icc, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hda, hdb⟩, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hda (by omega), (Nat.le_of_dvd (by omega) hda).trans haX⟩,
          hda, hdb⟩
      · rintro ⟨-, hda, hdb⟩
        exact ⟨⟨hda, hdb⟩, Nat.gcd_ne_zero_left (by omega)⟩
    rw [← sum_filter, ← hdiv, sum_divisors_moebius_real_eq_ite]
  have hS : coprimePairMoebiusHarmonicSum g X = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ δ ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (u a * u b) := by
    unfold coprimePairMoebiusHarmonicSum
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    rw [← sum_mul, ← hind a ha b hb]
    have hua : u a = if Nat.Coprime a g then (moebius a : ℝ) / a else 0 := rfl
    have hub : u b = if Nat.Coprime b g then (moebius b : ℝ) / b else 0 := rfl
    rw [hua, hub]
    have hiff : Nat.Coprime (a * b) g ↔ Nat.Coprime a g ∧ Nat.Coprime b g :=
      Nat.coprime_mul_iff_left
    by_cases hab : Nat.Coprime a b
    · by_cases hag : Nat.Coprime a g
      · by_cases hbg : Nat.Coprime b g
        · rw [if_pos ⟨hab, hiff.mpr ⟨hag, hbg⟩⟩, if_pos hab, if_pos hag, if_pos hbg, one_mul]
        · rw [if_neg (fun h => hbg (hiff.mp h.2).2), if_pos hab, if_pos hag, if_neg hbg,
            mul_zero, mul_zero]
      · rw [if_neg (fun h => hag (hiff.mp h.2).1), if_pos hab, if_neg hag, zero_mul, mul_zero]
    · rw [if_neg (fun h => hab h.1), if_neg hab, zero_mul]
  rw [hS]
  have hswap : ∀ a ∈ Icc 1 X, (∑ b ∈ Icc 1 X, ∑ δ ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (u a * u b)) =
      ∑ δ ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (u a * u b) :=
    fun a _ => sum_comm
  rw [sum_congr rfl hswap, sum_comm]
  refine sum_congr rfl fun δ hδ => ?_
  have hδ0 : 0 < δ := (mem_Icc.mp hδ).1
  set A : ℕ → ℝ := fun a => if δ ∣ a ∧ Nat.Coprime a g then (moebius a : ℝ) / a else 0 with hA
  have hpt : ∀ a b : ℕ, (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (u a * u b) =
      (moebius δ : ℝ) * (A a * A b) := by
    intro a b
    simp only [hA, hu]
    by_cases ha : δ ∣ a <;> by_cases hb : δ ∣ b <;> by_cases hag : Nat.Coprime a g <;>
      by_cases hbg : Nat.Coprime b g <;> simp [ha, hb, hag, hbg]
  calc ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        (if δ ∣ a ∧ δ ∣ b then (moebius δ : ℝ) else 0) * (u a * u b)
      = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (moebius δ : ℝ) * (A a * A b) := by simp_rw [hpt]
    _ = (moebius δ : ℝ) * ((∑ a ∈ Icc 1 X, A a) * ∑ b ∈ Icc 1 X, A b) := by
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
    _ = _ := by
        rw [show (∑ a ∈ Icc 1 X, A a) = _ from sum_multiples_coprimeMoebiusHarmonic hδ0 g X, sq]

/-- Conditional on `|m_f(Y)| ≤ C Π(f)(1 + log Y)^{-2}`, `|S'_g(X)| ≤ C' Π(g)² (1 + log X)^{-4}`. -/
theorem abs_coprimePairMoebiusHarmonicSum_le_of {C : ℝ}
    (hC : ∀ f : ℕ, f ≠ 0 → ∀ Y : ℕ, 1 ≤ Y →
      |coprimeMoebiusHarmonicSum f Y| ≤ C * rankinProduct f / (1 + Real.log Y) ^ 2)
    {g : ℕ} (hg : g ≠ 0) {X : ℕ} (hX : 1 ≤ X) :
    |coprimePairMoebiusHarmonicSum g X| ≤
      16 * 65536 * (25 / 4) ^ 2 * C ^ 2 * (∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ))) *
        rankinProduct g ^ 2 / (1 + Real.log X) ^ 4 := by
  rw [coprimePairMoebiusHarmonicSum_eq]
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlX := Real.log_nonneg hXR
  have hLX : 0 < (1 + Real.log X) ^ 4 := by positivity
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hPg := one_le_rankinProduct g
  set K := 16 * 65536 * (25 / 4) ^ 2 * C ^ 2 * rankinProduct g ^ 2 / (1 + Real.log X) ^ 4 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ δ ∈ Icc 1 X, |(moebius δ : ℝ) * (if Nat.Coprime δ g then
        (moebius δ : ℝ) / δ * coprimeMoebiusHarmonicSum (δ * g) (X / δ) else 0) ^ 2| ≤
      K * (δ : ℝ) ^ (-(5 / 4 : ℝ)) := by
    intro δ hδ
    obtain ⟨hδ1, hδX⟩ := mem_Icc.mp hδ
    have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ1
    have hδ0 : (0 : ℝ) < δ := by linarith
    have hrp : 0 ≤ K * (δ : ℝ) ^ (-(5 / 4 : ℝ)) := mul_nonneg hK0 (Real.rpow_nonneg hδ0.le _)
    split_ifs with hcop
    swap
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, abs_zero]
      exact hrp
    have hq : 1 ≤ X / δ := (Nat.one_le_div_iff (by omega)).mpr hδX
    have hqR : (1 : ℝ) ≤ ((X / δ : ℕ) : ℝ) := by exact_mod_cast hq
    have hlq := Real.log_nonneg hqR
    have hlδ := Real.log_nonneg hδR
    set T := coprimeMoebiusHarmonicSum (δ * g) (X / δ)
    set L := 1 + Real.log ((X / δ : ℕ) : ℝ)
    have hL : 1 ≤ L := by simp only [L]; linarith
    have hT := hC (δ * g) (Nat.mul_ne_zero (by omega) hg) (X / δ) hq
    rw [rankinProduct_mul hcop] at hT
    have hPδ := rankinProduct_le (by omega : δ ≠ 0)
    have hPδ1 := one_le_rankinProduct δ
    have hP : 0 ≤ (δ : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hδ0.le _
    have hT2 : T ^ 2 ≤ (C * (25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) * rankinProduct g)) ^ 2 / L ^ 4 := by
      rw [← sq_abs]
      have hC0 : 0 ≤ C := by
        have := (abs_nonneg T).trans hT
        have hp : 0 < rankinProduct δ * rankinProduct g / L ^ 2 := by positivity
        by_contra hneg
        push Not at hneg
        have : C * (rankinProduct δ * rankinProduct g) / L ^ 2 < 0 := by
          rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos hneg hp
        linarith
      have hT' : |T| ≤ C * (25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) * rankinProduct g) / L ^ 2 := by
        refine hT.trans (div_le_div_of_nonneg_right ?_ (by positivity))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPδ (by linarith)) hC0
      calc |T| ^ 2 ≤ (C * (25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) * rankinProduct g) / L ^ 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hT' 2
        _ = _ := by rw [div_pow, ← pow_mul]
    have hden : 1 / L ^ 4 ≤ 16 * (1 + Real.log δ) ^ 4 / (1 + Real.log X) ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) hLX]
      have h4 : (1 + Real.log X) ^ 4 ≤ (2 * L * (1 + Real.log δ)) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (one_add_log_le_two_mul_log_div hδ1 hδX) 4
      calc 1 * (1 + Real.log X) ^ 4 ≤ (2 * L * (1 + Real.log δ)) ^ 4 := by rw [one_mul]; exact h4
        _ = 16 * (1 + Real.log δ) ^ 4 * L ^ 4 := by ring
    have hl4 := one_add_log_pow_four_le_rpow_quarter hδR
    have hw2 : ((moebius δ : ℝ) / δ) ^ 2 ≤ ((δ : ℝ)⁻¹) ^ 2 := by
      rw [← sq_abs, abs_div, Nat.abs_cast]
      apply pow_le_pow_left₀ (by positivity)
      have hμ : |(moebius δ : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) hμ
    have hμ : |(moebius δ : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hT2' : T ^ 2 ≤ (25 / 4) ^ 2 * C ^ 2 * rankinProduct g ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        (16 * (65536 * (δ : ℝ) ^ (1 / 4 : ℝ)) / (1 + Real.log X) ^ 4) := by
      calc T ^ 2 ≤ (C * (25 / 4 * (δ : ℝ) ^ (1 / 4 : ℝ) * rankinProduct g)) ^ 2 / L ^ 4 := hT2
        _ = (25 / 4) ^ 2 * C ^ 2 * rankinProduct g ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
            (1 / L ^ 4) := by ring
        _ ≤ (25 / 4) ^ 2 * C ^ 2 * rankinProduct g ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
            (16 * (1 + Real.log δ) ^ 4 / (1 + Real.log X) ^ 4) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ _ := by gcongr
    rw [abs_mul, mul_pow, abs_of_nonneg (mul_nonneg (sq_nonneg ((moebius δ : ℝ) / δ)) (sq_nonneg T))]
    calc |(moebius δ : ℝ)| * (((moebius δ : ℝ) / δ) ^ 2 * T ^ 2)
        ≤ 1 * (((δ : ℝ)⁻¹) ^ 2 * ((25 / 4) ^ 2 * C ^ 2 * rankinProduct g ^ 2 *
            ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (16 * (65536 * (δ : ℝ) ^ (1 / 4 : ℝ)) /
              (1 + Real.log X) ^ 4))) := by
          apply mul_le_mul hμ _ (by positivity) zero_le_one
          exact mul_le_mul hw2 hT2' (sq_nonneg _) (sq_nonneg _)
      _ = K * (((δ : ℝ)⁻¹) ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 3) := by rw [hK]; ring
      _ = _ := by rw [inv_sq_mul_rpow_quarter_cube hδ0]
  calc |∑ δ ∈ Icc 1 X, (moebius δ : ℝ) * (if Nat.Coprime δ g then
        (moebius δ : ℝ) / δ * coprimeMoebiusHarmonicSum (δ * g) (X / δ) else 0) ^ 2|
      ≤ ∑ δ ∈ Icc 1 X, |(moebius δ : ℝ) * (if Nat.Coprime δ g then
        (moebius δ : ℝ) / δ * coprimeMoebiusHarmonicSum (δ * g) (X / δ) else 0) ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ δ ∈ Icc 1 X, K * (δ : ℝ) ^ (-(5 / 4 : ℝ)) := sum_le_sum hpt
    _ = K * ∑ δ ∈ Icc 1 X, (δ : ℝ) ^ (-(5 / 4 : ℝ)) := by rw [mul_sum]
    _ ≤ K * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hK0
    _ = _ := by rw [hK]; ring

/-- **Pair decay with coprimality.** `|S'_g(X)| ≤ C Π(g)² (1 + log X)^{-4}`. -/
theorem exists_abs_coprimePairMoebiusHarmonicSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℕ, g ≠ 0 → ∀ X : ℕ, 1 ≤ X →
      |coprimePairMoebiusHarmonicSum g X| ≤ C * rankinProduct g ^ 2 / (1 + Real.log X) ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_coprimeMoebiusHarmonicSum_le
  have hsum0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) :=
    tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨16 * 65536 * (25 / 4) ^ 2 * C ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)), by positivity,
    fun g hg X hX => ?_⟩
  exact abs_coprimePairMoebiusHarmonicSum_le_of hC hg hX

/-! ### The harmonic mean of `Π²` -/

/-- `h(d) = ∏_{p ∣ d} ((1 - r_p)^{-2} - 1)` on squarefree `d`, `0` otherwise. -/
def rankinDivisorKernel : ArithmeticFunction ℝ :=
  ⟨fun d => if Squarefree d then ∏ p ∈ d.primeFactors, ((1 - rankinRatio p)⁻¹ ^ 2 - 1) else 0,
    by simp⟩

theorem rankinDivisorKernel_apply (d : ℕ) : rankinDivisorKernel d =
    if Squarefree d then ∏ p ∈ d.primeFactors, ((1 - rankinRatio p)⁻¹ ^ 2 - 1) else 0 := rfl

theorem inv_one_sub_rankinRatio_ge {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - rankinRatio p)⁻¹ := by
  have h1r : 0 < 1 - rankinRatio p := by linarith [rankinRatio_le hp]
  rw [le_inv_comm₀ zero_lt_one h1r, inv_one]
  linarith [rankinRatio_nonneg p]

theorem rankinDivisorKernel_nonneg (d : ℕ) : 0 ≤ rankinDivisorKernel d := by
  rw [rankinDivisorKernel_apply]
  split_ifs
  · exact prod_nonneg fun p hp => by
      have := inv_one_sub_rankinRatio_ge (Nat.prime_of_mem_primeFactors hp)
      nlinarith
  · exact le_rfl

theorem isMultiplicative_rankinDivisorKernel : rankinDivisorKernel.IsMultiplicative := by
  refine ⟨by simp [rankinDivisorKernel_apply], fun {m n} h => ?_⟩
  simp only [rankinDivisorKernel_apply]
  have hsq : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
    rw [Nat.squarefree_mul_iff]; exact ⟨fun h' => ⟨h'.2.1, h'.2.2⟩, fun h' => ⟨h, h'⟩⟩
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n
  · rw [if_pos (hsq.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, Nat.Coprime.primeFactors_mul h,
      prod_union (Nat.Coprime.disjoint_primeFactors h)]
  · rw [if_neg (fun h' => hn (hsq.mp h').2), if_neg hn, mul_zero]
  · rw [if_neg (fun h' => hm (hsq.mp h').1), if_neg hm, zero_mul]
  · rw [if_neg (fun h' => hm (hsq.mp h').1), if_neg hm, zero_mul]

/-- On squarefree `g`, `Σ_{d ∣ g} h(d) = Π(g)²`. -/
theorem sum_divisors_rankinDivisorKernel {g : ℕ} (hg : Squarefree g) :
    ∑ d ∈ g.divisors, rankinDivisorKernel d = rankinProduct g ^ 2 := by
  have hmul : (rankinDivisorKernel *
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)).IsMultiplicative :=
    isMultiplicative_rankinDivisorKernel.mul isMultiplicative_zeta.natCast
  have hprod := Nat.prod_primeFactors_of_squarefree hg
  rw [← coe_mul_zeta_apply]
  conv_lhs => rw [← hprod]
  rw [hmul.map_prod_of_prime _ (fun p hp => Nat.prime_of_mem_primeFactors hp), rankinProduct,
    ← prod_pow]
  refine prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [coe_mul_zeta_apply, Nat.Prime.sum_divisors hp', rankinDivisorKernel_apply,
    rankinDivisorKernel_apply, if_pos hp'.squarefree, if_pos squarefree_one, hp'.primeFactors,
    prod_singleton, Nat.primeFactors_one, prod_empty]
  ring

/-- `h(d)/d`. -/
def rankinDivisorKernelHarmonic : ArithmeticFunction ℝ :=
  ⟨fun d => rankinDivisorKernel d / d, by simp⟩

theorem isMultiplicative_rankinDivisorKernelHarmonic :
    rankinDivisorKernelHarmonic.IsMultiplicative := by
  refine ⟨by simp [rankinDivisorKernelHarmonic, isMultiplicative_rankinDivisorKernel.map_one],
    fun {m n} h => ?_⟩
  show rankinDivisorKernel (m * n) / ((m * n : ℕ) : ℝ) =
    rankinDivisorKernel m / m * (rankinDivisorKernel n / n)
  rw [isMultiplicative_rankinDivisorKernel.map_mul_of_coprime h, Nat.cast_mul, mul_div_mul_comm]

/-- `h_p/p ≤ 9 p^{-7/4}`. -/
theorem rankin_local_le {p : ℕ} (hp : p.Prime) :
    ((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p ≤ 9 * (p : ℝ) ^ (-(7 / 4 : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr := rankinRatio_le hp
  have hr0 := rankinRatio_nonneg p
  have h1r : 0 < 1 - rankinRatio p := by linarith
  set x := (1 - rankinRatio p)⁻¹ with hx
  have hx1 : x * (1 - rankinRatio p) = 1 := inv_mul_cancel₀ h1r.ne'
  have hx52 : x ≤ 5 / 2 := by rw [hx, inv_le_comm₀ h1r (by norm_num)]; norm_num; linarith
  have hx0 : 1 ≤ x := inv_one_sub_rankinRatio_ge hp
  have hsq : x ^ 2 - 1 ≤ 9 * rankinRatio p := by nlinarith
  have hsplit : (p : ℝ) ^ (-(7 / 4 : ℝ)) = rankinRatio p * (p : ℝ)⁻¹ := by
    rw [rankinRatio, ← Real.rpow_neg_one, ← Real.rpow_add hpR]; norm_num
  rw [hsplit, div_eq_mul_inv]
  have hinv : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hpR.le
  nlinarith

/-- **`Π²` has bounded harmonic mean.** `Σ_{g ≤ N} μ(g)² Π(g)²/g ≤ (1 + log N) E`. -/
theorem sum_rankinProduct_sq_div_le (N : ℕ) :
    ∑ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g ≤
      (1 + Real.log N) * Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) := by
  classical
  set E := Real.exp (9 * ∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) with hE
  set hd := rankinDivisorKernelHarmonic
  set iv : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩ with hiv
  -- termwise domination by the divisor sum
  have hterm : ∀ g ∈ Icc 1 N, (moebius g : ℝ) ^ 2 * rankinProduct g ^ 2 / g ≤ (hd * iv) g := by
    intro g hg
    have hg1 := (mem_Icc.mp hg).1
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
    have hconv : (hd * iv) g = (∑ d ∈ g.divisors, rankinDivisorKernel d) / g := by
      rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => hd x * iv y), sum_div]
      refine sum_congr rfl fun d hdv => ?_
      have hdg := Nat.dvd_of_mem_divisors hdv
      have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hdv
      have hmul : (d : ℝ) * ((g / d : ℕ) : ℝ) = g := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdg]
      show rankinDivisorKernel d / d * ((g / d : ℕ) : ℝ)⁻¹ = rankinDivisorKernel d / g
      rw [← hmul]; field_simp
    rw [hconv]
    by_cases hsq : Squarefree g
    · rw [sum_divisors_rankinDivisorKernel hsq]
      have hμ : (moebius g : ℝ) ^ 2 = 1 := by
        have := moebius_sq_eq_one_of_squarefree hsq
        exact_mod_cast this
      rw [hμ, one_mul]
    · rw [moebius_eq_zero_of_not_squarefree hsq]
      simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        zero_div]
      exact div_nonneg (sum_nonneg fun d _ => rankinDivisorKernel_nonneg d) hgR.le
  refine (sum_le_sum hterm).trans ?_
  rw [RHTower.sum_Icc_mul_apply]
  have hharm : ∀ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), iv m ≤ 1 + Real.log N := by
    intro d hd1
    have h1 : ∑ m ∈ Icc 1 (N / d), iv m = (harmonic (N / d) : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h1]
    refine (harmonic_le_one_add_log _).trans ?_
    rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero, add_zero]
      have : (1 : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hd1).1.trans (mem_Icc.mp hd1).2
      linarith [Real.log_nonneg this]
    · have : ((N / d : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N d
      linarith [Real.log_le_log (by exact_mod_cast hpos) this]
  have hhd0 : ∀ d, 0 ≤ hd d := fun d =>
    div_nonneg (rankinDivisorKernel_nonneg d) (Nat.cast_nonneg _)
  calc ∑ d ∈ Icc 1 N, hd d * ∑ m ∈ Icc 1 (N / d), iv m
      ≤ ∑ d ∈ Icc 1 N, hd d * (1 + Real.log N) :=
        sum_le_sum fun d hdN => mul_le_mul_of_nonneg_left (hharm d hdN) (hhd0 d)
    _ = (1 + Real.log N) * ∑ d ∈ Icc 1 N, hd d := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ (1 + Real.log N) * E := by
        have hlN : 0 ≤ 1 + Real.log N := by
          rcases Nat.eq_zero_or_pos N with rfl | hN
          · simp
          · have : (1 : ℝ) ≤ N := by exact_mod_cast hN
            linarith [Real.log_nonneg this]
        refine mul_le_mul_of_nonneg_left ?_ hlN
        -- Euler product bound
        have hm := isMultiplicative_rankinDivisorKernelHarmonic
        have hval : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, hd (p ^ k) =
            if k = 0 then 1 else if k = 1 then ((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p else 0 := by
          intro p hp k
          rcases Nat.lt_trichotomy k 1 with hk | rfl | hk
          · have : k = 0 := by omega
            subst this
            rw [pow_zero, if_pos rfl]
            exact hm.map_one
          · show rankinDivisorKernel (p ^ 1) / ((p ^ 1 : ℕ) : ℝ) = _
            rw [pow_one, rankinDivisorKernel_apply, if_pos hp.squarefree, hp.primeFactors,
              prod_singleton]
            simp
          · show rankinDivisorKernel (p ^ k) / ((p ^ k : ℕ) : ℝ) = _
            have hns : ¬ Squarefree (p ^ k) := by
              rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega
            rw [rankinDivisorKernel_apply, if_neg hns, if_neg (by omega), if_neg (by omega), zero_div]
        have hloc : ∀ {p : ℕ}, p.Prime → HasSum (fun k => hd (p ^ k))
            (1 + ((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p) := by
          intro p hp
          have h := (hasSum_ite_eq 0 (1 : ℝ)).add
            (hasSum_ite_eq 1 (((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p))
          convert h using 1
          funext k
          rw [hval hp k]
          by_cases h0 : k = 0
          · subst h0; simp
          · by_cases h1 : k = 1
            · subst h1; simp
            · simp [h0, h1]
        have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖hd (p ^ k)‖) := fun hp => by
          simp only [Real.norm_eq_abs]
          exact (hloc hp).summable.abs
        have hhas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
          (f := fun n => hd n) hm.map_one (fun h => hm.map_mul_of_coprime h) hnorm
          (range (N + 1))).2
        have hsub : ∀ n ∈ Icc 1 N, n ∈ Nat.factoredNumbers (range (N + 1)) := by
          intro n hn
          rw [mem_Icc] at hn
          refine Nat.mem_factoredNumbers.mpr ⟨by omega, fun q hq => ?_⟩
          exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactorsList hq).trans hn.2))
        have hle : ∑ n ∈ Icc 1 N, hd n ≤
            ∏ p ∈ range (N + 1) with p.Prime, ∑' k : ℕ, hd (p ^ k) := by
          rw [← sum_subtype_of_mem (fun n => hd n) hsub]
          exact sum_le_hasSum _ (fun n _ => hhd0 n) hhas
        refine hle.trans ?_
        rw [prod_congr rfl fun p hp => (hloc (mem_filter.mp hp).2).tsum_eq]
        have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(7 / 4 : ℝ))) :=
          Real.summable_nat_rpow.mpr (by norm_num)
        calc ∏ p ∈ range (N + 1) with p.Prime, (1 + ((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p)
            ≤ ∏ p ∈ range (N + 1) with p.Prime, Real.exp (9 * (p : ℝ) ^ (-(7 / 4 : ℝ))) := by
              refine prod_le_prod (fun p hp => ?_) fun p hp => ?_
              · have hp' := (mem_filter.mp hp).2
                have := inv_one_sub_rankinRatio_ge hp'
                have h0 : 0 ≤ ((1 - rankinRatio p)⁻¹ ^ 2 - 1) / p :=
                  div_nonneg (by nlinarith) (Nat.cast_nonneg _)
                linarith
              · have hp' := (mem_filter.mp hp).2
                linarith [Real.add_one_le_exp (9 * (p : ℝ) ^ (-(7 / 4 : ℝ))), rankin_local_le hp']
          _ = Real.exp (∑ p ∈ range (N + 1) with p.Prime, 9 * (p : ℝ) ^ (-(7 / 4 : ℝ))) :=
              (Real.exp_sum _ _).symm
          _ ≤ E := by
              rw [hE, Real.exp_le_exp, ← mul_sum]
              exact mul_le_mul_of_nonneg_left
                (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)

end

end GaloisForLFunctions.BezoutValuationIncidence
