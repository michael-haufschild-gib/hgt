import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeRowIsMinorArcBelowTheDiagonal

/-!
# Vinogradov's bound at rationals of any denominator

For a primitive `q`-th root of unity `ζ`, `q ≥ 1`, and `1 ≤ U`,

`‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ U log U + log U·T₁ + log N·Π + T_L + (log₂ N + 1)(1 + log N) √B`

(`norm_sum_vonMangoldt_pow_le`), with the Type-I majorant `T₁ = (U/q + 1)W_q + (N/q)(1 + log U)`,
its log-weighted version `T_L`, the Type-II block bound `B` of the corpus, and the block bound
`Π` of the double convolution above `U`. The Vaughan identity of the corpus
(`BezoutValuationIncidence.vonMangoldt_eq_vaughan_decomposition`) splits the sum; the difference
from the corpus's prime-root law is that `q` may be smaller than `U`:

* in a Type-I sum the moduli `d` divisible by `q` have `ζ^d = 1` and cost `N/d`, together
  `(N/q)(1 + log U)` (`sum_Icc_dvd_div_le`); the others cost `2/|ζ^d − 1|`, at most
  `(U/q + 1) W_q` over `d ≤ U` (`sum_Icc_geomMajorant_le`);
* the double convolution `Λ_U ∗ μ_U ∗ 1` is Type I on `d ≤ U` (coefficients `≤ log d`) and Type II
  on `U < d ≤ U²` against the constant `1` (`norm_sum_doubleConv_le`).
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

/-! ## Type-I sums at a root of any order -/

/-- `Σ_{1 ≤ d ≤ V} F_0(ζ^d) ≤ (V/q + 1) W_q`, `F_0(w) = 2/|w − 1|` off `w = 1`. -/
theorem sum_Icc_geomMajorant_le {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (V : ℕ) :
    ∑ d ∈ Icc 1 V, geomMajorant 0 (ζ ^ d) ≤ ((V : ℝ) / q + 1) * rootHarmonicSum q := by
  have h := sum_Ioc_root_mul_pow_le hq hζ (z := 1) (one_pow q) (geomMajorant 0)
    (geomMajorant_nonneg le_rfl) 0 V
  rw [sum_nthRootsFinset_geomMajorant hq 0, zero_add, zero_add] at h
  simp only [one_mul] at h
  rwa [show Icc 1 V = Ioc 0 V from (Finset.Icc_add_one_left_eq_Ioc 0 V)]

/-- `Σ_{d ≤ V, q | d} N/d ≤ (N/q)(1 + log V)`. -/
theorem sum_Icc_dvd_div_le {q : ℕ} (hq : 0 < q) (N V : ℕ) :
    ∑ d ∈ (Icc 1 V).filter (q ∣ ·), (N : ℝ) / d ≤ (N : ℝ) / q * (1 + Real.log V) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have himg : (Icc 1 V).filter (q ∣ ·) = (Icc 1 (V / q)).map ⟨(q * ·), fun a b h =>
      Nat.eq_of_mul_eq_mul_left hq h⟩ := by
    ext d
    simp only [mem_filter, mem_Icc, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at h1
        · exact hj
      · exact (Nat.le_div_iff_mul_le hq).mpr (by linarith [mul_comm q j])
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hq h1, ?_⟩, dvd_mul_right q j⟩
      have := (Nat.le_div_iff_mul_le hq).mp h2
      linarith [mul_comm q j]
  rw [himg, sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.cast_mul]
  have hrw : ∑ j ∈ Icc 1 (V / q), (N : ℝ) / ((q : ℝ) * j) = (N : ℝ) / q * ∑ j ∈ Icc 1 (V / q),
      (1 : ℝ) / j := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    field_simp
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← RHTower.Sieve.harmonic_eq_sum_Icc]
  refine (harmonic_le_one_add_log _).trans ?_
  have := real_log_natCast_mono (Nat.div_le_self V q)
  linarith

/-- A geometric sum `Σ_{1 ≤ m ≤ L} w^m` at a root of unity: `≤ 2/|w − 1|`, or `L` at `w = 1`. -/
theorem norm_sum_Icc_pow_le_root {w : ℂ} (hw : ‖w‖ = 1) (L : ℕ) :
    ‖∑ m ∈ Icc 1 L, w ^ m‖ ≤ geomMajorant 0 w + (if w = 1 then (L : ℝ) else 0) := by
  by_cases h1 : w = 1
  · subst h1
    simp [geomMajorant]
  · rw [if_neg h1, add_zero, geomMajorant, if_neg h1]
    exact GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_sum_Icc_pow_le hw.le h1 L

/-- **Type I at any order.** For `c` supported on `[1, V]` with `|c| ≤ C`,
`‖Σ_{d ≤ M} c(d) Σ_{m ≤ N/d} (ζ^d)^m‖ ≤ C((V/q + 1) W_q + (N/q)(1 + log V))`. -/
theorem norm_typeI_le_any {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) {V : ℕ}
    (c : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d, |c d| ≤ C) (hcs : ∀ d, V < d → c d = 0)
    (M N : ℕ) :
    ‖∑ d ∈ Icc 1 M, (c d : ℂ) * ∑ m ∈ Icc 1 (N / d), (ζ ^ d) ^ m‖ ≤
      C * (((V : ℝ) / q + 1) * rootHarmonicSum q + (N : ℝ) / q * (1 + Real.log V)) := by
  have hnorm : ∀ d : ℕ, ‖ζ ^ d‖ = 1 := fun d => by
    rw [norm_pow, hζ.norm'_eq_one hq.ne', one_pow]
  have hterm : ∀ d ∈ Icc 1 M, ‖(c d : ℂ) * ∑ m ∈ Icc 1 (N / d), (ζ ^ d) ^ m‖ ≤
      if d ≤ V then C * (geomMajorant 0 (ζ ^ d) + (if q ∣ d then (N : ℝ) / d else 0)) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    by_cases hdV : d ≤ V
    · rw [if_pos hdV, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (hc d) ((norm_sum_Icc_pow_le_root (hnorm d) _).trans ?_) (norm_nonneg _)
        hC
      refine add_le_add le_rfl ?_
      by_cases hqd : q ∣ d
      · have h1 : ζ ^ d = 1 := (hζ.pow_eq_one_iff_dvd d).mpr hqd
        rw [if_pos h1, if_pos hqd]
        exact Nat.cast_div_le
      · have h1 : ζ ^ d ≠ 1 := fun h => hqd ((hζ.pow_eq_one_iff_dvd d).mp h)
        rw [if_neg h1, if_neg hqd]
    · rw [if_neg hdV, hcs d (by omega)]
      simp
  have hsum := (norm_sum_le _ _).trans (sum_le_sum hterm)
  refine hsum.trans ?_
  rw [← sum_filter]
  calc ∑ d ∈ (Icc 1 M).filter (· ≤ V), C * (geomMajorant 0 (ζ ^ d) +
        (if q ∣ d then (N : ℝ) / d else 0))
      ≤ ∑ d ∈ Icc 1 V, C * (geomMajorant 0 (ζ ^ d) + (if q ∣ d then (N : ℝ) / d else 0)) := by
        refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => ?_
        · simp only [mem_filter, mem_Icc] at hd ⊢
          omega
        · have := geomMajorant_nonneg (le_refl (0 : ℝ)) (ζ ^ d)
          have : 0 ≤ (if q ∣ d then (N : ℝ) / d else 0) := by split_ifs <;> positivity
          positivity
    _ = C * (∑ d ∈ Icc 1 V, geomMajorant 0 (ζ ^ d) +
          ∑ d ∈ (Icc 1 V).filter (q ∣ ·), (N : ℝ) / d) := by
        rw [← mul_sum, sum_add_distrib, sum_filter]
    _ ≤ C * (((V : ℝ) / q + 1) * rootHarmonicSum q + (N : ℝ) / q * (1 + Real.log V)) :=
        mul_le_mul_of_nonneg_left (add_le_add (sum_Icc_geomMajorant_le hq hζ V)
          (sum_Icc_dvd_div_le hq N V)) hC

/-- **The `log`-weighted Type-I sum at any order.** For `U ≥ 1`,
`‖Σ_{n ≤ N} (μ_U ∗ log)(n) ζⁿ‖ ≤ 2 log N (U/q + 1) W_q + (N/q)(1 + log U) log N`. -/
theorem norm_sum_moebius_log_le_any {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q)
    (U N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (((truncAF (moebius : ArithmeticFunction ℝ) U *
      ArithmeticFunction.log) n : ℝ) : ℂ) * ζ ^ n‖ ≤
      2 * Real.log N * (((U : ℝ) / q + 1) * rootHarmonicSum q) +
        (N : ℝ) / q * (1 + Real.log U) * Real.log N := by
  have hnorm : ∀ d : ℕ, ‖ζ ^ d‖ = 1 := fun d => by
    rw [norm_pow, hζ.norm'_eq_one hq.ne', one_pow]
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hμU : ∀ b, |truncAF (moebius : ArithmeticFunction ℝ) U b| ≤ 1 := fun b =>
    (abs_truncAF_moebius_le U b).trans (by split_ifs <;> norm_num)
  rw [sum_Icc_mul_conv]
  have hterm : ∀ b ∈ Icc 1 N, ‖∑ k ∈ Icc 1 (N / b), ((truncAF (moebius : ArithmeticFunction ℝ) U b *
      ArithmeticFunction.log k : ℝ) : ℂ) * ζ ^ (b * k)‖ ≤
      if b ≤ U then 2 * Real.log N * geomMajorant 0 (ζ ^ b) +
        (if q ∣ b then (N : ℝ) / b * Real.log N else 0) else 0 := by
    intro b hb
    have hb1 : 1 ≤ b := (mem_Icc.mp hb).1
    have hrw : ∑ k ∈ Icc 1 (N / b), ((truncAF (moebius : ArithmeticFunction ℝ) U b *
        ArithmeticFunction.log k : ℝ) : ℂ) * ζ ^ (b * k) =
        ((truncAF (moebius : ArithmeticFunction ℝ) U b : ℝ) : ℂ) *
          ∑ k ∈ Icc 1 (N / b), ((Real.log k : ℝ) : ℂ) * (ζ ^ b) ^ k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [ArithmeticFunction.log_apply, pow_mul]
      push_cast
      ring
    rw [hrw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hbU hqb
    · -- `ζ^b = 1`: the sum of `log k` over `k ≤ N/b`
      have hone : ζ ^ b = 1 := (hζ.pow_eq_one_iff_dvd b).mpr hqb
      have hinner : ‖∑ k ∈ Icc 1 (N / b), ((Real.log k : ℝ) : ℂ) * (ζ ^ b) ^ k‖
          ≤ (N : ℝ) / b * Real.log N := by
        rw [hone]
        simp only [one_pow, mul_one]
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k ∈ Icc 1 (N / b), ‖((Real.log k : ℝ) : ℂ)‖
            ≤ ∑ _k ∈ Icc 1 (N / b), Real.log N := by
              refine sum_le_sum fun k hk => ?_
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg k)]
              exact real_log_natCast_mono ((mem_Icc.mp hk).2.trans (Nat.div_le_self N b))
          _ = ((N / b : ℕ) : ℝ) * Real.log N := by rw [sum_const, Nat.card_Icc]; simp
          _ ≤ (N : ℝ) / b * Real.log N := by
              refine mul_le_mul_of_nonneg_right ?_ hlogN
              exact Nat.cast_div_le
      have hG : 0 ≤ geomMajorant 0 (ζ ^ b) := geomMajorant_nonneg le_rfl _
      calc |truncAF (moebius : ArithmeticFunction ℝ) U b| *
            ‖∑ k ∈ Icc 1 (N / b), ((Real.log k : ℝ) : ℂ) * (ζ ^ b) ^ k‖
          ≤ 1 * ((N : ℝ) / b * Real.log N) :=
            mul_le_mul (hμU b) hinner (norm_nonneg _) zero_le_one
        _ ≤ 2 * Real.log N * geomMajorant 0 (ζ ^ b) + (N : ℝ) / b * Real.log N := by
            have : 0 ≤ 2 * Real.log N * geomMajorant 0 (ζ ^ b) := by positivity
            linarith
    · have hne : ζ ^ b ≠ 1 := fun h => hqb ((hζ.pow_eq_one_iff_dvd b).mp h)
      have hinner := norm_sum_Icc_log_mul_pow_le (hnorm b) hne (N / b)
      have hlog' : Real.log (N / b : ℕ) ≤ Real.log N :=
        real_log_natCast_mono (Nat.div_le_self N b)
      rw [geomMajorant, if_neg hne, add_zero]
      calc |truncAF (moebius : ArithmeticFunction ℝ) U b| *
            ‖∑ k ∈ Icc 1 (N / b), ((Real.log k : ℝ) : ℂ) * (ζ ^ b) ^ k‖
          ≤ 1 * (2 * (2 / ‖ζ ^ b - 1‖) * Real.log N) :=
            mul_le_mul (hμU b) (hinner.trans (mul_le_mul_of_nonneg_left hlog' (by positivity)))
              (norm_nonneg _) zero_le_one
        _ = 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) := by ring
    · rw [truncAF_apply_of_gt (by omega), abs_zero, zero_mul]
  refine ((norm_sum_le _ _).trans (sum_le_sum hterm)).trans ?_
  rw [← sum_filter]
  calc ∑ b ∈ (Icc 1 N).filter (· ≤ U), (2 * Real.log N * geomMajorant 0 (ζ ^ b) +
        (if q ∣ b then (N : ℝ) / b * Real.log N else 0))
      ≤ ∑ b ∈ Icc 1 U, (2 * Real.log N * geomMajorant 0 (ζ ^ b) +
          (if q ∣ b then (N : ℝ) / b * Real.log N else 0)) := by
        refine sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => ?_
        · simp only [mem_filter, mem_Icc] at hb ⊢
          omega
        · have := geomMajorant_nonneg (le_refl (0 : ℝ)) (ζ ^ b)
          have : 0 ≤ (if q ∣ b then (N : ℝ) / b * Real.log N else 0) := by
            split_ifs <;> positivity
          positivity
    _ = 2 * Real.log N * ∑ b ∈ Icc 1 U, geomMajorant 0 (ζ ^ b) +
          (∑ b ∈ (Icc 1 U).filter (q ∣ ·), (N : ℝ) / b) * Real.log N := by
        rw [sum_add_distrib, ← mul_sum, sum_filter, sum_mul]
        congr 1
        refine sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
    _ ≤ 2 * Real.log N * (((U : ℝ) / q + 1) * rootHarmonicSum q) +
          (N : ℝ) / q * (1 + Real.log U) * Real.log N := by
        refine add_le_add (mul_le_mul_of_nonneg_left (sum_Icc_geomMajorant_le hq hζ U)
          (by positivity)) (mul_le_mul_of_nonneg_right (sum_Icc_dvd_div_le hq N U) hlogN)

/-! ## The double convolution `Λ_U ∗ μ_U ∗ 1` -/

/-- The coefficients `F = Λ_U ∗ μ_U`. -/
def dcCoeff (U : ℕ) : ArithmeticFunction ℝ :=
  truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) U

/-- `|(Λ_U ∗ μ_U)(d)| ≤ log d`. -/
theorem abs_dcCoeff_le (U d : ℕ) : |dcCoeff U d| ≤ Real.log d := by
  rw [dcCoeff, ArithmeticFunction.mul_apply]
  calc |∑ x ∈ d.divisorsAntidiagonal, truncAF vonMangoldt U x.1 *
        truncAF (moebius : ArithmeticFunction ℝ) U x.2|
      ≤ ∑ x ∈ d.divisorsAntidiagonal, vonMangoldt x.1 := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul]
        have h1 : |truncAF vonMangoldt U x.1| ≤ vonMangoldt x.1 := by
          rw [truncAF_apply]
          split_ifs
          · rw [abs_of_nonneg vonMangoldt_nonneg]
          · simp [vonMangoldt_nonneg]
        have h2 : |truncAF (moebius : ArithmeticFunction ℝ) U x.2| ≤ 1 :=
          abs_truncAF_moebius_le_one U x.2
        calc |truncAF vonMangoldt U x.1| * |truncAF (moebius : ArithmeticFunction ℝ) U x.2|
            ≤ vonMangoldt x.1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) vonMangoldt_nonneg
          _ = vonMangoldt x.1 := mul_one _
    _ = ∑ i ∈ d.divisors, vonMangoldt i := by
        rw [Nat.sum_divisorsAntidiagonal (fun a _ => vonMangoldt a)]
    _ = Real.log d := vonMangoldt_sum

/-- `Λ_U ∗ μ_U` vanishes above `U²`. -/
theorem dcCoeff_eq_zero {U d : ℕ} (hd : U * U < d) : dcCoeff U d = 0 := by
  rw [dcCoeff, ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun x hx => ?_
  have hx' := Nat.mem_divisorsAntidiagonal.mp hx
  by_cases h1 : x.1 ≤ U
  · have h2 : U < x.2 := by
      by_contra h2
      push Not at h2
      have : x.1 * x.2 ≤ U * U := Nat.mul_le_mul h1 h2
      omega
    rw [truncAF_apply_of_gt (f := (moebius : ArithmeticFunction ℝ)) h2, mul_zero]
  · rw [truncAF_apply_of_gt (f := vonMangoldt) (by omega), zero_mul]

/-- **Type II against the constant.** For `α` with `|α| ≤ 1`, vanishing on `[1, U]` and above `U²`,
`‖Σ_{d ≤ N} α(d) Σ_{k ≤ N/d} ζ^{dk}‖ ≤ (log₂ U + 1) √(N (N/q + U² W_q/q + N/U + W_q))`. -/
theorem norm_typeII_const_le {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) {U : ℕ}
    (hU : 1 ≤ U) (N : ℕ) (α : ℕ → ℝ) (hα : ∀ d, |α d| ≤ 1) (hα0 : ∀ d, d ≤ U → α d = 0)
    (hαU : ∀ d, U * U < d → α d = 0) :
    ‖∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), ((α d * 1 : ℝ) : ℂ) * ζ ^ (d * k)‖ ≤
      (Nat.log 2 U + 1) * Real.sqrt (N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q +
        (N : ℝ) / U + rootHarmonicSum q)) := by
  set I := Nat.log 2 U + 1 with hI
  set F : ℕ → ℂ := fun d => ∑ k ∈ Icc 1 (N / d), ((α d * 1 : ℝ) : ℂ) * ζ ^ (d * k) with hF
  have hUI : U * U < 2 ^ I * U := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) U
    exact Nat.mul_lt_mul_of_pos_right this (by omega)
  have hext : ∑ d ∈ Icc 1 N, F d = ∑ d ∈ Ioc U (2 ^ I * U), F d := by
    have hzero : ∀ d, F d ≠ 0 → U < d ∧ d ≤ U * U ∧ d ≤ N := by
      intro d hd
      refine ⟨?_, ?_, ?_⟩
      · by_contra h
        push Not at h
        apply hd
        simp [hF, hα0 d h]
      · by_contra h
        push Not at h
        apply hd
        simp [hF, hαU d h]
      · by_contra h
        push Not at h
        apply hd
        simp [hF, Nat.div_eq_of_lt h]
    rw [← sum_filter_ne_zero, ← sum_filter_ne_zero (s := Ioc U (2 ^ I * U))]
    congr 1
    ext d
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨h1, h2, _⟩ := hzero d h
      exact ⟨⟨h1, by omega⟩, h⟩
    · rintro ⟨-, h⟩
      obtain ⟨h1, _, h3⟩ := hzero d h
      exact ⟨⟨by omega, h3⟩, h⟩
  rw [hext, sum_Ioc_eq_sum_dyadic]
  have hblock : ∀ i ∈ range I, ‖∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), F d‖ ≤
      Real.sqrt (N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q + (N : ℝ) / U + rootHarmonicSum q)) := by
    intro i hi
    set D := 2 ^ i * U with hD
    have hD1 : U ≤ D := Nat.le_mul_of_pos_left U (Nat.two_pow_pos i)
    have hD0 : 0 < D := by omega
    by_cases hDU : U * U ≤ D
    · -- the block lies above `U²`
      have : ∑ d ∈ Ioc D (2 * D), F d = 0 := sum_eq_zero fun d hd => by
        simp [hF, hαU d (by have := (mem_Ioc.mp hd).1; omega)]
      rw [this, norm_zero]
      exact Real.sqrt_nonneg _
    push Not at hDU
    have h := norm_sq_typeII_block_le hq hζ N hD0 α (fun _ => 1) hα
    have hsum1 : ∑ k ∈ Icc 1 (N / D), ((fun _ : ℕ => (1 : ℝ)) k) ^ 2 = ((N / D : ℕ) : ℝ) := by
      simp
    rw [hsum1] at h
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
    have hDR : (U : ℝ) ≤ D := by exact_mod_cast hD1
    have hDUR : (D : ℝ) ≤ U * U := by exact_mod_cast hDU.le
    have hW := rootHarmonicSum_nonneg q
    have hND : ((N / D : ℕ) : ℝ) * D ≤ N := by exact_mod_cast Nat.div_mul_le_self N D
    have hND' : ((N / D : ℕ) : ℝ) ≤ N / U := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [Nat.cast_nonneg (α := ℝ) (N / D)]
    have hbound : ((N / D : ℕ) : ℝ) * ((D : ℝ) * (((D : ℝ) / q + 1) *
        (((N / D : ℕ) : ℝ) + rootHarmonicSum q))) ≤
        N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q + (N : ℝ) / U +
          rootHarmonicSum q) := by
      set m : ℝ := ((N / D : ℕ) : ℝ) with hm
      have hm0 : 0 ≤ m := Nat.cast_nonneg _
      have e : m * ((D : ℝ) * (((D : ℝ) / q + 1) * (m + rootHarmonicSum q))) =
          (m * D) * (m * D) / q + (m * D) * D * rootHarmonicSum q / q + (m * D) * m +
            (m * D) * rootHarmonicSum q := by
        field_simp
        ring
      rw [e]
      have hmD0 : 0 ≤ m * D := by positivity
      have t1 : (m * D) * (m * D) / q ≤ N * (N / q) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right (mul_le_mul hND hND hmD0 (Nat.cast_nonneg _)) hqR.le
      have t2 : (m * D) * D * rootHarmonicSum q / q ≤ N * ((U : ℝ) * U * rootHarmonicSum q / q) := by
        rw [mul_div_assoc']
        refine div_le_div_of_nonneg_right ?_ hqR.le
        have : (m * D) * D ≤ N * ((U : ℝ) * U) := mul_le_mul hND hDUR (Nat.cast_nonneg _)
          (Nat.cast_nonneg _)
        nlinarith
      have t3 : (m * D) * m ≤ N * (N / U) := mul_le_mul hND hND' hm0 (Nat.cast_nonneg _)
      have t4 : (m * D) * rootHarmonicSum q ≤ N * rootHarmonicSum q :=
        mul_le_mul_of_nonneg_right hND hW
      nlinarith
    have h2 := h.trans hbound
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  calc ‖∑ i ∈ range I, ∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), F d‖
      ≤ ∑ i ∈ range I, ‖∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), F d‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range I, Real.sqrt (N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q +
          (N : ℝ) / U + rootHarmonicSum q)) := sum_le_sum hblock
    _ = (Nat.log 2 U + 1) * Real.sqrt (N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q +
          (N : ℝ) / U + rootHarmonicSum q)) := by
        rw [sum_const, card_range, nsmul_eq_mul, hI]
        push_cast
        ring

/-- **The double convolution.** For `1 ≤ U` and `3 ≤ N`,
`‖Σ_{n ≤ N} (Λ_U ∗ μ_U ∗ 1)(n) ζⁿ‖ ≤ log U·T₁ + log N (log₂ U + 1) √(N(U²/q+1)(N/U + W_q))`. -/
theorem norm_sum_doubleConv_le {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) {U : ℕ}
    (hU : 1 ≤ U) {N : ℕ} (hN : 3 ≤ N) :
    ‖∑ n ∈ Icc 1 N, (((dcCoeff U * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * ζ ^ n‖ ≤
      Real.log U * (((U : ℝ) / q + 1) * rootHarmonicSum q + (N : ℝ) / q * (1 + Real.log U)) +
        Real.log N * ((Nat.log 2 U + 1) * Real.sqrt (N * ((N : ℝ) / q + (U : ℝ) * U * rootHarmonicSum q / q +
          (N : ℝ) / U + rootHarmonicSum q))) := by
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogU : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  rw [sum_Icc_mul_conv]
  have hz : ∀ k ∈ Icc 1 N, (zeta : ArithmeticFunction ℝ) k = 1 := fun k hk => by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg (by have := (mem_Icc.mp hk).1; omega)]
    simp
  have hsplit : ∀ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), ((dcCoeff U d *
      (zeta : ArithmeticFunction ℝ) k : ℝ) : ℂ) * ζ ^ (d * k) =
      ((if d ≤ U then dcCoeff U d else 0 : ℝ) : ℂ) * ∑ k ∈ Icc 1 (N / d), (ζ ^ d) ^ k +
        ∑ k ∈ Icc 1 (N / d), (((if U < d ∧ d ≤ N then dcCoeff U d / Real.log N else 0) * 1 : ℝ) : ℂ) *
          ζ ^ (d * k) * (Real.log N : ℂ) := by
    intro d hd
    have hlogN0 : (Real.log N : ℂ) ≠ 0 := by
      exact_mod_cast (show Real.log N ≠ 0 by linarith)
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hkN : k ≤ N := (mem_Icc.mp hk).2.trans (Nat.div_le_self N d)
    rw [hz k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, hkN⟩), pow_mul]
    have hdN : d ≤ N := (mem_Icc.mp hd).2
    by_cases hdU : d ≤ U
    · rw [if_pos hdU, if_neg (by omega)]
      push_cast
      ring
    · rw [if_neg hdU, if_pos ⟨by omega, hdN⟩]
      simp only [Complex.ofReal_div, Complex.ofReal_zero, mul_one, zero_mul, zero_add]
      field_simp
  rw [sum_congr rfl hsplit, sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_typeI_le_any hq hζ (fun d => if d ≤ U then dcCoeff U d else 0) hlogU
      (fun d => by
        split_ifs with hdU
        · refine (abs_dcCoeff_le U d).trans ?_
          rcases Nat.eq_zero_or_pos d with rfl | hd
          · simp [hlogU]
          · exact Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdU)
        · simp [hlogU])
      (fun d hd => by simp [show ¬ d ≤ U by omega]) N N
  · rw [show ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), (((if U < d ∧ d ≤ N then dcCoeff U d / Real.log N else 0)
        * 1 : ℝ) : ℂ) * ζ ^ (d * k) * (Real.log N : ℂ) = (Real.log N : ℂ) * ∑ d ∈ Icc 1 N,
        ∑ k ∈ Icc 1 (N / d), (((if U < d ∧ d ≤ N then dcCoeff U d / Real.log N else 0) * 1 : ℝ) : ℂ) *
          ζ ^ (d * k) by
      rw [mul_sum]
      refine sum_congr rfl fun d _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      ring]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine norm_typeII_const_le hq hζ hU N _ (fun d => ?_)
      (fun d hd => by simp [show ¬ U < d by omega])
      (fun d hd => by simp [dcCoeff_eq_zero hd])
    split_ifs with hdU
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Real.log N), div_le_one (by linarith)]
      refine (abs_dcCoeff_le U d).trans ?_
      exact Real.log_le_log (by exact_mod_cast (show 0 < d by omega)) (by exact_mod_cast hdU.2)
    · simp

/-! ## Vinogradov's bound -/

/-- The majorant of Vinogradov's bound at a primitive `q`-th root, with Vaughan parameter `U`. -/
def vinogradovBound (q U N : ℕ) : ℝ :=
  U * Real.log U
    + (Real.log U * (((U : ℝ) / q + 1) * rootHarmonicSum q + (N : ℝ) / q * (1 + Real.log U)) +
        Real.log N * ((Nat.log 2 U + 1) * Real.sqrt (N * ((N : ℝ) / q +
          (U : ℝ) * U * rootHarmonicSum q / q + (N : ℝ) / U + rootHarmonicSum q))))
    + (2 * Real.log N * (((U : ℝ) / q + 1) * rootHarmonicSum q) +
        (N : ℝ) / q * (1 + Real.log U) * Real.log N)
    + (Nat.log 2 N + 1) * (1 + Real.log N) * Real.sqrt (typeIIBlockBound q U N)

/-- **Vinogradov's bound at a root of any order.** For a primitive `q`-th root `ζ`, `1 ≤ U` and
`3 ≤ N`, `‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ vinogradovBound q U N`. -/
theorem norm_sum_vonMangoldt_pow_le {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q)
    {U : ℕ} (hU : 1 ≤ U) {N : ℕ} (hN : 3 ≤ N) :
    ‖∑ n ∈ Icc 1 N, ((vonMangoldt n : ℝ) : ℂ) * ζ ^ n‖ ≤ vinogradovBound q U N := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hq.ne'
  have h := norm_sum_vonMangoldt_mul_pow_le_split hnorm U N
  have h2 := norm_sum_doubleConv_le hq hζ hU hN
  have h3 := norm_sum_moebius_log_le_any hq hζ U N
  have h4 := norm_sum_vonMangoldt_typeII_le hq hζ hU N
  have e : (dcCoeff U * (zeta : ArithmeticFunction ℝ)) = truncAF vonMangoldt U *
      truncAF (moebius : ArithmeticFunction ℝ) U * (zeta : ArithmeticFunction ℝ) := rfl
  rw [e] at h2
  unfold vinogradovBound
  linarith

end

end GaloisForLFunctions.PrimeExponentialSums
