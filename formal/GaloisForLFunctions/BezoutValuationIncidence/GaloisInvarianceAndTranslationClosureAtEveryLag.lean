import GaloisForLFunctions.BezoutValuationIncidence.SelbergSupportExactRecurrenceComplexity
import GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal

/-!
# Galois invariance and the translation closure of the row space at every lag

In the spectral form `s(k) = Σ_{ζ ∈ T_N} Y(ord ζ) ζ^k` the coefficient of a response depends only on
the order of the frequency: responses are the exponential sums on `T_N` whose coefficients are
invariant under `ζ ↦ ζ^u`, `u` a unit. Translation by `h` multiplies the coefficient of `ζ` by `ζ^h`,
and the characters `n ↦ ζ^n` are independent, so the translate of a response is again a response
exactly when `ζ^h` is constant on the primitive roots of every active order. For primitive roots of
order `q`, comparing `ζ` with `ζ^{q-1} = ζ̄` shows that this happens exactly when `q / gcd(q, 2)`
divides `h`.

**Translation closure at lag `h`.** The translate `k ↦ s_{N,c}(k + h)` is the response of a row iff
every `q ≤ N` with `Y(q) ≠ 0` satisfies `q / gcd(q, 2) ∣ h`; the translated row then has Selberg
coordinates `Y(q) ζ_q^h = ± Y(q)`. At `h = 1` this is closure only for rows with Selberg support in
`{1, 2}`; at general `h` the closed rows are those supported on the odd divisors of `h` and the
even divisors of `2h`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Constancy of `ζ^h` on the primitive roots -/

theorem dvd_mul_sub_one_of_div_gcd_two_dvd {q h i : ℕ} (hqh : q / Nat.gcd q 2 ∣ h)
    (hi : Nat.Coprime i q) (hi1 : 1 ≤ i) : q ∣ (i - 1) * h := by
  rcases Nat.even_or_odd q with hq | hq
  · have hg : Nat.gcd q 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hq)
    rw [hg] at hqh
    have hi2 : 2 ∣ i - 1 := by
      have hodd : Odd i := by
        by_contra hev
        rw [Nat.not_odd_iff_even] at hev
        have := Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.mp hev) hi
        rw [Nat.coprime_comm] at this
        exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.mp hq) this)
          (by norm_num)
      obtain ⟨t, ht⟩ := hodd
      exact ⟨t, by omega⟩
    have : q = 2 * (q / 2) := (Nat.mul_div_cancel' (even_iff_two_dvd.mp hq)).symm
    rw [this]
    exact mul_dvd_mul hi2 hqh
  · have hg : Nat.gcd q 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hq)
    rw [hg, Nat.div_one] at hqh
    exact Dvd.dvd.mul_left hqh _

/-- If `q / gcd(q, 2)` divides `h`, then `ζ^h` is the same for all primitive `q`-th roots. -/
theorem pow_eq_pow_of_div_gcd_two_dvd {q h : ℕ} (hq : 0 < q) (hqh : q / Nat.gcd q 2 ∣ h)
    {ζ ξ : ℂ} (hζ : IsPrimitiveRoot ζ q) (hξ : IsPrimitiveRoot ξ q) : ζ ^ h = ξ ^ h := by
  haveI : NeZero q := ⟨hq.ne'⟩
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · have h1 : q = 1 := by omega
    subst h1
    rw [IsPrimitiveRoot.one_right_iff.mp hζ, IsPrimitiveRoot.one_right_iff.mp hξ]
  obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hi : Nat.Coprime i q := (hζ.pow_iff_coprime hq i).mp hξ
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [Nat.coprime_zero_left] at hi
      omega
    · exact h0
  have hdvd := dvd_mul_sub_one_of_div_gcd_two_dvd hqh hi hi1
  have h1 : ζ ^ ((i - 1) * h) = 1 := (hζ.pow_eq_one_iff_dvd _).mpr hdvd
  calc ζ ^ h = ζ ^ h * ζ ^ ((i - 1) * h) := by rw [h1, mul_one]
    _ = (ζ ^ i) ^ h := by
      rw [← pow_add, ← pow_mul]
      congr 1
      have : i = (i - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring

/-- Conversely, constancy of `ζ^h` on the primitive `q`-th roots forces `q / gcd(q, 2) ∣ h`. -/
theorem div_gcd_two_dvd_of_pow_const {q h : ℕ} (hq : 0 < q)
    (hconst : ∀ ζ ξ : ℂ, IsPrimitiveRoot ζ q → IsPrimitiveRoot ξ q → ζ ^ h = ξ ^ h) :
    q / Nat.gcd q 2 ∣ h := by
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · interval_cases q <;> simp
  have hζ := Complex.isPrimitiveRoot_exp q hq.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑q)
  have hcop : Nat.Coprime (q - 1) q := by
    have : q = (q - 1) + 1 := by omega
    conv_rhs => rw [this]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hξ := hζ.pow_of_coprime (q - 1) hcop
  have heq := hconst ζ (ζ ^ (q - 1)) hζ hξ
  have hne : ζ ^ h ≠ 0 := pow_ne_zero _ (hζ.ne_zero hq.ne')
  -- `ζ^{(q-2) h} = 1`
  have hpow : ζ ^ ((q - 2) * h) = 1 := by
    have h2 : (ζ ^ (q - 1)) ^ h = ζ ^ ((q - 2) * h) * ζ ^ h := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : q - 1 = (q - 2) + 1 := by omega
      rw [this]
      ring
    rw [h2] at heq
    exact (mul_eq_right₀ hne).mp heq.symm
  have hq2h : q ∣ 2 * h := by
    have hd := (hζ.pow_eq_one_iff_dvd _).mp hpow
    have hsum : (q - 2) * h + 2 * h = q * h := by
      have : q = (q - 2) + 2 := by omega
      conv_rhs => rw [this]
      ring
    have := (Nat.dvd_add_right hd).mp (hsum ▸ dvd_mul_right q h)
    exact this
  rcases Nat.even_or_odd q with he | ho
  · rw [Nat.gcd_eq_right (even_iff_two_dvd.mp he)]
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
    rw [hm, Nat.mul_div_cancel_left m (by norm_num)]
    rw [hm] at hq2h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hq2h
  · rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr ho), Nat.div_one]
    exact (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_left hq2h

theorem pow_const_iff_div_gcd_two_dvd {q h : ℕ} (hq : 0 < q) :
    (∀ ζ ξ : ℂ, IsPrimitiveRoot ζ q → IsPrimitiveRoot ξ q → ζ ^ h = ξ ^ h) ↔
      q / Nat.gcd q 2 ∣ h :=
  ⟨div_gcd_two_dvd_of_pow_const hq, fun hqh _ _ hζ hξ => pow_eq_pow_of_div_gcd_two_dvd hq hqh hζ hξ⟩

/-- The common value of `ζ^h` is a sign. -/
theorem pow_eq_one_or_neg_one_of_div_gcd_two_dvd {q h : ℕ} (hqh : q / Nat.gcd q 2 ∣ h)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) : ζ ^ h = 1 ∨ ζ ^ h = -1 := by
  have hq2 : q ∣ 2 * h := by
    rcases Nat.even_or_odd q with he | ho
    · rw [Nat.gcd_eq_right (even_iff_two_dvd.mp he)] at hqh
      obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
      rw [hm, Nat.mul_div_cancel_left m (by norm_num)] at hqh
      rw [hm]
      exact mul_dvd_mul_left 2 hqh
    · rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr ho), Nat.div_one] at hqh
      exact Dvd.dvd.mul_left hqh 2
  have h2 : ζ ^ h * ζ ^ h = 1 := by
    rw [← pow_add, ← two_mul]
    exact (hζ.pow_eq_one_iff_dvd _).mpr hq2
  exact mul_self_eq_one_iff.mp h2

/-! ## §2. Translation closure -/

/-- The sign `ζ_q^h` read at the standard primitive root. -/
def lagSign (q h : ℕ) : ℝ := ((Complex.exp (2 * ↑Real.pi * Complex.I / ↑q)) ^ h).re

theorem pow_eq_lagSign {q h : ℕ} (hq : 0 < q) (hqh : q / Nat.gcd q 2 ∣ h) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) : ζ ^ h = (lagSign q h : ℂ) := by
  have hζ0 := Complex.isPrimitiveRoot_exp q hq.ne'
  rw [pow_eq_pow_of_div_gcd_two_dvd hq hqh hζ hζ0, lagSign]
  rcases pow_eq_one_or_neg_one_of_div_gcd_two_dvd hqh hζ0 with h1 | h1 <;> rw [h1] <;> simp

/-- **Translation closure at every lag.** The translate `k ↦ s_{N,c}(k + h)` is the response of a
row exactly when every active Selberg order `q` has `q / gcd(q, 2) ∣ h`. -/
theorem exists_row_translate_iff (N h : ℕ) (c : ℕ → ℝ) :
    (∃ c' : ℕ → ℝ, ∀ k, sieveSeq N c (k + h) = sieveSeq N c' k) ↔
      ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → q / Nat.gcd q 2 ∣ h := by
  constructor
  · rintro ⟨c', hc'⟩ q hq hY
    have hq0 := (mem_Icc.mp hq).1
    -- the spectral coefficients agree
    have hzero := eq_zero_of_sum_mul_pow_eq_zero (responseRoots N)
      (fun ζ => (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ h -
        (selbergMultiplesCoord N c' (orderOf ζ) : ℂ)) fun n => by
        have h1 := sieveSeq_eq_sum_responseRoots N c (n + h)
        have h2 := sieveSeq_eq_sum_responseRoots N c' n
        rw [hc' n, h2] at h1
        have h3 : ∑ ζ ∈ responseRoots N, ((selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ h -
            (selbergMultiplesCoord N c' (orderOf ζ) : ℂ)) * ζ ^ n =
            (∑ ζ ∈ responseRoots N, (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ζ ^ (n + h)) -
              ∑ ζ ∈ responseRoots N, (selbergMultiplesCoord N c' (orderOf ζ) : ℂ) * ζ ^ n := by
          rw [← sum_sub_distrib]
          exact sum_congr rfl fun ζ _ => by rw [pow_add]; ring
        rw [h3, ← h1, sub_self]
    refine div_gcd_two_dvd_of_pow_const hq0 fun ζ ξ hζ hξ => ?_
    have hζ' := hzero ζ (primitiveRoot_mem_responseRoots hq hζ)
    have hξ' := hzero ξ (primitiveRoot_mem_responseRoots hq hξ)
    rw [← hζ.eq_orderOf, sub_eq_zero] at hζ'
    rw [← hξ.eq_orderOf, sub_eq_zero] at hξ'
    have hYc : (selbergMultiplesCoord N c q : ℂ) ≠ 0 := by exact_mod_cast hY
    exact mul_left_cancel₀ hYc (hζ'.trans hξ'.symm)
  · intro hcond
    set a : ℕ → ℝ := fun q => selbergMultiplesCoord N c q * lagSign q h with ha
    refine ⟨RHTower.pmRamanujanResidueCoeff a N, fun k => ?_⟩
    apply Complex.ofReal_injective
    rw [sieveSeq_eq_sum_responseRoots, sieveSeq_eq_sum_responseRoots]
    refine sum_congr rfl fun ζ hζ => ?_
    have hord := orderOf_mem_Icc_of_mem_responseRoots hζ
    have hord0 := (mem_Icc.mp hord).1
    have hY' : selbergMultiplesCoord N (RHTower.pmRamanujanResidueCoeff a N) (orderOf ζ) =
        a (orderOf ζ) := RHTower.pmRamanujanResidueCoeff_multiples a hord0 (mem_Icc.mp hord).2
    rw [hY', ha, pow_add]
    by_cases hY : selbergMultiplesCoord N c (orderOf ζ) = 0
    · simp [hY]
    · rw [pow_eq_lagSign hord0 (hcond _ hord hY) (IsPrimitiveRoot.orderOf ζ)]
      push_cast
      ring

/-- At lag one the row space is closed exactly for Selberg support in `{1, 2}`. -/
theorem exists_row_succ_translate_iff (N : ℕ) (c : ℕ → ℝ) :
    (∃ c' : ℕ → ℝ, ∀ k, sieveSeq N c (k + 1) = sieveSeq N c' k) ↔
      ∀ q ∈ Icc 3 N, selbergMultiplesCoord N c q = 0 := by
  rw [exists_row_translate_iff]
  constructor
  · intro h q hq
    by_contra hY
    have hq' := mem_Icc.mp hq
    have hd := h q (mem_Icc.mpr ⟨by omega, hq'.2⟩) hY
    have hle := Nat.le_of_dvd one_pos hd
    have hpos : 0 < q / Nat.gcd q 2 := Nat.div_pos (Nat.le_of_dvd (by omega)
      (Nat.gcd_dvd_left q 2)) (Nat.gcd_pos_of_pos_left 2 (by omega))
    have hg : Nat.gcd q 2 ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right q 2)
    have : q ≤ 2 := by
      have h1 : q / Nat.gcd q 2 = 1 := by omega
      have := Nat.div_mul_cancel (Nat.gcd_dvd_left q 2)
      rw [h1, one_mul] at this
      omega
    omega
  · intro h q hq hY
    obtain ⟨hq1, hqN⟩ := mem_Icc.mp hq
    rcases Nat.lt_or_ge q 3 with h3 | h3
    · interval_cases q <;> simp
    · exact absurd (h q (mem_Icc.mpr ⟨h3, hqN⟩)) hY

end

end GaloisForLFunctions.BezoutValuationIncidence
