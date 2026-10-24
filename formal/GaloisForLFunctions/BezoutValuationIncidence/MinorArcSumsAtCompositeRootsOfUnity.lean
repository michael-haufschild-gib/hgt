import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeRowIsMinorArcBelowTheDiagonal

/-!
# Minor-arc sums at roots of unity of composite order

The minor-arc laws for `Σ μ(n) wⁿ` and `Σ Λ(n) wⁿ` hold at a primitive `r`-th root of unity `w` of
any order `r`. The Type-II part and the `log`-weighted Type-I part go through verbatim (they only use
that `w` is primitive). The double Type-I sum `Σ_{d₁,d₂ ≤ U} f(d₁) c(d₂) Σ_m w^{d₁d₂m}` changes:
for composite `r` the product `d₁d₂` may be divisible by `r` although `d₁, d₂ < r`.

* If `r ∣ d₁d₂` then `d₁d₂ ≥ r` and the inner sum is at most `N/r`; there are at most `U²` such pairs.
* Otherwise `ξ = w^{d₁}` is a primitive root of order `r' = ord(ξ) ∣ r`, and the residue-class count
  gives `Σ_{d₂ ≤ U} 2/|ξ^{d₂} - 1| ≤ (U/r' + 1) W_{r'} ≤ (U + r)(1 + log r)`.

Hence the double Type-I sum is at most `U F (U N/r + (U + r)(1 + log r))` for `|f| ≤ F`, `|c| ≤ 1`
supported on `[1, U]` (`norm_sum_conv_conv_zeta_le_of_isPrimitiveRoot`), and

`‖Σ_{n ≤ N} μ(n) wⁿ‖ ≤ 2U + U(UN/r + (U + r)(1 + log r)) + (log₂ N + 1) √(typeIIBlockBound r U N)`

(`norm_sum_moebius_mul_pow_le_of_isPrimitiveRoot`), with the analogous law for `Λ` when `U < r`.
-/

open Finset ArithmeticFunction RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The double Type-I sum at a root of any order -/

/-- `Σ_{n ≤ N} (f ∗ c ∗ 1)(n) wⁿ = Σ_{d ≤ N} f(d) Σ_{k ≤ N/d} c(k) Σ_{m ≤ N/(dk)} (w^{dk})^m`. -/
theorem sum_Icc_conv_conv_zeta_mul_pow (f c : ArithmeticFunction ℝ) (w : ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((f * c * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w ^ n =
      ∑ d ∈ Icc 1 N, (f d : ℂ) * ∑ k ∈ Icc 1 (N / d), (c k : ℂ) *
        ∑ m ∈ Icc 1 ((N / d) / k), ((w ^ d) ^ k) ^ m := by
  set G : ℕ → ℂ := fun e => ∑ m ∈ Icc 1 (N / e), (w ^ e) ^ m
  have h1 : ∑ n ∈ Icc 1 N, (((f * c * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w ^ n =
      ∑ e ∈ Icc 1 N, (((f * c) e : ℝ) : ℂ) * G e := by
    rw [sum_Icc_mul_conv]
    refine sum_congr rfl fun e _ => ?_
    simp only [G, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [natCoe_apply, zeta_apply, if_neg (by have := (mem_Icc.mp hm).1; omega), pow_mul]
    push_cast
    ring
  rw [h1, sum_Icc_mul_conv]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [G, Nat.div_div_eq_div_mul, ← pow_mul]
  push_cast
  ring

/-- **The inner Type-I sum at a root of any order.** For an `r`-th root of unity `ξ`, `c`
supported on `[1, U]` with `|c| ≤ 1`, and `M ≤ N/d` with `ξ = w^d`, the inner sum
`Σ_{k ≤ M} c(k) Σ_{m ≤ M/k} (ξ^k)^m` is at most `U N/r + (U + r)(1 + log r)`. -/
theorem norm_inner_typeI_le {r : ℕ} (hr : 0 < r) {w : ℂ} (hw : IsPrimitiveRoot w r) {U : ℕ}
    (c : ArithmeticFunction ℝ) (hc : ∀ b, |c b| ≤ 1) (hcs : ∀ b, U < b → c b = 0)
    {N d : ℕ} (hd : 1 ≤ d) :
    ‖∑ k ∈ Icc 1 (N / d), (c k : ℂ) * ∑ m ∈ Icc 1 ((N / d) / k), ((w ^ d) ^ k) ^ m‖ ≤
      U * N / r + (U + r) * (1 + Real.log r) := by
  have hnorm : ‖w‖ = 1 := hw.norm'_eq_one hr.ne'
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set ξ := w ^ d
  have hξr : ξ ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
  have hξn : ‖ξ‖ = 1 := by rw [norm_pow, hnorm, one_pow]
  have hr'dvd : orderOf ξ ∣ r := orderOf_dvd_of_pow_eq_one hξr
  have hr'0 : 0 < orderOf ξ := Nat.pos_of_ne_zero fun h => by
    rw [h] at hr'dvd; exact hr.ne' (Nat.eq_zero_of_zero_dvd hr'dvd)
  have hr'le : orderOf ξ ≤ r := Nat.le_of_dvd hr hr'dvd
  have hk : ∀ k ∈ Icc 1 (N / d), ‖(c k : ℂ) * ∑ m ∈ Icc 1 ((N / d) / k), (ξ ^ k) ^ m‖ ≤
      if k ≤ U then (N : ℝ) / r + geomMajorant 0 (ξ ^ k) else 0 := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hkU
    · have hGM : 0 ≤ geomMajorant 0 (ξ ^ k) := geomMajorant_nonneg le_rfl _
      have hNr : (0 : ℝ) ≤ (N : ℝ) / r := by positivity
      refine (mul_le_of_le_one_left (norm_nonneg _) (hc k)).trans ?_
      by_cases h1 : ξ ^ k = 1
      · -- `r ∣ dk`, so the full geometric sum has `N/(dk) ≤ N/r` terms
        have hdk : r ∣ d * k := by rw [← hw.pow_eq_one_iff_dvd, pow_mul]; exact h1
        have hdkr : (r : ℝ) ≤ d * k := by exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hd hk1) hdk
        rw [h1]
        simp only [one_pow, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
          mul_one, Complex.norm_natCast]
        rw [show geomMajorant 0 1 = 0 by simp [geomMajorant]]
        have hM : (((N / d) / k : ℕ) : ℝ) ≤ (N : ℝ) / r := by
          rw [Nat.div_div_eq_div_mul]
          refine Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hrR ?_)
          exact_mod_cast hdkr
        linarith
      · have h := GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_sum_Icc_pow_le
          (by rw [norm_pow, hξn, one_pow]) h1 ((N / d) / k)
        rw [geomMajorant, if_neg h1]
        linarith
    · rw [hcs k (by omega)]; simp
  have hres : ∑ k ∈ Icc 1 U, geomMajorant 0 (ξ ^ k) ≤ (U + r) * (1 + Real.log r) := by
    have hIoc : Icc 1 U = Ioc 0 (0 + U) := by rw [zero_add]; exact Finset.Icc_add_one_left_eq_Ioc 0 U
    have h := sum_Ioc_root_mul_pow_le hr'0 (IsPrimitiveRoot.orderOf ξ) (one_pow _)
      (geomMajorant 0) (geomMajorant_nonneg le_rfl) 0 U
    simp only [one_mul] at h
    rw [hIoc]
    refine h.trans ?_
    rw [sum_nthRootsFinset_geomMajorant hr'0, zero_add]
    have hW := rootHarmonicSum_le (orderOf ξ)
    have hr'R : (0 : ℝ) < orderOf ξ := by exact_mod_cast hr'0
    have hr'leR : (orderOf ξ : ℝ) ≤ r := by exact_mod_cast hr'le
    have hlog : Real.log (orderOf ξ) ≤ Real.log r := Real.log_le_log hr'R hr'leR
    have hlog0 : 0 ≤ Real.log (orderOf ξ) := Real.log_natCast_nonneg _
    calc ((U : ℝ) / orderOf ξ + 1) * rootHarmonicSum (orderOf ξ)
        ≤ ((U : ℝ) / orderOf ξ + 1) * (orderOf ξ * (1 + Real.log r)) :=
          mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_left (by linarith)
            hr'R.le)) (by positivity)
      _ = (U + orderOf ξ) * (1 + Real.log r) := by field_simp
      _ ≤ (U + r) * (1 + Real.log r) := by gcongr
  calc ‖∑ k ∈ Icc 1 (N / d), (c k : ℂ) * ∑ m ∈ Icc 1 ((N / d) / k), (ξ ^ k) ^ m‖
      ≤ ∑ k ∈ Icc 1 (N / d), (if k ≤ U then (N : ℝ) / r + geomMajorant 0 (ξ ^ k) else 0) :=
        (norm_sum_le _ _).trans (sum_le_sum hk)
    _ ≤ ∑ k ∈ Icc 1 U, ((N : ℝ) / r + geomMajorant 0 (ξ ^ k)) := by
        rw [← sum_filter]
        exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
          simp only [mem_filter, mem_Icc] at hk ⊢; omega) fun k _ _ => by
          have := geomMajorant_nonneg le_rfl (ξ ^ k); positivity
    _ = U * ((N : ℝ) / r) + ∑ k ∈ Icc 1 U, geomMajorant 0 (ξ ^ k) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ U * N / r + (U + r) * (1 + Real.log r) := by
        rw [mul_div_assoc]
        linarith

/-- **The double Type-I sum at a root of any order.** For `f` supported on `[1, U]` with
`|f| ≤ F` and `c` supported on `[1, U]` with `|c| ≤ 1`,
`‖Σ_{n ≤ N} (f ∗ c ∗ 1)(n) wⁿ‖ ≤ U F (U N/r + (U + r)(1 + log r))`. -/
theorem norm_sum_conv_conv_zeta_le_of_isPrimitiveRoot {r : ℕ} (hr : 0 < r) {w : ℂ}
    (hw : IsPrimitiveRoot w r) {U : ℕ} (f c : ArithmeticFunction ℝ) {F : ℝ} (hf : ∀ a, |f a| ≤ F)
    (hfs : ∀ a, U < a → f a = 0) (hc : ∀ b, |c b| ≤ 1) (hcs : ∀ b, U < b → c b = 0) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (((f * c * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w ^ n‖ ≤
      U * F * (U * N / r + (U + r) * (1 + Real.log r)) := by
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hf 0)
  have hX0 : 0 ≤ (U : ℝ) * N / r + (U + r) * (1 + Real.log r) := by
    have := Real.log_natCast_nonneg r
    positivity
  rw [sum_Icc_conv_conv_zeta_mul_pow]
  have hterm : ∀ d ∈ Icc 1 N, ‖(f d : ℂ) * ∑ k ∈ Icc 1 (N / d), (c k : ℂ) *
      ∑ m ∈ Icc 1 ((N / d) / k), ((w ^ d) ^ k) ^ m‖ ≤
      if d ≤ U then F * (U * N / r + (U + r) * (1 + Real.log r)) else 0 := by
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hdU
    · exact mul_le_mul (hf d) (norm_inner_typeI_le hr hw c hc hcs (mem_Icc.mp hd).1)
        (norm_nonneg _) hF0
    · rw [hfs d (by omega), abs_zero, zero_mul]
  calc _ ≤ ∑ d ∈ Icc 1 N, (if d ≤ U then F * (U * N / r + (U + r) * (1 + Real.log r)) else 0) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ ≤ U * (F * (U * N / r + (U + r) * (1 + Real.log r))) :=
        sum_Icc_ite_le_le N U (mul_nonneg hF0 hX0)
    _ = U * F * (U * N / r + (U + r) * (1 + Real.log r)) := by ring

/-! ## §2. The minor-arc laws at a root of any order -/

/-- The composite minor-arc majorant
`2U + U (U N/r + (U + r)(1 + log r)) + (log₂ N + 1) √(typeIIBlockBound r U N)`. -/
def compositeMinorArcBound (r U N : ℕ) : ℝ :=
  2 * U + U * (U * N / r + (U + r) * (1 + Real.log r)) +
    (Nat.log 2 N + 1) * Real.sqrt (typeIIBlockBound r U N)

/-- **The minor-arc law for Möbius at a primitive root of any order.** -/
theorem norm_sum_moebius_mul_pow_le_of_isPrimitiveRoot {r : ℕ} (hr : 0 < r) {w : ℂ}
    (hw : IsPrimitiveRoot w r) {U : ℕ} (hU : 1 ≤ U) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (moebiusReal n : ℂ) * w ^ n‖ ≤ compositeMinorArcBound r U N := by
  have hnorm : ‖w‖ = 1 := hw.norm'_eq_one hr.ne'
  have hb : ∀ k, |truncAF (moebius : ArithmeticFunction ℝ) U k| ≤ 1 := fun k =>
    (abs_truncAF_moebius_le U k).trans (by split_ifs <;> norm_num)
  have hs : ∀ k, U < k → truncAF (moebius : ArithmeticFunction ℝ) U k = 0 := fun k hk =>
    truncAF_apply_of_gt hk
  have hB := norm_sum_conv_conv_zeta_le_of_isPrimitiveRoot hr hw _ _ hb hs hb hs N
  have hC := norm_sum_moebius_typeII_le hr hw hU N
  have h := norm_sum_moebius_mul_pow_le_split hnorm U N
  unfold compositeMinorArcBound
  linarith

/-- The composite prime majorant `U log U + U log U (U N/r + (U + r)(1 + log r)) + 2 log N · W_r
+ (log₂ N + 1)(1 + log N) √(typeIIBlockBound r U N)`. -/
def compositePrimeMinorArcBound (r U N : ℕ) : ℝ :=
  U * Real.log U + U * Real.log U * (U * N / r + (U + r) * (1 + Real.log r)) +
    2 * Real.log N * rootHarmonicSum r +
    (Nat.log 2 N + 1) * (1 + Real.log N) * Real.sqrt (typeIIBlockBound r U N)

/-- **The minor-arc law for `Λ` at a primitive root of any order** `r > U`. -/
theorem norm_sum_vonMangoldt_mul_pow_le_of_isPrimitiveRoot {r : ℕ} (hr : 0 < r) {w : ℂ}
    (hw : IsPrimitiveRoot w r) {U : ℕ} (hU : 1 ≤ U) (hUr : U < r) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((vonMangoldt n : ℝ) : ℂ) * w ^ n‖ ≤ compositePrimeMinorArcBound r U N := by
  have hnorm : ‖w‖ = 1 := hw.norm'_eq_one hr.ne'
  have hμU : ∀ b, |truncAF (moebius : ArithmeticFunction ℝ) U b| ≤ 1 := fun b =>
    (abs_truncAF_moebius_le U b).trans (by split_ifs <;> norm_num)
  have h2 := norm_sum_conv_conv_zeta_le_of_isPrimitiveRoot hr hw (truncAF vonMangoldt U)
    (truncAF (moebius : ArithmeticFunction ℝ) U) (abs_truncAF_vonMangoldt_le U)
    (fun a ha => truncAF_apply_of_gt ha) hμU (fun b hb => truncAF_apply_of_gt hb) N
  have h3 := norm_sum_truncAF_moebius_mul_log_le hr hw hUr N
  have h4 := norm_sum_vonMangoldt_typeII_le hr hw hU N
  have h := norm_sum_vonMangoldt_mul_pow_le_split hnorm U N
  unfold compositePrimeMinorArcBound
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
