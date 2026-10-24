import GaloisForLFunctions.BezoutValuationIncidence.TheDiagonalDualNormIsArchimedean
import GaloisForLFunctions.BezoutValuationIncidence.CentredPrimeBlockBeatsTheLargeSieve
import GaloisForLFunctions.RHTower.Sieve.AbelIcoWeight
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The centred prime row: minor arcs below the diagonal, the archimedean place on it

The dichotomy of the Möbius row holds for `c' = (Λ - 1)·𝟙_{(Q,2Q]}`.

* **Minor arcs.** Vaughan's identity with `U = V < p`,
  `Λ = Λ_U - Λ_U ∗ μ_U ∗ 1 + μ_U ∗ log + (Λ - Λ_U) ∗ g`, splits `Σ_{n ≤ N} Λ(n) ζⁿ` into a short sum,
  two Type-I sums at the prime denominator (the second carries the increasing weight `log m`,
  removed by Abel summation) and a Type-II sum whose long coefficients satisfy `|Λ| ≤ 1 + log N`:
  `‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ U log U (1 + W_p) + 2 log N · W_p + (log₂ N + 1)(1 + log N) √(typeIIBlockBound p U N)`
  (`norm_sum_vonMangoldt_mul_pow_le`). The constant `1` adds a geometric sum `≤ p/2`. At every prime
  `Q^δ ≤ p ≤ Q^{1-δ}` this gives `|Λ_p(c')| ≤ 24 (1 + log 2Q)⁴ (p²/Q) Q^{-δ/4}`
  (`abs_kernelStatistic_centredPrimeBlock_le_rpow`). The omitted residue class `0 mod p` of the
  primes has relative size `1/p ≤ Q^{-δ}` and lies inside this saving.
* **The diagonal.** The long-window partial sums of `c'` are `ψ(Q + x) - ψ(Q) - x`; the prime number
  theorem with error term gives `|Λ_d(c')| ≤ C (d²/Q) e^{-(c/2)√(log Q)}` at every balanced modulus
  `Q/K ≤ d ≤ 2Q` (`exists_balanced_kernelStatisticAll_centredPrimeBlock_le`).
-/

open Finset Filter Topology ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The minor-arc law for `Λ` at prime roots of unity -/

/-- `Σ_{1 ≤ m ≤ M} log m · wᵐ` for `‖w‖ = 1`, `w ≠ 1`: at most `2 log M · 2/‖w - 1‖`. -/
theorem norm_sum_Icc_log_mul_pow_le {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (M : ℕ) :
    ‖∑ m ∈ Icc 1 M, ((Real.log m : ℝ) : ℂ) * w ^ m‖ ≤ 2 * (2 / ‖w - 1‖) * Real.log M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hIcc : ∀ k, Ico 1 (1 + k) = Icc 1 k := fun k => by ext i; simp only [mem_Ico, mem_Icc]; omega
  have h := norm_sum_Ico_mul_le_of_bounded_partial_mono (A := 1) (B := M + 1) (by omega)
    (fun i => Real.log i) (fun i => w ^ i) (Bd := 2 / ‖w - 1‖) (by simp)
    (fun i hi => Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by push_cast; linarith))
    (fun k _ => by
      rw [hIcc]
      exact GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_sum_Icc_pow_le hw.le hw1 k)
  rwa [show Ico 1 (M + 1) = Icc 1 M by rw [add_comm]; exact hIcc M, Nat.add_sub_cancel] at h

/-- **Vaughan's identity with `U = V`**, in the order used here. -/
theorem vonMangoldt_eq_vaughan_decomposition (U : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) =
      truncAF vonMangoldt U - truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) U *
          (zeta : ArithmeticFunction ℝ) +
        truncAF (moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log +
        typeIILong U * typeIIShort U := by
  have h := vaughan_identity U U
  unfold typeIILong typeIIShort
  linear_combination h

theorem real_log_natCast_mono {M N : ℕ} (h : M ≤ N) : Real.log M ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast h)

/-- The prime minor-arc majorant
`U log U (1 + W_p) + 2 log N · W_p + (log₂ N + 1)(1 + log N) √(typeIIBlockBound p U N)`. -/
def primeMinorArcBound (p U N : ℕ) : ℝ :=
  U * Real.log U * (1 + rootHarmonicSum p) + 2 * Real.log N * rootHarmonicSum p +
    (Nat.log 2 N + 1) * (1 + Real.log N) * Real.sqrt (typeIIBlockBound p U N)

theorem primeMinorArcBound_mono (p U : ℕ) {M N : ℕ} (h : M ≤ N) :
    primeMinorArcBound p U M ≤ primeMinorArcBound p U N := by
  unfold primeMinorArcBound
  have hW := rootHarmonicSum_nonneg p
  have hlog := real_log_natCast_mono h
  have hlogM := Real.log_natCast_nonneg M
  have hNlog : (Nat.log 2 M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast Nat.log_mono_right h
  have hsq := Real.sqrt_le_sqrt (typeIIBlockBound_mono p U h)
  gcongr

/-- The short sum `‖Σ_{n ≤ N} Λ_U(n) ζⁿ‖ ≤ U log U` on the unit circle. -/
theorem norm_sum_truncAF_vonMangoldt_le {ζ : ℂ} (hnorm : ‖ζ‖ = 1) (U N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((truncAF vonMangoldt U n : ℝ) : ℂ) * ζ ^ n‖ ≤ U * Real.log U := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Icc 1 N, ‖((truncAF vonMangoldt U n : ℝ) : ℂ) * ζ ^ n‖
      ≤ ∑ n ∈ Icc 1 N, (if n ≤ U then Real.log U else 0) := by
        refine sum_le_sum fun n hn => ?_
        rw [norm_mul, norm_pow, hnorm, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
          truncAF_apply]
        split_ifs with hnU
        · rw [abs_of_nonneg vonMangoldt_nonneg]
          exact vonMangoldt_le_log.trans
            (Real.log_le_log (Nat.cast_pos.mpr (by have := (mem_Icc.mp hn).1; omega))
              (by exact_mod_cast hnU))
        · simp
    _ ≤ U * Real.log U := sum_Icc_ite_le_le N U (Real.log_natCast_nonneg U)

/-- **The `log`-weighted Type-I sum.** For `U < p`,
`‖Σ_{n ≤ N} (μ_U ∗ log)(n) ζⁿ‖ ≤ 2 log N · W_p`. -/
theorem norm_sum_truncAF_moebius_mul_log_le {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hprim : IsPrimitiveRoot ζ p) {U : ℕ} (hUp : U < p) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (((truncAF (moebius : ArithmeticFunction ℝ) U *
      ArithmeticFunction.log) n : ℝ) : ℂ) * ζ ^ n‖ ≤ 2 * Real.log N * rootHarmonicSum p := by
  have hnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one hp.ne_zero
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hμU : ∀ b, |truncAF (moebius : ArithmeticFunction ℝ) U b| ≤ 1 := fun b =>
    (abs_truncAF_moebius_le U b).trans (by split_ifs <;> norm_num)
  rw [sum_Icc_mul_conv]
  have hterm : ∀ b ∈ Icc 1 N, ‖∑ k ∈ Icc 1 (N / b), ((truncAF (moebius : ArithmeticFunction ℝ) U b *
      ArithmeticFunction.log k : ℝ) : ℂ) * ζ ^ (b * k)‖ ≤
      if b ≤ U then 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) else 0 := by
    intro b hb
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
    split_ifs with hbU
    · have hne : ζ ^ b ≠ 1 := fun h => Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hb).1 (by omega)
        ((hprim.pow_eq_one_iff_dvd b).mp h)
      have hw : ‖ζ ^ b‖ = 1 := by rw [norm_pow, hnorm, one_pow]
      have hinner := norm_sum_Icc_log_mul_pow_le hw hne (N / b)
      have hlog' : Real.log (N / b : ℕ) ≤ Real.log N := real_log_natCast_mono (Nat.div_le_self N b)
      calc |truncAF (moebius : ArithmeticFunction ℝ) U b| *
            ‖∑ k ∈ Icc 1 (N / b), ((Real.log k : ℝ) : ℂ) * (ζ ^ b) ^ k‖
          ≤ 1 * (2 * (2 / ‖ζ ^ b - 1‖) * Real.log N) :=
            mul_le_mul (hμU b) (hinner.trans (mul_le_mul_of_nonneg_left hlog' (by positivity)))
              (norm_nonneg _) zero_le_one
        _ = 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) := by ring
    · rw [truncAF_apply_of_gt (by omega), abs_zero, zero_mul]
  calc _ ≤ ∑ b ∈ Icc 1 N, (if b ≤ U then 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) else 0) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = ∑ b ∈ (Icc 1 N).filter (· ≤ U), 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) := (sum_filter _ _).symm
    _ ≤ ∑ b ∈ Icc 1 U, 2 * Real.log N * (2 / ‖ζ ^ b - 1‖) :=
        sum_le_sum_of_subset_of_nonneg (fun b hb => by
          simp only [mem_filter, mem_Icc] at hb ⊢; omega) fun _ _ _ => by positivity
    _ = 2 * Real.log N * ∑ b ∈ Icc 1 U, 2 / ‖ζ ^ b - 1‖ := by rw [mul_sum]
    _ ≤ 2 * Real.log N * rootHarmonicSum p :=
        mul_le_mul_of_nonneg_left (sum_Icc_two_div_norm_pow_sub_one_le hp hprim hUp)
          (by positivity)

/-- **The minor-arc law for `Λ` at prime roots of unity.** For `p` prime, `ζ ≠ 1` a `p`-th root of
unity and `1 ≤ U < p`, `‖Σ_{n ≤ N} Λ(n) ζⁿ‖ ≤ primeMinorArcBound p U N`. -/
theorem norm_sum_vonMangoldt_mul_pow_le {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : ζ ∈ nontrivialRoots p) {U : ℕ} (hU : 1 ≤ U) (hUp : U < p) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((vonMangoldt n : ℝ) : ℂ) * ζ ^ n‖ ≤ primeMinorArcBound p U N := by
  have hprim := isPrimitiveRoot_of_mem_nontrivialRoots hp hζ
  have hnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one hp.ne_zero
  have hlogU : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hdec : ∀ n, ((vonMangoldt n : ℝ) : ℂ) =
      ((truncAF vonMangoldt U n : ℝ) : ℂ) -
        (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) U *
          (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) +
        (((truncAF (moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ) +
        (((typeIILong U * typeIIShort U) n : ℝ) : ℂ) := by
    intro n
    have h : (vonMangoldt : ArithmeticFunction ℝ) n =
        truncAF vonMangoldt U n - (truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) U *
          (zeta : ArithmeticFunction ℝ)) n +
        (truncAF (moebius : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n +
        (typeIILong U * typeIIShort U) n :=
      congrArg (fun f : ArithmeticFunction ℝ => f n) (vonMangoldt_eq_vaughan_decomposition U)
    rw [h]
    push_cast
    ring
  rw [sum_congr rfl fun n _ => by rw [hdec n]]
  simp_rw [add_mul, sub_mul]
  rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib]
  have h1 := norm_sum_truncAF_vonMangoldt_le hnorm U N
  -- the first Type-I sum
  have hΛU : ∀ a, |truncAF vonMangoldt U a| ≤ Real.log U := fun a => by
    rw [truncAF_apply]
    split_ifs with haU
    · rw [abs_of_nonneg vonMangoldt_nonneg]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp [hlogU]
      · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast haU))
    · simp [hlogU]
  have hμU : ∀ b, |truncAF (moebius : ArithmeticFunction ℝ) U b| ≤ 1 := fun b =>
    (abs_truncAF_moebius_le U b).trans (by split_ifs <;> norm_num)
  have h2 := norm_sum_conv_conv_zeta_le hp hprim hUp hUp (truncAF vonMangoldt U)
    (truncAF (moebius : ArithmeticFunction ℝ) U) hΛU (fun a ha => truncAF_apply_of_gt ha) hμU
    (fun b hb => truncAF_apply_of_gt hb) N
  have h3 := norm_sum_truncAF_moebius_mul_log_le hp hprim hUp N
  -- the Type-II sum, with long coefficients `|Λ| ≤ 1 + log N`
  have h4 : ‖∑ n ∈ Icc 1 N, (((typeIILong U * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n‖ ≤
      (Nat.log 2 N + 1) * (1 + Real.log N) * Real.sqrt (typeIIBlockBound p U N) := by
    rw [sum_Icc_mul_conv]
    refine norm_sum_typeIIShort_le hp hprim hU N (typeIILong U) (by positivity) (fun d hd => ?_)
      (fun d hd => ?_)
    · refine (abs_vonMangoldt_sub_truncAF_le U d).trans ?_
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp only [ArithmeticFunction.map_zero]; positivity
      · exact vonMangoldt_le_log.trans ((real_log_natCast_mono hd).trans (by linarith))
    · show vonMangoldt d - truncAF vonMangoldt U d = 0
      rw [truncAF_apply, if_pos hd, sub_self]
  unfold primeMinorArcBound
  calc _ ≤ ‖∑ n ∈ Icc 1 N, ((truncAF vonMangoldt U n : ℝ) : ℂ) * ζ ^ n‖ +
        ‖∑ n ∈ Icc 1 N, (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) U *
          (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * ζ ^ n‖ +
        ‖∑ n ∈ Icc 1 N, (((truncAF (moebius : ArithmeticFunction ℝ) U *
          ArithmeticFunction.log) n : ℝ) : ℂ) * ζ ^ n‖ +
        ‖∑ n ∈ Icc 1 N, (((typeIILong U * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-! ## §2. The centred prime row below the diagonal -/

theorem centredPrimeBlock_ne_zero_imp {Q n : ℕ} (h : centredPrimeBlock Q n ≠ 0) :
    Q < n ∧ n ≤ 2 * Q := by
  unfold centredPrimeBlock at h
  split_ifs at h with hn
  · exact hn
  · exact absurd rfl h

/-- **The kernel statistic of the centred prime row through the minor-arc law.** For `p` prime,
`1 ≤ U < p` and `N ≥ 2Q`, `|Λ_p((Λ - 1)𝟙_{(Q,2Q]})| ≤
(π²(p² - 1)/72 (Q+1)^{-2} + π²p³/48 (Q+1)^{-3}) (2 primeMinorArcBound p U 2Q + p/2)`. -/
theorem abs_kernelStatistic_centredPrimeBlock_le_minorArc {p : ℕ} (hp : p.Prime) {U : ℕ}
    (hU : 1 ≤ U) (hUp : U < p) {Q N : ℕ} (hQN : 2 * Q ≤ N) :
    |kernelStatistic N (centredPrimeBlock Q) p| ≤
      (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 / ((Q : ℝ) + 1) ^ 2 +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 / ((Q : ℝ) + 1) ^ 3) *
        (2 * primeMinorArcBound p U (2 * Q) + p / 2) := by
  set B' := 2 * primeMinorArcBound p U (2 * Q) + (p : ℝ) / 2
  have hsupp : ∀ n, centredPrimeBlock Q n ≠ 0 → Q < n ∧ n ≤ 2 * Q :=
    fun n h => centredPrimeBlock_ne_zero_imp h
  have htw : ∀ ζ ∈ nontrivialRoots p, ∀ k ≤ Q,
      ‖∑ i ∈ range k, ((centredPrimeBlock Q (Q + 1 + i) : ℝ) : ℂ) * ζ ^ (Q + 1 + i)‖ ≤ B' := by
    intro ζ hζ k hk
    set S : ℕ → ℂ := fun x => ∑ n ∈ Icc 1 x, ((vonMangoldt n : ℝ) : ℂ) * ζ ^ n
    have hdiff : ∑ i ∈ range k, ((centredPrimeBlock Q (Q + 1 + i) : ℝ) : ℂ) * ζ ^ (Q + 1 + i) =
        (S (Q + k) - S Q) - ζ ^ Q * ∑ i ∈ range k, ζ ^ (i + 1) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ,
          show Q + (k + 1) = (Q + k) + 1 by ring]
        simp only [S]
        rw [sum_Icc_succ_top (by omega : 1 ≤ Q + k + 1), show Q + 1 + k = Q + k + 1 by ring,
          centredPrimeBlock, if_pos (by omega)]
        push_cast
        ring
    have hnorm := norm_eq_one_of_mem_nontrivialRoots hp.pos hζ
    have hgeo : ‖ζ ^ Q * ∑ i ∈ range k, ζ ^ (i + 1)‖ ≤ (p : ℝ) / 2 := by
      have hne : ζ ≠ 1 := ((mem_nontrivialRoots hp.pos).mp hζ).1
      have h4 := four_div_le_norm_sub_one_of_mem_nontrivialRoots hp.pos hζ
      have hpos : 0 < ‖ζ - 1‖ :=
        lt_of_lt_of_le (div_pos (by norm_num) (by exact_mod_cast hp.pos)) h4
      rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]
      refine (GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le hnorm.le hne k).trans ?_
      rw [div_le_div_iff₀ hpos (by norm_num)]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [div_le_iff₀ hp0] at h4
      linarith
    have hS : ∀ x ≤ 2 * Q, ‖S x‖ ≤ primeMinorArcBound p U (2 * Q) := fun x hx =>
      (norm_sum_vonMangoldt_mul_pow_le hp hζ hU hUp x).trans (primeMinorArcBound_mono p U hx)
    rw [hdiff]
    calc ‖S (Q + k) - S Q - ζ ^ Q * ∑ i ∈ range k, ζ ^ (i + 1)‖
        ≤ ‖S (Q + k)‖ + ‖S Q‖ + ‖ζ ^ Q * ∑ i ∈ range k, ζ ^ (i + 1)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ primeMinorArcBound p U (2 * Q) + primeMinorArcBound p U (2 * Q) + (p : ℝ) / 2 :=
          add_le_add (add_le_add (hS _ (by omega)) (hS _ (by omega))) hgeo
      _ = B' := by ring
  have hB'0 : 0 ≤ B' := by
    have : 0 ≤ primeMinorArcBound p U (2 * Q) := by
      unfold primeMinorArcBound
      have := rootHarmonicSum_nonneg p
      have := Real.log_natCast_nonneg U
      have := Real.log_natCast_nonneg (2 * Q)
      positivity
    positivity
  have h2 : rowTransformMax N (centredPrimeBlock Q) p ≤ B' / ((Q : ℝ) + 1) ^ 2 :=
    rowTransformMax_le_of_forall (by positivity) fun ζ hζ =>
      norm_sum_window_div_pow_le_of_twisted Q N 2 hQN hsupp ζ (htw ζ hζ)
  have h3 : cubicRowTransformMax N (centredPrimeBlock Q) p ≤ B' / ((Q : ℝ) + 1) ^ 3 :=
    cubicRowTransformMax_le_of_forall (by positivity) fun ζ hζ =>
      norm_sum_window_div_pow_le_of_twisted Q N 3 hQN hsupp ζ (htw ζ hζ)
  have hp1 : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  refine (abs_kernelStatistic_le_fourier hp N _).trans ?_
  calc Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * rowTransformMax N (centredPrimeBlock Q) p +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * cubicRowTransformMax N (centredPrimeBlock Q) p
      ≤ Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * (B' / ((Q : ℝ) + 1) ^ 2) +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * (B' / ((Q : ℝ) + 1) ^ 3) := by gcongr
    _ = _ := by ring

/-- **The power saving for the centred prime row below the diagonal.** For `Q ≥ 2`, `0 < δ < 1`,
every prime `Q^δ ≤ p ≤ Q^{1-δ}` and `N ≥ 2Q`,
`|Λ_p((Λ - 1)𝟙_{(Q,2Q]})| ≤ 24 (1 + log 2Q)⁴ (p²/Q) Q^{-δ/4}`. -/
theorem abs_kernelStatistic_centredPrimeBlock_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {Q : ℕ} (hQ : 2 ≤ Q) {p : ℕ} (hp : p.Prime) (hpl : (Q : ℝ) ^ δ ≤ p)
    (hpu : (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ} (hQN : 2 * Q ≤ N) :
    |kernelStatistic N (centredPrimeBlock Q) p| ≤
      24 * (1 + Real.log (2 * Q)) ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
  obtain ⟨U, hU1, hUp, hUT, hlogU, hWT, hUW, hpT, hsq⟩ := exists_minorArc_cutoff hδ hδ1 hQ hp hpl hpu
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hlog2Q : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  set T := (Q : ℝ) * (Q : ℝ) ^ (-(δ / 4))
  have hT0 : 0 ≤ T := mul_nonneg hq0.le (Real.rpow_nonneg hq0.le _)
  have hcast : ((2 * Q : ℕ) : ℝ) = 2 * (Q : ℝ) := by push_cast; ring
  have hlogU0 : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  have hW0 := rootHarmonicSum_nonneg p
  have hM : primeMinorArcBound p U (2 * Q) ≤ 34 * L ^ 4 * T := by
    unfold primeMinorArcBound
    rw [hcast]
    have hlogL : Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith
    have hL2 : L ≤ L ^ 2 := le_self_pow₀ hL1 (by norm_num)
    have hL4 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    have t1 : (U : ℝ) * Real.log U * (1 + rootHarmonicSum p) ≤ 2 * L ^ 2 * T := by
      have : (U : ℝ) * Real.log U * (1 + rootHarmonicSum p) =
          Real.log U * U + Real.log U * (U * rootHarmonicSum p) := by ring
      rw [this]
      have a : Real.log U * U ≤ L * T := mul_le_mul hlogU hUT (Nat.cast_nonneg _) (by linarith)
      have b : Real.log U * (U * rootHarmonicSum p) ≤ L * (L * T) :=
        mul_le_mul hlogU hUW (by positivity) (by linarith)
      linarith [mul_le_mul_of_nonneg_right hL2 hT0]
    have t2 : 2 * Real.log (2 * (Q : ℝ)) * rootHarmonicSum p ≤ 2 * L ^ 2 * T := by
      have := mul_le_mul hlogL hWT hW0 (by linarith)
      linarith
    have t3 : ((Nat.log 2 (2 * Q) : ℝ) + 1) * (1 + Real.log (2 * (Q : ℝ))) *
        Real.sqrt (typeIIBlockBound p U (2 * Q)) ≤ 30 * L ^ 4 * T := by
      have h0 : 0 ≤ ((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound p U (2 * Q)) := by
        positivity
      calc ((Nat.log 2 (2 * Q) : ℝ) + 1) * (1 + Real.log (2 * (Q : ℝ))) *
            Real.sqrt (typeIIBlockBound p U (2 * Q))
          = L * (((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound p U (2 * Q))) := by
            rw [hLdef]; ring
        _ ≤ L * (30 * L ^ 3 * T) := mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = 30 * L ^ 4 * T := by ring
    linarith [mul_le_mul_of_nonneg_right hL4 hT0]
  have hpq : (p : ℝ) ≤ Q := hpT.trans (by
    calc T ≤ (Q : ℝ) * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ Q))
            (by linarith)) hq0.le
      _ = Q := mul_one _)
  have hfac := spectralFactor_le (by exact_mod_cast hp.one_lt.le) hq0 hpq
  have hB : 2 * primeMinorArcBound p U (2 * Q) + (p : ℝ) / 2 ≤ 69 * L ^ 4 * T := by
    have : (p : ℝ) / 2 ≤ L ^ 4 * T := by
      have h1 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
      linarith [mul_le_mul_of_nonneg_right h1 hT0]
    linarith
  have hfac2 : Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 / ((Q : ℝ) + 1) ^ 2 +
      Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 / ((Q : ℝ) + 1) ^ 3 ≤ 0.345 * ((p : ℝ) ^ 2 / (Q : ℝ) ^ 2) := by
    have e : Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 / ((Q : ℝ) + 1) ^ 2 +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 / ((Q : ℝ) + 1) ^ 3 =
        (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 36 / ((Q : ℝ) + 1) ^ 2 +
          Real.pi ^ 2 * (p : ℝ) ^ 3 / 24 / ((Q : ℝ) + 1) ^ 3) / 2 := by ring
    rw [e]
    linarith
  have hB0 : 0 ≤ 2 * primeMinorArcBound p U (2 * Q) + (p : ℝ) / 2 := by
    have : 0 ≤ primeMinorArcBound p U (2 * Q) := by unfold primeMinorArcBound; positivity
    positivity
  calc |kernelStatistic N (centredPrimeBlock Q) p|
      ≤ _ := abs_kernelStatistic_centredPrimeBlock_le_minorArc hp hU1 hUp hQN
    _ ≤ 0.345 * ((p : ℝ) ^ 2 / (Q : ℝ) ^ 2) * (69 * L ^ 4 * T) :=
        mul_le_mul hfac2 hB hB0 (by positivity)
    _ ≤ 24 * L ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
        have e : 0.345 * ((p : ℝ) ^ 2 / (Q : ℝ) ^ 2) * (69 * L ^ 4 * T) =
            23.805 * L ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
          simp only [T]; field_simp; ring
        rw [e]
        have : 0 ≤ L ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by positivity
        linarith

/-- **The dual norm of the centred prime row has a power saving below the diagonal.** -/
theorem dualNorm_centredPrimeBlock_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {Q : ℕ}
    (hQ : 2 ≤ Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ (Q : ℝ) ^ δ ≤ p ∧ (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ}
    (hQN : 2 * Q ≤ N) :
    ∑ p ∈ S, |kernelStatistic N (centredPrimeBlock Q) p| / p ≤
      24 * (1 + Real.log (2 * Q)) ^ 4 * (Q : ℝ) ^ (-(δ / 4)) * ∑ p ∈ S, (p : ℝ) / Q := by
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hpp, hpl, hpu⟩ := hS p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have h := abs_kernelStatistic_centredPrimeBlock_le_rpow hδ hδ1 hQ hpp hpl hpu hQN
  calc |kernelStatistic N (centredPrimeBlock Q) p| / p
      ≤ 24 * (1 + Real.log (2 * Q)) ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) / p :=
        div_le_div_of_nonneg_right h hp0.le
    _ = _ := by field_simp

/-! ## §3. The centred prime row on the diagonal -/

/-- The partial sums of the centred prime window are `ψ(Q + x) - ψ(Q) - x`. -/
theorem sum_range_centredPrimeBlock (Q x : ℕ) (hx : x ≤ Q) :
    ∑ i ∈ range x, centredPrimeBlock Q (Q + 1 + i) =
      (Chebyshev.psi ((Q + x : ℕ) : ℝ) - (Q + x : ℕ)) - (Chebyshev.psi (Q : ℝ) - Q) := by
  have hpsi : ∀ m : ℕ, Chebyshev.psi (m : ℝ) = ∑ n ∈ Icc 1 m, vonMangoldt n := fun m => by
    rw [Chebyshev.psi, Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ih (by omega), hpsi, hpsi, hpsi, show Q + (x + 1) = Q + x + 1 by ring,
      sum_Icc_succ_top (by omega : 1 ≤ Q + x + 1), centredPrimeBlock, if_pos (by omega),
      show Q + 1 + x = Q + x + 1 by ring]
    push_cast
    ring

/-- `Σ_n |(Λ(n) - 1)𝟙_{(Q,2Q]}(n)|/n² ≤ (B + 1)/Q` when `Σ_{Q<n≤2Q} Λ(n) ≤ B Q`. -/
theorem sum_Icc_abs_centredPrimeBlock_div_sq_le {Q N : ℕ} (hQ1 : 1 ≤ Q) {B : ℝ}
    (hψ : ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n ≤ B * Q) :
    ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 2 ≤ (B + 1) / Q := by
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hsub : ∀ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 2 ≤
      if Q < n ∧ n ≤ 2 * Q then (vonMangoldt n + 1) / (Q : ℝ) ^ 2 else 0 := by
    intro n _
    unfold centredPrimeBlock
    split_ifs with hn
    · have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
      calc |vonMangoldt n - 1| / (n : ℝ) ^ 2 ≤ (vonMangoldt n + 1) / (n : ℝ) ^ 2 := by
            gcongr
            rw [abs_le]; constructor <;> linarith [vonMangoldt_nonneg (n := n)]
        _ ≤ (vonMangoldt n + 1) / (Q : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by linarith [vonMangoldt_nonneg (n := n)]) (by positivity)
              (pow_le_pow_left₀ hq0.le hnQ 2)
    · simp
  calc ∑ n ∈ Icc 1 N, |centredPrimeBlock Q n| / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Icc 1 N, (if Q < n ∧ n ≤ 2 * Q then (vonMangoldt n + 1) / (Q : ℝ) ^ 2 else 0) :=
        sum_le_sum hsub
    _ ≤ ∑ n ∈ Ioc Q (2 * Q), (vonMangoldt n + 1) / (Q : ℝ) ^ 2 := by
        rw [← sum_filter]
        exact sum_le_sum_of_subset_of_nonneg (fun n hn => by
          simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢; omega)
          fun n _ _ => by have := vonMangoldt_nonneg (n := n); positivity
    _ = ((∑ n ∈ Ioc Q (2 * Q), vonMangoldt n) + Q) / (Q : ℝ) ^ 2 := by
        rw [← sum_div, sum_add_distrib, sum_const, Nat.card_Ioc, show 2 * Q - Q = Q by omega,
          nsmul_eq_mul, mul_one]
    _ ≤ (B * Q + Q) / (Q : ℝ) ^ 2 := by gcongr
    _ = (B + 1) / Q := by field_simp

/-- **The balanced dual-norm law for the centred prime row.** There is `c > 0` such that for every
`K ≥ 1` there are `C ≥ 0` and `Q₀` with `|Λ_d((Λ - 1)𝟙_{(Q,2Q]})| ≤ C (d²/Q) e^{-(c/2)√(log Q)}` for
`Q ≥ Q₀`, every modulus `d` with `Q ≤ K d`, `d ≤ 2Q`, and every `N ≥ 2Q`: the long-window saving of
the prime number theorem with error term. -/
theorem exists_balanced_kernelStatisticAll_centredPrimeBlock_le :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q →
      ∀ d : ℕ, 1 ≤ d → (Q : ℝ) ≤ K * d → d ≤ 2 * Q → ∀ N, 2 * Q ≤ N →
        |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
          C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c / 2 * Real.sqrt (Real.log Q))) := by
  obtain ⟨Cψ, c, hc, hCψ, hev⟩ := exists_psi_error_eventually
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨c, hc, fun K hK => ?_⟩
  obtain ⟨C, hC0, hlaw⟩ := exists_balanced_kernelStatisticAll_le hc hK
    (by positivity : (0 : ℝ) ≤ 3 * Cψ) (by positivity : (0 : ℝ) ≤ 3 + 2 * Cψ)
  refine ⟨C, hC0, max ⌈X⌉₊ 1, fun Q hQ d hd hQd hd2 N hQN => ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hQX : X ≤ Q := (Nat.le_ceil X).trans (by exact_mod_cast le_of_max_le_left hQ)
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hq0 : (0 : ℝ) < Q := by linarith
  set E := Real.exp (-(c * Real.sqrt (Real.log Q)))
  have hψ : ∀ y : ℝ, (Q : ℝ) ≤ y → |Chebyshev.psi y - y| ≤ Cψ * (y * E) := by
    intro y hy
    refine (hX y (hQX.trans hy)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ?_ (by linarith)) hCψ)
    apply Real.exp_le_exp.mpr
    have : Real.sqrt (Real.log Q) ≤ Real.sqrt (Real.log y) :=
      Real.sqrt_le_sqrt (Real.log_le_log hq0 hy)
    nlinarith
  have hA : ∀ x ≤ Q, |∑ i ∈ range x, centredPrimeBlock Q (Q + 1 + i)| ≤ 3 * Cψ * Q * E := by
    intro x hx
    rw [sum_range_centredPrimeBlock Q x hx]
    have hxR : (x : ℝ) ≤ Q := by exact_mod_cast hx
    have h1 := hψ ((Q + x : ℕ) : ℝ) (by push_cast; linarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)])
    have h2 := hψ Q le_rfl
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc |(Chebyshev.psi ((Q + x : ℕ) : ℝ) - (Q + x : ℕ)) - (Chebyshev.psi (Q : ℝ) - Q)|
        ≤ |Chebyshev.psi ((Q + x : ℕ) : ℝ) - (Q + x : ℕ)| + |Chebyshev.psi (Q : ℝ) - Q| :=
          abs_sub _ _
      _ ≤ Cψ * (((Q + x : ℕ) : ℝ) * E) + Cψ * (Q * E) := add_le_add h1 h2
      _ ≤ Cψ * (2 * Q * E) + Cψ * (Q * E) := by
          gcongr
          push_cast
          linarith
      _ = 3 * Cψ * Q * E := by ring
  -- `Σ_{Q<n≤2Q} Λ(n) ≤ (2 + 2Cψ) Q` from `ψ(2Q) ≤ (1 + Cψ) 2Q`
  have hψ2 : ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n ≤ (2 + 2 * Cψ) * Q := by
    have hpsi2 : Chebyshev.psi ((2 * Q : ℕ) : ℝ) = ∑ n ∈ Icc 1 (2 * Q), vonMangoldt n := by
      rw [Chebyshev.psi, Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    have hsplit : ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n ≤ ∑ n ∈ Icc 1 (2 * Q), vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg (fun n hn => by
        simp only [mem_Ioc, mem_Icc] at hn ⊢; omega) fun _ _ _ => vonMangoldt_nonneg
    have h2Q := hψ ((2 * Q : ℕ) : ℝ) (by push_cast; linarith)
    have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := Real.sqrt_nonneg (Real.log Q); nlinarith)
    have h3 : Chebyshev.psi ((2 * Q : ℕ) : ℝ) ≤ (2 * Q : ℕ) + Cψ * ((2 * Q : ℕ) * E) := by
      have := (abs_le.mp h2Q).2; linarith
    rw [hpsi2] at h3
    push_cast at h3
    have h4 : Cψ * (2 * Q * E) ≤ Cψ * (2 * Q) := by
      refine mul_le_mul_of_nonneg_left ?_ hCψ
      have := mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℝ) ≤ 2 * Q)
      linarith
    linarith
  have hT := sum_Icc_abs_centredPrimeBlock_div_sq_le (N := N) hQ1 hψ2
  rw [show (2 + 2 * Cψ + 1) = (3 + 2 * Cψ) by ring] at hT
  exact hlaw Q hQ1 _ (fun n h => centredPrimeBlock_ne_zero_imp h) hA N hQN hT d hd hQd hd2

/-! ## §4. The dichotomy for the actual rows -/

/-- **The cross-scale dichotomy.** For the Möbius row and the centred prime row on `(Q, 2Q]`:
below the diagonal, at every prime `Q^δ ≤ p ≤ Q^{1-δ}`, the dual-norm statistic is at most
`24 (1 + log 2Q)⁴ (p²/Q) Q^{-δ/4}` (a power saving, from the minor-arc law); on the diagonal, at
every modulus `Q ≤ K d`, `d ≤ 2Q`, it is at most `C (d²/Q) e^{-c√(log Q)}` (the long-window saving of
the zero-free region, from the archimedean law). -/
theorem crossScale_dichotomy_moebius_and_centredPrime {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {K : ℝ}
    (hK : 1 ≤ K) :
    (∀ Q : ℕ, 2 ≤ Q → ∀ p : ℕ, p.Prime → (Q : ℝ) ^ δ ≤ p → (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ) →
      ∀ N, 2 * Q ≤ N →
        |kernelStatistic N (moebiusWindowRow Q) p| ≤
            24 * (1 + Real.log (2 * Q)) ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) ∧
        |kernelStatistic N (centredPrimeBlock Q) p| ≤
            24 * (1 + Real.log (2 * Q)) ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4))) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → ∀ d : ℕ, 1 ≤ d →
      (Q : ℝ) ≤ K * d → d ≤ 2 * Q → ∀ N, 2 * Q ≤ N →
        |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
            C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c * Real.sqrt (Real.log Q))) ∧
        |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
            C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c * Real.sqrt (Real.log Q))) := by
  refine ⟨fun Q hQ p hp hpl hpu N hQN => ⟨?_, abs_kernelStatistic_centredPrimeBlock_le_rpow hδ hδ1
    hQ hp hpl hpu hQN⟩, ?_⟩
  · have h := abs_kernelStatistic_moebiusWindowRow_le_rpow hδ hδ1 hQ hp hpl hpu hQN
    have hL : 1 ≤ 1 + Real.log (2 * (Q : ℝ)) := by
      have := Real.log_nonneg (by have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith :
        (1 : ℝ) ≤ 2 * Q)
      linarith
    have hL34 : (1 + Real.log (2 * (Q : ℝ))) ^ 3 ≤ (1 + Real.log (2 * (Q : ℝ))) ^ 4 :=
      pow_le_pow_right₀ hL (by norm_num)
    have hpos : 0 ≤ ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by positivity
    calc |kernelStatistic N (moebiusWindowRow Q) p|
        ≤ 23 * (1 + Real.log (2 * Q)) ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := h
      _ ≤ 24 * (1 + Real.log (2 * Q)) ^ 4 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
          have h3 : 0 ≤ (1 + Real.log (2 * (Q : ℝ))) ^ 3 := by positivity
          linarith [mul_le_mul_of_nonneg_right hL34 hpos, mul_nonneg h3 hpos]
  · obtain ⟨C₁, hC₁, Q₁, h₁⟩ := exists_balanced_kernelStatisticAll_moebiusWindowRow_le hK
    obtain ⟨c₂, hc₂, h₂⟩ := exists_balanced_kernelStatisticAll_centredPrimeBlock_le
    obtain ⟨C₂, hC₂, Q₂, h₂⟩ := h₂ K hK
    refine ⟨min (1 / 24) (c₂ / 2), lt_min (by norm_num) (by positivity), max C₁ C₂,
      le_max_of_le_left hC₁, max Q₁ Q₂, fun Q hQ d hd hQd hd2 N hQN => ?_⟩
    have hD : 0 ≤ (d : ℝ) ^ 2 / Q := by positivity
    have hs : 0 ≤ Real.sqrt (Real.log Q) := Real.sqrt_nonneg _
    have hexp : ∀ a : ℝ, min (1 / 24) (c₂ / 2) ≤ a →
        Real.exp (-(a * Real.sqrt (Real.log Q))) ≤
          Real.exp (-(min (1 / 24) (c₂ / 2) * Real.sqrt (Real.log Q))) := fun a ha =>
      Real.exp_le_exp.mpr (by nlinarith)
    constructor
    · refine (h₁ Q (le_of_max_le_left hQ) d hd hQd hd2 N hQN).trans ?_
      have e : -(Real.sqrt (Real.log Q) / 24) = -(1 / 24 * Real.sqrt (Real.log Q)) := by ring
      rw [e]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hD) (hexp _ (min_le_left _ _))
        (Real.exp_pos _).le (mul_nonneg (le_max_of_le_left hC₁) hD)
    · refine (h₂ Q (le_of_max_le_right hQ) d hd hQd hd2 N hQN).trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hD) (hexp _ (min_le_right _ _))
        (Real.exp_pos _).le (mul_nonneg (le_max_of_le_left hC₁) hD)

end

end GaloisForLFunctions.BezoutValuationIncidence
