import GaloisForLFunctions.ExceptionalLayerTheory.TheDistinctPrimeFactorsOfOneCentralBinomialDetectEveryRightZero
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError

/-!
# The tent profile of binary carries and adjacent quotient intervals

Summing the period-two quotient carry over all base cutoffs below `X` produces
a continuous piecewise-affine tent offset from `X / 2`. Both the odd quotient
interval `⌊X / m⌋ = 2Q + 1` and its adjacent even quotient interval `⌊X / m⌋ = 2Q`
carry strictly positive cumulative weight at least `Q / (2Q + 1) * X ≥ X / 3`.
Pairing adjacent quotient intervals therefore creates no sign opposition: while
the von Mangoldt carry sum cancels `ζ`-zeros to `O(X^{3/2})` unconditionally,
the unweighted distinct-prime carry sum retains exact exponent `1 + zeroReSup`.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction
open scoped LSeries.notation

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Indicator of odd integral quotients, i.e., the binary carry of a central binomial coefficient. -/
def binaryCarryProfile (n : ℕ) : ℝ :=
  if 2 ∣ n + 1 then 1 else 0

/-- Distance from `X mod 2m` to the nearest endpoint of `[0, 2m]`, bounded by `m`. -/
def binaryCarryTent (m X : ℕ) : ℝ :=
  min ((X % (2 * m) : ℕ) : ℝ) (2 * (m : ℝ) - (X % (2 * m) : ℕ))

theorem binaryCarryProfile_eq_mod (n : ℕ) :
    binaryCarryProfile n = ((n % 2 : ℕ) : ℝ) := by
  unfold binaryCarryProfile
  split_ifs with h
  · have hm : n % 2 = 1 := by omega
    simp [hm]
  · have hm : n % 2 = 0 := by omega
    simp [hm]

theorem binaryCarryProfile_zero : binaryCarryProfile 0 = 0 := by
  simp [binaryCarryProfile]

theorem binaryCarryProfile_bounds (n : ℕ) :
    0 ≤ binaryCarryProfile n ∧ binaryCarryProfile n ≤ 1 := by
  unfold binaryCarryProfile
  split_ifs <;> norm_num

theorem binaryCarryTent_bounds {m : ℕ} (hm : 0 < m) (X : ℕ) :
    0 ≤ binaryCarryTent m X ∧ binaryCarryTent m X ≤ m := by
  have hlt : X % (2 * m) < 2 * m := Nat.mod_lt X (by omega)
  have hle : ((X % (2 * m) : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hlt.le
  unfold binaryCarryTent
  refine ⟨le_min (Nat.cast_nonneg _) (sub_nonneg.mpr hle), ?_⟩
  by_cases h : ((X % (2 * m) : ℕ) : ℝ) ≤ m
  · exact (min_le_left _ _).trans h
  · refine (min_le_right _ _).trans ?_
    linarith only [h]

private theorem sum_range_binaryCarryProfile (d : ℕ) :
    (∑ j ∈ range d, binaryCarryProfile j) = ((d / 2 : ℕ) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    unfold binaryCarryProfile
    by_cases h : 2 ∣ d + 1
    · rw [if_pos h]
      have hd : (d + 1) / 2 = d / 2 + 1 := by omega
      push_cast [hd]
      ring
    · rw [if_neg h]
      have hd : (d + 1) / 2 = d / 2 := by omega
      simp [hd]

private theorem sum_range_mul_div {m : ℕ} (hm : 0 < m) (d : ℕ) :
    (∑ k ∈ range (m * d), binaryCarryProfile (k / m)) =
      (m : ℝ) * ∑ j ∈ range d, binaryCarryProfile j := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    calc
      _ = ∑ _r ∈ range m, binaryCarryProfile d := by
        refine sum_congr rfl fun r hr => ?_
        rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (mem_range.mp hr), add_zero]
      _ = _ := by simp

/-- Exact piecewise-affine evaluation of the discrete quotient mean of the binary carry. -/
theorem discreteQuotientMean_binaryCarryProfile_eq_piecewise {m : ℕ} (hm : 0 < m) (X : ℕ) :
    discreteQuotientMean binaryCarryProfile m X =
      if 2 ∣ X / m then (((X / m) / 2 : ℕ) : ℝ) * m
      else (X : ℝ) - ((((X / m) / 2 : ℕ) : ℝ) + 1) * m := by
  let d := X / m
  let r := X % m
  have hX : m * d + r = X := Nat.div_add_mod X m
  have hr : r < m := Nat.mod_lt X hm
  have htail : (∑ i ∈ range r, binaryCarryProfile ((m * d + i) / m)) =
      (r : ℝ) * binaryCarryProfile d := by
    calc
      _ = ∑ _i ∈ range r, binaryCarryProfile d := by
        refine sum_congr rfl fun i hi => ?_
        rw [Nat.mul_add_div hm, Nat.div_eq_of_lt ((mem_range.mp hi).trans hr), add_zero]
      _ = _ := by simp
  have hLHS : discreteQuotientMean binaryCarryProfile m X =
      (m : ℝ) * ((d / 2 : ℕ) : ℝ) + (r : ℝ) * binaryCarryProfile d := by
    rw [discreteQuotientMean, ← hX, sum_range_add, sum_range_mul_div hm d,
      sum_range_binaryCarryProfile, htail]
  rw [hLHS]
  change (m : ℝ) * ((d / 2 : ℕ) : ℝ) + (r : ℝ) * binaryCarryProfile d =
    if 2 ∣ d then ((d / 2 : ℕ) : ℝ) * m else (X : ℝ) - (((d / 2 : ℕ) : ℝ) + 1) * m
  split_ifs with hd
  · have hb : binaryCarryProfile d = 0 := if_neg (by omega)
    rw [hb]
    ring
  · have hb : binaryCarryProfile d = 1 := if_pos (by omega)
    have hodd : 2 * (d / 2) + 1 = d := by omega
    have hoddR : 2 * ((d / 2 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hodd
    have hXR : (X : ℝ) = (m : ℝ) * d + r := by exact_mod_cast hX.symm
    rw [hb, mul_one, hXR]
    linear_combination (m : ℝ) * hoddR

/-- Period-mean plus symmetric tent decomposition of the binary-carry quotient mean. -/
theorem discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent {m : ℕ} (hm : 0 < m) (X : ℕ) :
    discreteQuotientMean binaryCarryProfile m X =
      (X : ℝ) / 2 - binaryCarryTent m X / 2 := by
  rw [discreteQuotientMean_binaryCarryProfile_eq_piecewise hm X]
  let d := X / m
  let Q := d / 2
  let r := X % m
  have hr : r < m := Nat.mod_lt X hm
  have hdiv : m * d + r = X := Nat.div_add_mod X m
  change (if 2 ∣ d then (Q : ℝ) * m else (X : ℝ) - ((Q : ℝ) + 1) * m) = _
  split_ifs with hd
  · have hd2 : d = 2 * Q := by omega
    have heq : r + 2 * m * Q = X := by
      calc r + 2 * m * Q = m * (2 * Q) + r := by ring
        _ = m * d + r := by rw [← hd2]
        _ = X := hdiv
    have hmod : X % (2 * m) = r := by
      rw [← heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hXeq : (X : ℝ) = 2 * (m : ℝ) * Q + r := by
      have : X = 2 * m * Q + r := by linarith only [heq]
      exact_mod_cast this
    have htent : binaryCarryTent m X = r := by
      unfold binaryCarryTent
      rw [hmod, min_eq_left]
      have : (r : ℝ) ≤ m := by exact_mod_cast hr.le
      linarith only [this]
    rw [htent, hXeq]
    ring
  · have hd2 : d = 2 * Q + 1 := by omega
    have heq : (m + r) + 2 * m * Q = X := by
      calc (m + r) + 2 * m * Q = m * (2 * Q + 1) + r := by ring
        _ = m * d + r := by rw [← hd2]
        _ = X := hdiv
    have hmod : X % (2 * m) = m + r := by
      rw [← heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hXeq : (X : ℝ) = (2 * (Q : ℝ) + 1) * m + r := by
      have : X = (2 * Q + 1) * m + r := by linarith only [heq]
      exact_mod_cast this
    have htent : binaryCarryTent m X = (m : ℝ) - r := by
      unfold binaryCarryTent
      rw [hmod]
      push_cast
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      rw [min_eq_right (by linarith only [hr0])]
      ring
    rw [htent, hXeq]
    ring

/-- Both the even quotient interval `⌊X/m⌋ = 2Q` and the adjacent odd quotient interval
`⌊X/m⌋ = 2Q + 1` carry positive cumulative weight between `Q/(2Q+1) * X` (`≥ X/3`) and `X/2`. -/
theorem discreteQuotientMean_binaryCarryProfile_adjacent_intervals {Q m X : ℕ}
    (hQ : 1 ≤ Q) (hm : 0 < m) (hband : X / m = 2 * Q ∨ X / m = 2 * Q + 1) :
    ((Q : ℝ) / (2 * (Q : ℝ) + 1)) * X ≤ discreteQuotientMean binaryCarryProfile m X ∧
      (X : ℝ) / 3 ≤ discreteQuotientMean binaryCarryProfile m X ∧
      discreteQuotientMean binaryCarryProfile m X ≤ (X : ℝ) / 2 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < 2 * (Q : ℝ) + 1 := by positivity
  have hthird : (X : ℝ) / 3 ≤ ((Q : ℝ) / (2 * (Q : ℝ) + 1)) * X := by
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hpos]
    nlinarith only [hQ1, hX0]
  have hhi : discreteQuotientMean binaryCarryProfile m X ≤ (X : ℝ) / 2 := by
    rw [discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent hm X]
    have ht := (binaryCarryTent_bounds hm X).1
    linarith only [ht]
  have hlo : ((Q : ℝ) / (2 * (Q : ℝ) + 1)) * X ≤ discreteQuotientMean binaryCarryProfile m X := by
    rw [discreteQuotientMean_binaryCarryProfile_eq_piecewise hm X]
    rcases hband with heven | hodd
    · rw [heven, if_pos ⟨Q, rfl⟩, Nat.mul_div_right Q two_pos]
      have hlt : X < (2 * Q + 1) * m := (Nat.div_lt_iff_lt_mul hm).mp (by omega)
      have hle : (X : ℝ) ≤ (2 * (Q : ℝ) + 1) * m := by exact_mod_cast hlt.le
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith only [hle, hQ1]
    · rw [hodd, if_neg (by omega)]
      have hdiv : (2 * Q + 1) / 2 = Q := by omega
      rw [hdiv]
      have hle_nat : (2 * Q + 1) * m ≤ X := (Nat.le_div_iff_mul_le hm).mp (by omega)
      have hle : (2 * (Q : ℝ) + 1) * m ≤ X := by exact_mod_cast hle_nat
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith only [hle, hQ1]
  exact ⟨hlo, hthird.trans hlo, hhi⟩

/-- Exact decomposition of the period-two ordinary-prime first total into half the
unweighted prime prefix error times `X` minus the tent-weighted remainder. -/
theorem ordinaryLastClassTotal_two_eq_half_prefix_sub_tent (X : ℕ) :
    ordinaryLastClassTotal 2 X =
      ((X : ℝ) / 2) * (∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m) -
        (1 / 2 : ℝ) * ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m * binaryCarryTent m X := by
  have he (k : ℕ) (hk : k ∈ range X) :
      quotientClassMassOf ordinaryPrimeCountWeight 2 k =
        ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m * binaryCarryProfile (k / m) := by
    apply sum_subset (Icc_subset_Icc_right (mem_range.mp hk).le)
    intro m hm hm'
    have hm0 := (mem_Icc.mp hm).1
    have hkm : k < m := by by_contra! hg; exact hm' (mem_Icc.mpr ⟨hm0, hg⟩)
    simp [Nat.div_eq_of_lt hkm]
  have hswap : ordinaryLastClassTotal 2 X =
      ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X := by
    rw [ordinaryLastClassTotal, sum_congr rfl he, sum_comm]
    simp only [discreteQuotientMean, mul_sum]
  rw [hswap]
  have hterm : (∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m *
      discreteQuotientMean binaryCarryProfile m X) =
      ∑ m ∈ Icc 1 X, (ordinaryPrimeCountWeight m * ((X : ℝ) / 2) -
        (1 / 2 : ℝ) * (ordinaryPrimeCountWeight m * binaryCarryTent m X)) := by
    refine sum_congr rfl fun m hm => ?_
    rw [discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent (mem_Icc.mp hm).1 X]
    ring
  rw [hterm, sum_sub_distrib, ← sum_mul, ← mul_sum, mul_comm _ ((X : ℝ) / 2)]

/-- With von Mangoldt weights, binary carries cancel `ζ`-zeros unconditionally to `O(X^{3/2})`
in the first total using only divisibility, integer division, and finite differences. -/
theorem mangoldt_binaryCarry_first_total_le_three_halves (X : ℕ) :
    |∑ k ∈ range X, ∑ m ∈ Icc 1 k, (vonMangoldt m - 1) * binaryCarryProfile (k / m)| ≤
      (75 + 2 * |Real.eulerMascheroniConstant|) * (X : ℝ) ^ (3 / 2 : ℝ) := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  let C := 75 + 2 * |Real.eulerMascheroniConstant|
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hterm (k : ℕ) :
      (∑ m ∈ Icc 1 k, (vonMangoldt m - 1) * binaryCarryProfile (k / m)) =
        ∑ n ∈ Icc 1 k, alternatingPrimeExcess n := by
    rw [alternatingPrimeExcess_eq_parity_count]
    refine sum_congr rfl fun m hm => ?_
    have hz : ((zeta : ArithmeticFunction ℝ) m : ℝ) = 1 := by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
        Nat.ne_of_gt (mem_Icc.mp hm).1]
    rw [binaryCarryProfile_eq_mod]
    change (vonMangoldt m - 1) * _ = (vonMangoldt m - (zeta : ArithmeticFunction ℝ) m) * _
    rw [hz]
  simp_rw [hterm]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k ∈ range X, C * Real.sqrt X := by
      refine sum_le_sum fun k hk => (abs_prefix_alternatingPrimeExcess k).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast (mem_range.mp hk).le)) hC
    _ = C * ((X : ℝ) * Real.sqrt X) := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring
    _ = C * (X : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (X : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) =
        (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hX0]
      norm_num

private theorem jump_series_eq {q : ℕ} [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    let c := fun n => ((ordinaryPrimeCountWeight * lastClassCoefficients q) n : ℂ)
    LSeriesSummable c s ∧ LSeries c s =
      lastQuotientClassSymbol q s * LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s := by
  have hc {n : ℕ} (hn : n ≠ 0) : (lastClassCoefficients q n : ℂ) = lastClassJumps (n : ZMod q) := by
    have h1 : ((n : ZMod q) = -1) ↔ q ∣ n + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]
    have hval : lastClassCoefficients q n =
        ((if q ∣ n + 1 then 1 else 0) - (if q ∣ n then 1 else 0) : ℝ) := if_neg hn
    rw [hval]
    simp only [lastClassJumps, h1, ZMod.natCast_eq_zero_iff]
    split_ifs <;> simp
  have he : (fun n => ((ordinaryPrimeCountWeight * lastClassCoefficients q) n : ℂ)) =
      ((fun n => (ordinaryPrimeCountWeight n : ℂ)) ⍟ fun n => (lastClassCoefficients q n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
  have ha := ordinaryPrimeCountWeight_summable hs
  have hd : LSeriesSummable (fun n => (lastClassCoefficients q n : ℂ)) s :=
    (LSeriesSummable_congr s hc).mpr (ZMod.LSeriesSummable_of_one_lt_re lastClassJumps hs)
  dsimp only
  rw [he]
  refine ⟨ha.convolution hd, ?_⟩
  rw [LSeries_convolution' ha hd, LSeries_congr hc s, lastQuotientClassSymbol_eq_LSeries q hs, mul_comm]

/-- Any `O(X^{b+1})` bound (`1/2 ≤ b < 1`) on `ordinaryLastClassTotal q` excludes all `ζ`-zeros
in `Re s > b` and forces `zeroReSup ≤ b`. -/
theorem ordinaryLastClassTotal_bound_excludes_zero_and_bounds_zeroReSup {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {b C : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (h : ∀ X : ℕ, 1 ≤ X → |ordinaryLastClassTotal q X| ≤ C * (X : ℝ) ^ (b + 1)) :
    (∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0) ∧ _root_.RHTower.zeroReSup ≤ b := by
  have hC : 0 ≤ |C| := abs_nonneg C
  have hb0 : 0 ≤ b := by linarith only [hb]
  let c := fun n => (ordinaryPrimeCountWeight * lastClassCoefficients q) n
  have hprofile (N : ℕ) (hn : 1 ≤ N) :
      |triangularPrimeProfile c (N : ℝ)⁻¹| ≤ |C| * (N : ℝ) ^ b := by
    have hp : 0 < (N : ℝ) := by exact_mod_cast hn
    have he : (N : ℝ) * triangularPrimeProfile c (N : ℝ)⁻¹ = ordinaryLastClassTotal q N := by
      rw [triangularPrimeProfile_sample, ordinaryLastClassTotal]
      exact sum_congr rfl fun k _ => (quotientClassMassOf_eq_prefix _ hq k).symm
    have hh := (h N hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    rw [← he, abs_mul, abs_of_pos hp, Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  have hdiff : DifferentiableOn ℂ (triangularDirichletContinuation c) {s : ℂ | b < s.re} :=
    fun _ hs => (differentiableAt_triangularDirichletContinuation c hC hb0 hprofile hs).differentiableWithinAt
  have hzf : ∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0 := by
    intro ρ hρ
    apply lastClass_primePrimitive_continuation_excludes_zero hq hb hb1
      (triangularDirichletContinuation c)
      ((hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)).meromorphicOn) _ hρ
    intro s hs
    let f := fun n => (c n : ℂ)
    have hf : LSeriesSummable f 2 := (jump_series_eq (q := q) (s := 2) (by norm_num)).1
    let M := ∑' n, ‖LSeries.term f 2 n‖
    have hcoef (n : ℕ) : |c (n + 1)| ≤ M * ((n : ℝ) + 1) ^ (2 : ℝ) := by
      have he : ‖LSeries.term f 2 (n + 1)‖ ≤ M := hf.norm.le_tsum (n + 1) (fun _ _ => norm_nonneg _)
      rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)] at he
      simp only [f, Complex.norm_real, Real.norm_eq_abs,
        show (2 : ℂ).re = (2 : ℝ) by norm_num, Nat.cast_succ] at he
      exact (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ (2 : ℝ))).mp he
    have hs1 : 1 < s.re := by linarith only [hs]
    rw [triangularDirichletContinuation_eq_series c hcoef (by linarith only [hs]) (by linarith only [hs]),
      ← (jump_series_eq (q := q) hs1).2]
    have hsum := (jump_series_eq (q := q) hs1).1.hasSum
    have hs' := (hasSum_nat_add_iff' 1).mpr hsum
    simp only [sum_range_one, LSeries.term_zero, sub_zero] at hs'
    refine (tsum_congr (g := fun n => LSeries.term f s (n + 1)) fun n => ?_).trans hs'.tsum_eq
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    simp [f]
  refine ⟨hzf, _root_.RHTower.zeroReSup_le_of_forall_re_le fun z => ?_⟩
  by_contra hgt
  exact hzf (z.1 : ℂ) (not_le.mp hgt) (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy z)

/-- At each fixed exponent `b ≥ 1/2`, `binomialDistinctPrimeTotal j` and
`ordinaryLastClassTotal (2^(j+1))` satisfy the same `O(X^{b+1})` growth law. -/
theorem binomialDistinctPrimeTotal_bound_iff_ordinaryLastClassTotal (j : ℕ) {b : ℝ} (hb : 1 / 2 ≤ b) :
    (∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (b + 1)) ↔
      (∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → |ordinaryLastClassTotal (2 ^ (j + 1)) X| ≤ C * (X : ℝ) ^ (b + 1)) := by
  obtain ⟨K, _, hcmp⟩ := binomialDistinctPrimeTotal_error j hb
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨K + |C|, fun X hX => ?_⟩
  · have he := abs_sub_le (ordinaryLastClassTotal (2 ^ (j + 1)) X) (binomialDistinctPrimeTotal j X) 0
    simp only [sub_zero] at he
    rw [abs_sub_comm] at he
    have hh := (hC X hX).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    exact (he.trans (add_le_add (hcmp X hX) hh)).trans_eq (add_mul ..).symm
  · have he := abs_sub_le (binomialDistinctPrimeTotal j X) (ordinaryLastClassTotal (2 ^ (j + 1)) X) 0
    simp only [sub_zero] at he
    have hh := (hC X hX).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    exact (he.trans (add_le_add (hcmp X hX) hh)).trans_eq (add_mul ..).symm

/-- Any `O(X^{b+1})` bound (`1/2 ≤ b < 1`) on `binomialDistinctPrimeTotal j` excludes all
`ζ`-zeros in `Re s > b` and forces `zeroReSup ≤ b`. -/
theorem binomialDistinctPrimeTotal_bound_excludes_zero_and_bounds_zeroReSup (j : ℕ)
    {b C : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (h : ∀ X : ℕ, 1 ≤ X → |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (b + 1)) :
    (∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0) ∧ _root_.RHTower.zeroReSup ≤ b := by
  obtain ⟨C', hC'⟩ := (binomialDistinctPrimeTotal_bound_iff_ordinaryLastClassTotal j hb).mp ⟨C, h⟩
  have hq : 2 ≤ 2 ^ (j + 1) := by have := Nat.lt_two_pow_self (n := j + 1); omega
  exact ordinaryLastClassTotal_bound_excludes_zero_and_bounds_zeroReSup hq hb hb1 hC'

#print axioms discreteQuotientMean_binaryCarryProfile_eq_piecewise
#print axioms discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent
#print axioms discreteQuotientMean_binaryCarryProfile_adjacent_intervals
#print axioms ordinaryLastClassTotal_two_eq_half_prefix_sub_tent
#print axioms mangoldt_binaryCarry_first_total_le_three_halves
#print axioms binomialDistinctPrimeTotal_bound_excludes_zero_and_bounds_zeroReSup

end GaloisForLFunctions.ExceptionalLayerTheory
