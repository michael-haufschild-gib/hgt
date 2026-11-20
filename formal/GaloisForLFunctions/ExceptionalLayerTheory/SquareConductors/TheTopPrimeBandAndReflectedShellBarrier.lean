import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.DisjointOrdinaryPrimeRangesAtTheSameMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeCentersOfTheSharpMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLargeOrdinaryPrimeShellsInTheMidpoint

/-!
# Exact top-band collapse at prime centers, cofactor slice self-duality, and the eight-ninths shell

Evaluating the moving-cofactor midpoint projection at the top band `a = b` (`V = 1`) and prime
centers `p` eliminates every proper-power and divisor-sum error term identically, while slicing
`unrestrictedLargePrimePrice` by cofactor `v` exposes exact Chebyshev-`θ` midpoint differences and
isolates the `p^{8/9}` reflected-shell threshold for `Θ_ζ ≤ 5 / 6`:

* **Exact `V = 1` (`a = b`) algebraic collapse at prime centers (`midpointFloorWeight_self`,
  `divisibleCofactorFactorial_self`, `divisibleCofactorPrimePrice_self`,
  `primitiveProjectedFactorial_prime_one`, `remainingPrimitivePrimePrice_prime_one`,
  `ordinaryPrimeBandPrice_self_prime`).** For every prime `p` and `3 ≤ Q ≤ 2p`,
  `remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q` and
  `primitiveProjectedFactorial p 1 = completeMidpointFactorial p - (log 4 - log 3)` with zero error.
* **Cofactor-slice decomposition and Chebyshev-`θ` self-duality
  (`unrestrictedLargePrimePrice_eq_sum_cofactorThetaSlice`, `cofactorThetaSlice_eq_chebyshev_theta`,
  `cofactorThetaSlice_mul_eq_neg_primeMidpointPrice`).** Grouping `q ∈ (Q, 2n]` by `v` with
  `q v ≤ k n` decomposes `unrestrictedLargePrimePrice n Q` over `2 ≤ v ≤ 4n`; whenever `v Q ≤ 2n`,
  the `v`-slice equals `θ(⌊4n/v⌋) - 2 θ(⌊3n/v⌋) + θ(⌊2n/v⌋)` (`= -primeMidpointPrice m` at `n = mv`).
* **Prime-center `p^{8/9}` reflected-shell criterion (`prime_centers_shell_eight_ninths_iff_five_sixths`).**
  `Θ_ζ ≤ 5 / 6` holds if and only if for every `t ∈ (5 / 6, 1)` there exists `C` such that
  `unrestrictedLargePrimePrice p ⌊p^{8/9}⌋₊ - reflectedDensity · p ≤ C p^t` for all primes `p`.
-/

noncomputable section

open Finset Filter ArithmeticFunction GaloisForLFunctions.PrimeExponentialSums
open scoped ArithmeticFunction.Moebius
open RHTower (truncMoebiusDivisorSum)

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-! ### Part 1: Exact `V = 1` (`a = b`) collapse at prime centers -/

/-- At `d = n` (`n > 0`), the three midpoint quotients are `4, 3, 2` and `4 - 2·3 + 2 = 0`. -/
theorem midpointFloorWeight_self {n : ℕ} (hn : 0 < n) : midpointFloorWeight n n = 0 := by
  unfold midpointFloorWeight
  rw [Nat.mul_div_cancel 4 hn, Nat.mul_div_cancel 3 hn, Nat.mul_div_cancel 2 hn]
  norm_num

/-- At `r = n` (`n > 0`), `divisibleCofactorFactorial n n = log(4!) - 2 log(3!) + log(2!) = log 4 - log 3`. -/
theorem divisibleCofactorFactorial_self {n : ℕ} (hn : 0 < n) :
    divisibleCofactorFactorial n n = Real.log 4 - Real.log 3 := by
  unfold divisibleCofactorFactorial
  rw [Nat.mul_div_cancel 4 hn, Nat.mul_div_cancel 3 hn, Nat.mul_div_cancel 2 hn]
  have h4 : (Nat.factorial 4 : ℝ) = 4 * (3 * 2) := by norm_num [Nat.factorial]
  have h3 : (Nat.factorial 3 : ℝ) = 3 * 2 := by norm_num [Nat.factorial]
  have h2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [h4, h3, h2, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- At `r = n` (`n > 0`) and `Q ≥ 3`, `4n / n = 4` leaves only `q = 4 > Q`, which is composite;
hence `divisibleCofactorPrimePrice n Q n = 0`. -/
theorem divisibleCofactorPrimePrice_self {n Q : ℕ} (hn : 0 < n) (hQ : 3 ≤ Q) :
    divisibleCofactorPrimePrice n Q n = 0 := by
  unfold divisibleCofactorPrimePrice
  rw [Nat.mul_div_cancel 4 hn]
  refine sum_eq_zero fun q hq => ?_
  obtain ⟨hqI, hqQ, hqpr, _⟩ := mem_filter.mp hq
  have hq4 : q = 4 := by
    have := (mem_Icc.mp hqI).2
    omega
  subst hq4
  exact False.elim ((by norm_num : ¬ Nat.Prime 4) hqpr)

/-- At a prime center `p` and cofactor cut `V = 1`, `primitiveProjectedFactorial p 1` equals
`completeMidpointFactorial p - (log 4 - log 3)` identically. -/
theorem primitiveProjectedFactorial_prime_one {p : ℕ} (hp : p.Prime) :
    primitiveProjectedFactorial p 1 = completeMidpointFactorial p - (Real.log 4 - Real.log 3) := by
  unfold primitiveProjectedFactorial
  have hI : Icc (1 : ℕ) 1 = {1} := rfl
  rw [hI, sum_singleton, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
    hp.divisors, sum_pair hp.one_lt.ne, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp]
  simp only [Nat.lcm_one_left]
  rw [divisibleCofactorFactorial_self hp.pos]
  have h1 : divisibleCofactorFactorial p 1 = completeMidpointFactorial p := by
    simp [divisibleCofactorFactorial, completeMidpointFactorial]
  rw [h1]
  push_cast
  ring

private lemma sum_Ioc_two_four_midpoint {n : ℕ} :
    (∑ q ∈ (Ioc (2 * n) (4 * n)).filter Nat.Prime, Real.log q * midpointFloorWeight n q) =
      -primeMidpointPrice n := by
  let f (q : ℕ) : ℝ := if q.Prime then Real.log q * midpointFloorWeight n q else 0
  have hunit : ∀ {q : ℕ}, q ∈ Ioc (2 * n) (4 * n) →
      midpointFloorWeight n q = if q ≤ 3 * n then -1 else 1 := by
    intro q hq
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hq
    have hq0 : 0 < q := by omega
    have h4 : 4 * n / q = 1 := by
      have h1 : 1 ≤ 4 * n / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
      have h2 : 4 * n / q < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
      omega
    have h3 : 3 * n / q < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
    rw [midpointFloorWeight, h4, Nat.div_eq_of_lt hlo]
    split_ifs with hq3
    · have h1 : 1 ≤ 3 * n / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
      rw [show 3 * n / q = 1 by omega]; norm_num
    · rw [Nat.div_eq_of_lt (lt_of_not_ge hq3)]; norm_num
  have hleft : (∑ q ∈ Ioc (2 * n) (3 * n), f q) =
      -(∑ q ∈ (Ioc (2 * n) (3 * n)).filter Nat.Prime, Real.log q) := by
    rw [sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun q hq => ?_
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hq
    simp only [f, hunit (mem_Ioc.mpr ⟨hl, by omega⟩), if_pos hu]
    split_ifs <;> ring
  have hright : (∑ q ∈ Ioc (3 * n) (4 * n), f q) =
      ∑ q ∈ (Ioc (3 * n) (4 * n)).filter Nat.Prime, Real.log q := by
    rw [sum_filter]
    refine sum_congr rfl fun q hq => ?_
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hq
    simp only [f, hunit (mem_Ioc.mpr ⟨by omega, hu⟩), if_neg (not_le.mpr hl), mul_one]
  have hsplit := sum_Ioc_consecutive f (show 2 * n ≤ 3 * n by omega) (show 3 * n ≤ 4 * n by omega)
  rw [sum_filter]
  change (∑ q ∈ Ioc (2 * n) (4 * n), f q) = _
  rw [← hsplit, hleft, hright, primeMidpointPrice]
  ring

private lemma divisibleCofactorPrimePrice_prime_one {p Q : ℕ} (hp : p.Prime) (hQ2 : Q ≤ 2 * p) :
    divisibleCofactorPrimePrice p Q 1 = unrestrictedLargePrimePrice p Q - primeMidpointPrice p := by
  unfold divisibleCofactorPrimePrice
  simp only [Nat.div_one, mul_one]
  have heq : (∑ q ∈ (Icc 1 (4 * p)).filter (fun q => Q < q ∧ q.Prime ∧ ¬ q ∣ p),
        Real.log q * midpointFloorWeight p q) =
      ∑ q ∈ (Ioc Q (4 * p)).filter Nat.Prime, Real.log q * midpointFloorWeight p q := by
    refine sum_subset (fun q hq => ?_) (fun q hq hnot => ?_)
    · obtain ⟨hqI, hqQ, hqpr, _⟩ := mem_filter.mp hq
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hqQ, (mem_Icc.mp hqI).2⟩, hqpr⟩
    · obtain ⟨hqI, hqpr⟩ := mem_filter.mp hq
      obtain ⟨hqQ, hq4⟩ := mem_Ioc.mp hqI
      have hdvd : q ∣ p := by
        by_contra hnd
        exact hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨hqpr.pos, hq4⟩, hqQ, hqpr, hnd⟩)
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqpr hp).mp hdvd
      subst hqp
      rw [midpointFloorWeight_self hp.pos, mul_zero]
  rw [heq]
  have hconsec := sum_Ioc_consecutive
    (fun q : ℕ => if q.Prime then Real.log q * midpointFloorWeight p q else 0)
    hQ2 (show 2 * p ≤ 4 * p by omega)
  simp only [← sum_filter] at hconsec
  rw [← hconsec, sum_Ioc_two_four_midpoint]
  rfl

/-- **Exact `V = 1` primitive-to-unrestricted identity at prime centers.** For every prime `p` and
cutoff `3 ≤ Q ≤ 2p`, `remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q` with
zero approximation error. -/
theorem remainingPrimitivePrimePrice_prime_one {p Q : ℕ} (hp : p.Prime) (hQ3 : 3 ≤ Q)
    (hQ2 : Q ≤ 2 * p) :
    remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q := by
  have hproj := primitive_prime_cofactor_projection hp.pos Q 1
  let f (v : ℕ) : ℝ :=
    if p.Coprime v then truncMoebiusDivisorSum 1 v * primitiveOrdinaryCofactorRow p Q v else 0
  have hI01 : Ioc (0 : ℕ) 1 = {1} := by
    ext v; simp only [mem_Ioc, mem_singleton]; omega
  have hunit : (∑ v ∈ Ioc 0 1, f v) = -primeMidpointPrice p := by
    rw [hI01, sum_singleton]
    dsimp only [f]
    rw [if_pos (Nat.coprime_one_right p),
      _root_.RHTower.truncMoebiusDivisorSum_of_le (by decide) le_rfl, if_pos rfl, one_mul,
      prime_cofactor_unit_price hp.pos hQ2]
  have hsplit := sum_Ioc_consecutive f (Nat.zero_le 1) (by have := hp.pos; omega : 1 ≤ 4 * p)
  rw [hunit] at hsplit
  have hlhs : (∑ v ∈ (Ioc 0 (4 * p)).filter (p.Coprime ·),
        truncMoebiusDivisorSum 1 v * primitiveOrdinaryCofactorRow p Q v) =
      remainingPrimitivePrimePrice p Q 1 - primeMidpointPrice p := by
    simp only [remainingPrimitivePrimePrice, sum_filter]
    change (∑ v ∈ Ioc 0 (4 * p), f v) = (∑ v ∈ Ioc 1 (4 * p), f v) - _
    linarith only [hsplit]
  have hrhs : (∑ e ∈ Icc 1 1, (μ e : ℝ) * ∑ d ∈ p.divisors,
        (μ d : ℝ) * divisibleCofactorPrimePrice p Q (e.lcm d)) =
      unrestrictedLargePrimePrice p Q - primeMidpointPrice p := by
    have hI : Icc (1 : ℕ) 1 = {1} := rfl
    rw [hI, sum_singleton, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
      hp.divisors, sum_pair hp.one_lt.ne, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hp]
    simp only [Nat.lcm_one_left]
    rw [divisibleCofactorPrimePrice_self hp.pos hQ3, divisibleCofactorPrimePrice_prime_one hp hQ2]
    push_cast
    ring
  linarith only [hproj, hlhs, hrhs]

/-- At the top band `a = b` (`b ≥ 1 / 2`) and any prime center `p ≥ 3`, `ordinaryPrimeBandPrice b b p`
collapses identically to `unrestrictedLargePrimePrice p Q - completeMidpointFactorial p + (log 4 - log 3)`. -/
theorem ordinaryPrimeBandPrice_self_prime {b : ℝ} (hb : 1 / 2 ≤ b) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) :
    ordinaryPrimeBandPrice b b p =
      unrestrictedLargePrimePrice p (min (2 * p) ⌊(4 * (p : ℝ)) ^ b⌋₊) -
        completeMidpointFactorial p + (Real.log 4 - Real.log 3) := by
  unfold ordinaryPrimeBandPrice
  simp only [sub_self, Real.rpow_zero, Nat.floor_one]
  set Q := min (2 * p) ⌊(4 * (p : ℝ)) ^ b⌋₊
  have hQ2 : Q ≤ 2 * p := min_le_left _ _
  have hQ3 : 3 ≤ Q := by
    refine le_min (by omega) (Nat.le_floor ?_)
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h12 : (9 : ℝ) ≤ 4 * (p : ℝ) := by linarith
    have hsq : (3 : ℝ) ≤ Real.sqrt (4 * (p : ℝ)) := by
      calc (3 : ℝ) = Real.sqrt 9 := by norm_num
        _ ≤ Real.sqrt (4 * (p : ℝ)) := Real.sqrt_le_sqrt h12
    rw [Real.sqrt_eq_rpow] at hsq
    exact_mod_cast hsq.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hb)
  rw [remainingPrimitivePrimePrice_prime_one hp hQ3 hQ2, primitiveProjectedFactorial_prime_one hp]
  ring

/-! ### Part 2: Cofactor-slice decomposition and Chebyshev-`θ` self-duality -/

/-- The `v`-cofactor slice of `unrestrictedLargePrimePrice n Q`. -/
def cofactorThetaSlice (n Q v : ℕ) : ℝ :=
  ∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime,
    Real.log q * ((if q * v ≤ 4 * n then (1 : ℝ) else 0) -
      2 * (if q * v ≤ 3 * n then (1 : ℝ) else 0) +
      (if q * v ≤ 2 * n then (1 : ℝ) else 0))

private lemma sum_Icc_indicator_mul_le {q T M : ℕ} (hq : 0 < q) (hTM : T ≤ M) :
    (∑ v ∈ Icc 1 M, if q * v ≤ T then (1 : ℝ) else 0) = ((T / q : ℕ) : ℝ) := by
  rw [← sum_filter]
  have hset : (Icc 1 M).filter (fun v => q * v ≤ T) = Icc 1 (T / q) := by
    ext v
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hv1, _⟩, hqv⟩
      exact ⟨hv1, (Nat.le_div_iff_mul_le hq).mpr (by rw [Nat.mul_comm]; exact hqv)⟩
    · rintro ⟨hv1, hvT⟩
      have hqv : q * v ≤ T := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le hq).mp hvT
      exact ⟨⟨hv1, hvT.trans ((Nat.div_le_self T q).trans hTM)⟩, hqv⟩
  rw [hset, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

/-- Exact cofactor-slice decomposition of `unrestrictedLargePrimePrice n Q`. -/
theorem unrestrictedLargePrimePrice_eq_sum_cofactorThetaSlice (n Q : ℕ) :
    unrestrictedLargePrimePrice n Q = ∑ v ∈ Icc 2 (4 * n), cofactorThetaSlice n Q v := by
  have h1_zero : cofactorThetaSlice n Q 1 = 0 := by
    unfold cofactorThetaSlice
    refine sum_eq_zero fun q hq => ?_
    have hq2 := (mem_Ioc.mp (mem_filter.mp hq).1).2
    rw [mul_one, if_pos (by omega : q ≤ 4 * n), if_pos (by omega : q ≤ 3 * n), if_pos hq2]
    ring
  have hsplit1 : ∑ v ∈ Icc 1 (4 * n), cofactorThetaSlice n Q v =
      ∑ v ∈ Icc 2 (4 * n), cofactorThetaSlice n Q v := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hunion : Icc 1 (4 * n) = insert 1 (Icc 2 (4 * n)) := by
        ext v; simp only [mem_Icc, mem_insert]; omega
      rw [hunion, sum_insert (by simp), h1_zero, zero_add]
  rw [← hsplit1]
  unfold cofactorThetaSlice unrestrictedLargePrimePrice
  rw [sum_comm]
  refine sum_congr rfl fun q hq => ?_
  have hq_pos : 0 < q := (mem_filter.mp hq).2.pos
  rw [← mul_sum, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_Icc_indicator_mul_le hq_pos le_rfl,
    sum_Icc_indicator_mul_le hq_pos (by omega : 3 * n ≤ 4 * n),
    sum_Icc_indicator_mul_le hq_pos (by omega : 2 * n ≤ 4 * n)]
  rfl

/-- For every short cofactor `v ≥ 2` satisfying `v * Q ≤ 2 * n`, both cutoffs `Q` and `2 * n` are
inactive and `cofactorThetaSlice n Q v` equals `θ(⌊4n/v⌋) - 2 θ(⌊3n/v⌋) + θ(⌊2n/v⌋)` identically. -/
theorem cofactorThetaSlice_eq_chebyshev_theta {n Q v : ℕ} (hv : 2 ≤ v) (hvQ : v * Q ≤ 2 * n) :
    cofactorThetaSlice n Q v =
      Chebyshev.theta ((4 * n / v : ℕ) : ℝ) - 2 * Chebyshev.theta ((3 * n / v : ℕ) : ℝ) +
        Chebyshev.theta ((2 * n / v : ℕ) : ℝ) := by
  have hv_pos : 0 < v := by omega
  have hQ_le : Q ≤ 2 * n / v := (Nat.le_div_iff_mul_le hv_pos).mpr (by rw [Nat.mul_comm]; exact hvQ)
  have h4_le : 4 * n / v ≤ 2 * n := by
    have : 4 * n / v ≤ 4 * n / 2 := Nat.div_le_div_left hv (by decide)
    omega
  have hend : ∀ {T : ℕ}, 2 * n ≤ T → Q ≤ T / v → T / v ≤ 2 * n →
      (∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime,
        (Real.log q * if q * v ≤ T then (1 : ℝ) else 0)) -
      (∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime,
        (Real.log q * if q * v ≤ 2 * n then (1 : ℝ) else 0)) =
        Chebyshev.theta ((T / v : ℕ) : ℝ) - Chebyshev.theta ((2 * n / v : ℕ) : ℝ) := by
    intro T h2T_raw hQT hT2
    have h2T : 2 * n / v ≤ T / v := Nat.div_le_div_right h2T_raw
    rw [← sum_sub_distrib]
    have hterm : ∀ q ∈ (Ioc Q (2 * n)).filter Nat.Prime,
        Real.log q * (if q * v ≤ T then (1 : ℝ) else 0) -
          Real.log q * (if q * v ≤ 2 * n then (1 : ℝ) else 0) =
          if 2 * n / v < q ∧ q ≤ T / v then Real.log q else 0 := by
      intro q _
      have hqvT : q * v ≤ T ↔ q ≤ T / v := (Nat.le_div_iff_mul_le hv_pos).symm
      have hqv2 : q * v ≤ 2 * n ↔ q ≤ 2 * n / v := (Nat.le_div_iff_mul_le hv_pos).symm
      simp only [hqvT, hqv2]
      by_cases h1 : q ≤ 2 * n / v
      · rw [if_pos (h1.trans h2T), if_pos h1, if_neg (by omega)]
        ring
      · by_cases h2 : q ≤ T / v
        · rw [if_pos h2, if_neg h1, if_pos ⟨by omega, h2⟩]
          ring
        · rw [if_neg h2, if_neg h1, if_neg (by omega)]
          ring
    rw [sum_congr rfl hterm, ← sum_filter]
    have hset : ((Ioc Q (2 * n)).filter Nat.Prime).filter (fun q => 2 * n / v < q ∧ q ≤ T / v) =
        (Ioc (2 * n / v) (T / v)).filter Nat.Prime := by
      ext q
      simp only [mem_filter, mem_Ioc]
      exact ⟨fun ⟨⟨_, hpr⟩, hlo, hhi⟩ => ⟨⟨hlo, hhi⟩, hpr⟩,
        fun ⟨⟨hlo, hhi⟩, hpr⟩ => ⟨⟨⟨hQ_le.trans_lt hlo, hhi.trans hT2⟩, hpr⟩, hlo, hhi⟩⟩
    rw [hset]
    simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter]
    linarith only [sum_Ioc_consecutive (fun q : ℕ => if q.Prime then Real.log q else 0)
      (Nat.zero_le (2 * n / v)) h2T]
  have h4 := hend (T := 4 * n) (by omega)
    (hQ_le.trans (Nat.div_le_div_right (by omega : 2 * n ≤ 4 * n))) h4_le
  have h3 := hend (T := 3 * n) (by omega)
    (hQ_le.trans (Nat.div_le_div_right (by omega : 2 * n ≤ 3 * n)))
    ((Nat.div_le_div_right (by omega : 3 * n ≤ 4 * n)).trans h4_le)
  have hslice : cofactorThetaSlice n Q v =
      ((∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime, Real.log q * if q * v ≤ 4 * n then (1 : ℝ) else 0) -
        (∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime, Real.log q * if q * v ≤ 2 * n then (1 : ℝ) else 0)) -
      2 * ((∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime, Real.log q * if q * v ≤ 3 * n then (1 : ℝ) else 0) -
        (∑ q ∈ (Ioc Q (2 * n)).filter Nat.Prime, Real.log q * if q * v ≤ 2 * n then (1 : ℝ) else 0)) := by
    unfold cofactorThetaSlice
    rw [← sum_sub_distrib, ← sum_sub_distrib, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun q _ => by ring
  rw [hslice, h4, h3]
  ring

/-- Self-duality along divisible centers `n = m * v` (`v ≥ 2`, `Q ≤ 2 * m`): the `v`-cofactor slice
equals `-primeMidpointPrice m` identically. -/
theorem cofactorThetaSlice_mul_eq_neg_primeMidpointPrice {m Q v : ℕ} (hv : 2 ≤ v) (hQ : Q ≤ 2 * m) :
    cofactorThetaSlice (m * v) Q v = -primeMidpointPrice m := by
  have hv_pos : 0 < v := by omega
  have hvQ : v * Q ≤ 2 * (m * v) := by
    calc v * Q ≤ v * (2 * m) := Nat.mul_le_mul_left v hQ
      _ = 2 * (m * v) := by ring
  rw [cofactorThetaSlice_eq_chebyshev_theta hv hvQ,
    show 4 * (m * v) = (4 * m) * v by ring, show 3 * (m * v) = (3 * m) * v by ring,
    show 2 * (m * v) = (2 * m) * v by ring,
    Nat.mul_div_cancel _ hv_pos, Nat.mul_div_cancel _ hv_pos, Nat.mul_div_cancel _ hv_pos,
    prime_midpoint_price_eq]
  ring

/-! ### Part 3: The prime-center `p^{8/9}` reflected-shell criterion for `Θ_ζ ≤ 5 / 6` -/

/-- **Prime-center `p^{8/9}` reflected-shell equivalence.** `zetaZeroAbscissa ≤ 5 / 6` holds if and
only if at prime centers `p`, the reflected prime price above `p^{8/9}` satisfies
`unrestrictedLargePrimePrice p ⌊p^{8/9}⌋₊ - reflectedDensity · p ≤ C p^t` for every `t ∈ (5 / 6, 1)`. -/
theorem prime_centers_shell_eight_ninths_iff_five_sixths :
    _root_.RHTower.zetaZeroAbscissa ≤ 5 / 6 ↔
      ∀ t : ℝ, 5 / 6 < t → t < 1 → ∃ C : ℝ, ∀ p : ℕ, p.Prime →
        unrestrictedLargePrimePrice p ⌊(p : ℝ) ^ (8 / 9 : ℝ)⌋₊ - reflectedDensity * p ≤
          C * (p : ℝ) ^ t := by
  have hpc : _root_.RHTower.zetaZeroAbscissa ≤ 5 / 6 ↔
      ∀ t : ℝ, 5 / 6 < t → t < 1 → ∃ C : ℝ, ∀ p : ℕ, p.Prime →
        primeMidpointPrice p ≤ C * (p : ℝ) ^ t := by
    rw [← prime_midpoint_upper_spectrum_iff (by norm_num : (1 / 2 : ℝ) ≤ 5 / 6),
      prime_midpoint_iff_eleven_thirds, ← prime_centers_iff_eleven_thirds]
  rw [hpc]
  have h89 : reflectedPrimeShellExponent (5 / 6) = 8 / 9 := reflected_prime_shell_at_five_sixths
  constructor
  · intro h t ht ht1
    obtain ⟨C, hC⟩ := h t ht ht1
    obtain ⟨A, _, hA⟩ := large_prime_shell_linear_center
      (by norm_num : (1 / 2 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1) (sub_pos.mpr ht)
    refine ⟨C + A, fun p hp => ?_⟩
    have herr := (abs_le.mp (hA hp.one_le (by rw [h89]))).2
    rw [show (5 / 6 : ℝ) + (t - 5 / 6) = t by ring] at herr
    rw [add_mul]
    linarith only [herr, hC p hp]
  · intro h t ht ht1
    obtain ⟨C, hC⟩ := h t ht ht1
    obtain ⟨A, _, hA⟩ := large_prime_shell_linear_center
      (by norm_num : (1 / 2 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1) (sub_pos.mpr ht)
    refine ⟨C + A, fun p hp => ?_⟩
    have herr := (abs_le.mp (hA hp.one_le (by rw [h89]))).1
    rw [show (5 / 6 : ℝ) + (t - 5 / 6) = t by ring] at herr
    rw [add_mul]
    linarith only [herr, hC p hp]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
