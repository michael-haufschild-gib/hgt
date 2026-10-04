import GaloisForLFunctions.RHTower.PMRamanujanBandPhysicalSeparation
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Integer-cutoff separation of the complete Ramanujan bands

For `ε > 0` let `h_n = n^ε g_{(n,2n]}` be the normalized logarithmic source vector of the
complete band of denominators `n < q ≤ 2n`.  There is one `c > 0` such that for every fixed
`L²` profile `G` and every integer `B` some integer `n ≥ B` has `‖h_n - G‖ ≥ c`.

**Mechanism.**
* *One complete primitive.*  The floor expansion `P_q(N) = Σ_{de = q} d μ(e) ⌊N/d⌋` gives
  `|P_q(N)| ≤ N τ(q)`; periodicity reduces `N` modulo `q`, so `|P_q(N)| ≤ q τ(q)`.  Hence
  `Σ_{N ≥ 1} |P_q(N)|²/(N(N+1)) ≤ 2 q τ(q)²`: the first `q` terms are at most `τ(q)²` and the
  tail telescopes to at most `q τ(q)²`.
* *Vanishing atom.*  With `|a_ε(q)| ≤ q^{-1-ε}`, the single-denominator band vector satisfies
  `X^ε ‖a_ε(q) P_q‖ ≤ √2 τ(q)/√q` for `X ≤ q`, which tends to zero by the divisor bound.
* *Floor-band interpolation.*  For `n = ⌊X⌋` the real band `(⌊X⌋, ⌊2X⌋]` is `(n, 2n]` plus at
  most the single denominator `2n + 1`, so `G_X = (X/n)^ε h_n + X^ε g_{(2n, ⌊2X⌋]}`.
* *Transfer.*  If `h_n → G` then `G_X → G`, contradicting the real-cutoff separation; completeness
  turns the absence of a limit into one common radius.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

/-! ## One complete primitive -/

/-- `|P_q(N)| ≤ N τ(q)`, from the floor expansion and `|μ| ≤ 1`. -/
theorem norm_pmRamanujanPrimitive_le_mul_card (q N : ℕ) :
    ‖pmRamanujanPrimitive q N‖ ≤ (N : ℝ) * q.divisors.card := by
  rw [pmRamanujanPrimitive_eq_floor,
    Nat.sum_divisorsAntidiagonal (fun d e => (d : ℂ) * (ArithmeticFunction.moebius e : ℂ) *
      ((N / d : ℕ) : ℂ))]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  have hμ : ‖((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hdiv : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Nat.cast_one, mul_one]
  have hnn : (0 : ℝ) ≤ (d : ℝ) * ((N / d : ℕ) : ℝ) := by positivity
  calc (d : ℝ) * ‖((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)‖ * ((N / d : ℕ) : ℝ) ≤
        (d : ℝ) * 1 * ((N / d : ℕ) : ℝ) := by gcongr
    _ ≤ N := by nlinarith

/-- `|P_q(N)| ≤ (N mod q) τ(q) ≤ q τ(q)` by periodicity. -/
theorem norm_pmRamanujanPrimitive_le_self_mul_card {q : ℕ} (hq : 1 < q) (N : ℕ) :
    ‖pmRamanujanPrimitive q N‖ ≤ (q : ℝ) * q.divisors.card := by
  have hp : Function.Periodic (pmRamanujanPrimitive q) q := pmRamanujanPrimitive_periodic hq
  rw [← hp.map_mod_nat N]
  refine (norm_pmRamanujanPrimitive_le_mul_card q (N % q)).trans ?_
  have : ((N % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt N (by omega)).le
  gcongr

private theorem one_div_mul_succ (n : ℕ) :
    1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1) := by
  field_simp
  ring

/-- **Hilbert bound for one complete primitive.**
`Σ_{N ≥ 1} |P_q(N)|²/(N(N+1)) ≤ 2 q τ(q)²`. -/
theorem tsum_norm_sq_pmRamanujanPrimitive_le {q : ℕ} (hq : 1 < q) :
    ∑' n : ℕ, ‖pmRamanujanPrimitive q (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
      2 * q * (q.divisors.card : ℝ) ^ 2 := by
  set τ : ℝ := (q.divisors.card : ℝ)
  have hτ : 0 ≤ τ := by positivity
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  set h : ℕ → ℝ := fun n => if n < q then 1 else (q : ℝ) ^ 2 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1))
  have hh0 : ∀ n, 0 ≤ h n := by
    intro n
    simp only [h]
    split_ifs
    · norm_num
    · rw [← one_div_mul_succ]; positivity
  have hterm : ∀ n, ‖pmRamanujanPrimitive q (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
      τ ^ 2 * h n := by
    intro n
    have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
    simp only [h]
    split_ifs with hn
    · have hb := norm_pmRamanujanPrimitive_le_mul_card q (n + 1)
      push_cast at hb
      rw [div_le_iff₀ hden, mul_one]
      have h0 : 0 ≤ ‖pmRamanujanPrimitive q (n + 1)‖ := norm_nonneg _
      have := pow_le_pow_left₀ h0 hb 2
      nlinarith
    · have hb := norm_pmRamanujanPrimitive_le_self_mul_card hq (n + 1)
      have h0 : 0 ≤ ‖pmRamanujanPrimitive q (n + 1)‖ := norm_nonneg _
      have hsq := pow_le_pow_left₀ h0 hb 2
      rw [← one_div_mul_succ, div_eq_mul_one_div]
      calc ‖pmRamanujanPrimitive q (n + 1)‖ ^ 2 * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤
            ((q : ℝ) * τ) ^ 2 * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = τ ^ 2 * ((q : ℝ) ^ 2 * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) := by ring
  have hsum : ∀ M : ℕ, ∑ n ∈ Finset.range M, h n ≤ 2 * q := by
    intro M
    have hext : ∑ n ∈ Finset.range M, h n ≤ ∑ n ∈ Finset.range (q + M), h n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        fun n _ _ => hh0 n
    refine hext.trans ?_
    rw [Finset.sum_range_add]
    have hlow : ∑ n ∈ Finset.range q, h n = q := by
      have hone : ∀ n ∈ Finset.range q, h n = 1 := fun n hn => by
        simp only [h, if_pos (Finset.mem_range.mp hn)]
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hhigh : ∑ k ∈ Finset.range M, h (q + k) =
        (q : ℝ) ^ 2 * (1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + M + 1)) := by
      have he : ∀ k ∈ Finset.range M, h (q + k) =
          (q : ℝ) ^ 2 * (1 / ((q : ℝ) + k + 1) - 1 / ((q : ℝ) + (k + 1 : ℕ) + 1)) := by
        intro k _
        simp only [h, if_neg (show ¬ q + k < q by omega)]
        push_cast
        ring_nf
      rw [Finset.sum_congr rfl he, ← Finset.mul_sum,
        Finset.sum_range_sub' (fun k : ℕ => 1 / ((q : ℝ) + k + 1)) M]
      push_cast
      ring
    rw [hlow, hhigh]
    have h1 : (q : ℝ) ^ 2 * (1 / ((q : ℝ) + 1)) ≤ q := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    have h2 : 0 ≤ (q : ℝ) ^ 2 * (1 / ((q : ℝ) + M + 1)) := by positivity
    nlinarith
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun M => ?_
  calc ∑ n ∈ Finset.range M, ‖pmRamanujanPrimitive q (n + 1)‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ ∑ n ∈ Finset.range M, τ ^ 2 * h n :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = τ ^ 2 * ∑ n ∈ Finset.range M, h n := by rw [Finset.mul_sum]
    _ ≤ τ ^ 2 * (2 * q) := mul_le_mul_of_nonneg_left (hsum M) (sq_nonneg _)
    _ = 2 * q * τ ^ 2 := by ring

/-! ## The single-denominator atom -/

theorem pmRamanujanDenominatorBand_succ (ε : ℝ) (m N : ℕ) :
    pmRamanujanDenominatorBand ε m (m + 1) N =
      pmPowerDampedRamanujanWeight ε (m + 1) * pmRamanujanPrimitive (m + 1) N := by
  rw [pmRamanujanDenominatorBand, Nat.Ioc_succ_singleton, Finset.sum_singleton]

/-- **Atom Hilbert estimate.**  The single-denominator band vector `a_ε(q) P_q`, `q = m + 1`,
has `‖·‖² ≤ q^{-2-2ε} · 2 q τ(q)²`. -/
theorem norm_sq_pmRamanujanBandLogVector_succ_le {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) :
    ‖pmRamanujanBandLogVector ε m (m + 1) hm‖ ^ 2 ≤
      (1 / ((m + 1 : ℕ) : ℝ) ^ (1 + ε)) ^ 2 *
        (2 * (m + 1 : ℕ) * ((m + 1).divisors.card : ℝ) ^ 2) := by
  rw [norm_sq_pmRamanujanBandLogVector_eq_energy]
  have hw := norm_pmPowerDampedRamanujanWeight_le hε (show 0 < m + 1 by omega)
  have hP := tsum_norm_sq_pmRamanujanPrimitive_le (show 1 < m + 1 by omega)
  have he : (fun n : ℕ => ‖pmRamanujanDenominatorBand ε m (m + 1) (n + 1)‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2))) = fun n : ℕ => ‖pmPowerDampedRamanujanWeight ε (m + 1)‖ ^ 2 *
        (‖pmRamanujanPrimitive (m + 1) (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    funext n
    rw [pmRamanujanDenominatorBand_succ, norm_mul, mul_pow, mul_div_assoc]
  rw [he, tsum_mul_left]
  have hw2 : ‖pmPowerDampedRamanujanWeight ε (m + 1)‖ ^ 2 ≤ (1 / ((m + 1 : ℕ) : ℝ) ^ (1 + ε)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hT : 0 ≤ ∑' n : ℕ, ‖pmRamanujanPrimitive (m + 1) (n + 1)‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2)) := tsum_nonneg fun n => by positivity
  calc ‖pmPowerDampedRamanujanWeight ε (m + 1)‖ ^ 2 * ∑' n : ℕ,
        ‖pmRamanujanPrimitive (m + 1) (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
        (1 / ((m + 1 : ℕ) : ℝ) ^ (1 + ε)) ^ 2 * ∑' n : ℕ,
          ‖pmRamanujanPrimitive (m + 1) (n + 1)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hw2 hT
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (sq_nonneg _)

/-- The atom is invisible after the cutoff normalization: for `0 < X ≤ q = m + 1`,
`X^ε ‖a_ε(q) P_q‖ ≤ √2 τ(q) / √q`. -/
theorem rpow_mul_norm_pmRamanujanBandLogVector_succ_le {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m)
    {X : ℝ} (hX : 0 < X) (hXq : X ≤ ((m + 1 : ℕ) : ℝ)) :
    X ^ ε * ‖pmRamanujanBandLogVector ε m (m + 1) hm‖ ≤
      Real.sqrt 2 * ((m + 1).divisors.card : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  set q : ℝ := ((m + 1 : ℕ) : ℝ)
  set τ : ℝ := ((m + 1).divisors.card : ℝ)
  have hq : 0 < q := by positivity
  have hτ : 0 ≤ τ := by positivity
  have hnorm := norm_sq_pmRamanujanBandLogVector_succ_le hε hm
  have hsq : ‖pmRamanujanBandLogVector ε m (m + 1) hm‖ ≤ 1 / q ^ (1 + ε) * (Real.sqrt (2 * q) * τ) := by
    have hrhs : 0 ≤ 1 / q ^ (1 + ε) * (Real.sqrt (2 * q) * τ) := by positivity
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hrhs]
    refine Real.sqrt_le_sqrt (hnorm.trans (le_of_eq ?_))
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hXε : X ^ ε ≤ q ^ ε := Real.rpow_le_rpow hX.le hXq hε.le
  have hpow : q ^ ε * (1 / q ^ (1 + ε)) = 1 / q := by
    rw [Real.rpow_add hq, Real.rpow_one]
    field_simp
  have hs2q : Real.sqrt (2 * q) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) q
  have hsq_q : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  calc X ^ ε * ‖pmRamanujanBandLogVector ε m (m + 1) hm‖ ≤
        q ^ ε * (1 / q ^ (1 + ε) * (Real.sqrt (2 * q) * τ)) :=
        mul_le_mul hXε hsq (norm_nonneg _) (by positivity)
    _ = 1 / q * (Real.sqrt (2 * q) * τ) := by rw [← mul_assoc, hpow]
    _ = Real.sqrt 2 * τ / Real.sqrt q := by
        rw [hs2q]
        field_simp
        linear_combination τ * hsq_q

/-! ## Floor-band interpolation -/

theorem pmRamanujanBandLogVector_add (ε : ℝ) {X Y Z : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hXY : X ≤ Y) (hYZ : Y ≤ Z) :
    pmRamanujanBandLogVector ε X Z hX =
      pmRamanujanBandLogVector ε X Y hX + pmRamanujanBandLogVector ε Y Z hY := by
  unfold pmRamanujanBandLogVector
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards with u
  simp only [Pi.add_apply, pmRamanujanBandLogSource, pmRamanujanDenominatorBand, ← smul_add,
    Finset.sum_Ioc_consecutive _ hXY hYZ]

theorem pmRamanujanBandLogVector_self (ε : ℝ) {Y : ℕ} (hY : 1 ≤ Y) :
    pmRamanujanBandLogVector ε Y Y hY = 0 := by
  have h := norm_sq_pmRamanujanBandLogVector_eq_energy ε (X := Y) (Y := Y) hY
  simp only [pmRamanujanDenominatorBand, Finset.Ioc_self, Finset.sum_empty, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, tsum_zero] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

/-- The normalized integer band `h_n = n^ε g_{(n,2n]}`. -/
def pmRamanujanIntegerBandLogVector (ε : ℝ) (n : ℕ) : SoninL2 :=
  if hn : 1 ≤ n then (((n : ℝ) ^ ε : ℝ) : ℂ) • pmRamanujanBandLogVector ε n (2 * n) hn else 0

private theorem two_mul_floor_le_floor {X : ℝ} (hX : 0 ≤ X) : 2 * ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := by
  apply Nat.le_floor
  push_cast
  linarith [Nat.floor_le hX]

private theorem floor_two_mul_le {X : ℝ} (hX : 0 ≤ X) : ⌊2 * X⌋₊ ≤ 2 * ⌊X⌋₊ + 1 := by
  have h := Nat.lt_floor_add_one X
  have : ⌊2 * X⌋₊ < 2 * ⌊X⌋₊ + 2 := by
    rw [Nat.floor_lt (by linarith)]
    push_cast
    linarith
  omega

/-- **Floor-band interpolation.**  `G_X = (X/n)^ε h_n + X^ε g_{(2n, ⌊2X⌋]}` with `n = ⌊X⌋`. -/
theorem pmRamanujanNormalizedBandLogVector_eq {ε X : ℝ} (hX : 1 ≤ X) :
    pmRamanujanNormalizedBandLogVector ε X =
      (((X / ⌊X⌋₊) ^ ε : ℝ) : ℂ) • pmRamanujanIntegerBandLogVector ε ⌊X⌋₊ +
        ((X ^ ε : ℝ) : ℂ) • pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) ⌊2 * X⌋₊
          (by have := Nat.one_le_floor_iff X |>.mpr hX; omega) := by
  have hn : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
  have h2n : 1 ≤ 2 * ⌊X⌋₊ := by omega
  have hX0 : 0 < X := by linarith
  have hnR : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast hn
  unfold pmRamanujanNormalizedBandLogVector pmRamanujanNaturalBandLogVector
    pmRamanujanIntegerBandLogVector
  rw [dif_pos hn, dif_pos hn, pmRamanujanBandLogVector_add ε hn h2n (by omega)
    (two_mul_floor_le_floor hX0.le), smul_add, smul_smul]
  congr 2
  rw [← Complex.ofReal_mul, Real.div_rpow hX0.le hnR.le, div_mul_cancel₀ _
    (Real.rpow_pos_of_pos hnR ε).ne']

/-- The remainder band `(2n, ⌊2X⌋]` is empty or the single atom `2n + 1`. -/
theorem rpow_mul_norm_remainder_le {ε X : ℝ} (hε : 0 < ε) (hX : 1 ≤ X)
    (h2n : 1 ≤ 2 * ⌊X⌋₊) :
    X ^ ε * ‖pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) ⌊2 * X⌋₊ h2n‖ ≤
      Real.sqrt 2 * ((2 * ⌊X⌋₊ + 1).divisors.card : ℝ) /
        Real.sqrt ((2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hrhs : 0 ≤ Real.sqrt 2 * ((2 * ⌊X⌋₊ + 1).divisors.card : ℝ) /
      Real.sqrt ((2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) := by positivity
  rcases (show ⌊2 * X⌋₊ = 2 * ⌊X⌋₊ ∨ ⌊2 * X⌋₊ = 2 * ⌊X⌋₊ + 1 by
    have := two_mul_floor_le_floor hX0.le; have := floor_two_mul_le hX0.le; omega) with h | h
  · have hz : pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) ⌊2 * X⌋₊ h2n = 0 := by
      have e : ∀ (Z : ℕ) (hZ : Z = 2 * ⌊X⌋₊),
          pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) Z h2n = 0 := by
        rintro Z rfl; exact pmRamanujanBandLogVector_self ε h2n
      exact e _ h
    rw [hz, norm_zero, mul_zero]
    exact hrhs
  · have e : ∀ (Z : ℕ) (hZ : Z = 2 * ⌊X⌋₊ + 1),
        X ^ ε * ‖pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) Z h2n‖ ≤
          Real.sqrt 2 * ((2 * ⌊X⌋₊ + 1).divisors.card : ℝ) /
            Real.sqrt ((2 * ⌊X⌋₊ + 1 : ℕ) : ℝ) := by
      rintro Z rfl
      refine rpow_mul_norm_pmRamanujanBandLogVector_succ_le hε h2n hX0 ?_
      have := Nat.lt_floor_add_one X
      push_cast
      linarith
    exact e _ h

/-- The atom bound tends to zero: `√2 τ(q)/√q → 0` along `q = 2n + 1`. -/
theorem tendsto_atom_bound :
    Tendsto (fun n : ℕ => Real.sqrt 2 * ((2 * n + 1).divisors.card : ℝ) /
      Real.sqrt ((2 * n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hdiv⟩ := card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 4 by norm_num)
  have hq : Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_atTop_mono (fun n => show n ≤ 2 * n + 1 by omega) tendsto_id
  have hlim : Tendsto (fun n : ℕ => Real.sqrt 2 * C * ((2 * n + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hq).const_mul
        (Real.sqrt 2 * C)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  set q : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  have hq0 : 0 < q := by positivity
  have hτ := hdiv (2 * n + 1) (by omega)
  have hsq : Real.sqrt q = q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow q
  have hsplit : q ^ (1 / 4 : ℝ) / q ^ (1 / 2 : ℝ) = q ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_sub hq0]; norm_num
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hq0), hsq]
  have hpos : 0 < q ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have : q ^ (-(1 / 4 : ℝ)) * q ^ (1 / 2 : ℝ) = q ^ (1 / 4 : ℝ) := by
    rw [← hsplit, div_mul_cancel₀ _ hpos.ne']
  calc Real.sqrt 2 * ((2 * n + 1).divisors.card : ℝ) ≤ Real.sqrt 2 * (C * q ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hτ (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * C * q ^ (-(1 / 4 : ℝ)) * q ^ (1 / 2 : ℝ) := by rw [mul_assoc _ _ (q ^ (1/2 : ℝ)), this]; ring

/-! ## Transfer and the uniform radius -/

/-- **No integer limit.**  The normalized integer bands do not converge to any `L²` profile. -/
theorem not_tendsto_pmRamanujanIntegerBandLogVector {ε : ℝ} (hε : 0 < ε) (G : SoninL2) :
    ¬ Tendsto (pmRamanujanIntegerBandLogVector ε) atTop (𝓝 G) := by
  intro hG
  apply not_tendsto_pmRamanujanNormalizedBandLogVector hε G
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfloor : Tendsto (fun X : ℝ => ⌊X⌋₊) atTop atTop := tendsto_nat_floor_atTop
  -- the profile term
  have h1 : Tendsto (fun X : ℝ => ‖pmRamanujanIntegerBandLogVector ε ⌊X⌋₊ - G‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hG).comp hfloor
  -- the scale term
  have hratio : Tendsto (fun X : ℝ => X / ⌊X⌋₊) atTop (𝓝 1) := by
    have := (tendsto_nat_floor_div_atTop (R := ℝ)).inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using this
  have hpow : Tendsto (fun X : ℝ => (X / ⌊X⌋₊) ^ ε - 1) atTop (𝓝 0) := by
    have hc := ((Real.continuousAt_rpow_const 1 ε (Or.inl one_ne_zero)).tendsto.comp hratio).sub_const 1
    simpa only [Real.one_rpow, sub_self, Function.comp_def] using hc
  have hbdd : Tendsto (fun X : ℝ => ‖pmRamanujanIntegerBandLogVector ε ⌊X⌋₊‖) atTop (𝓝 ‖G‖) :=
    (hG.comp hfloor).norm
  have h2 : Tendsto (fun X : ℝ => |(X / ⌊X⌋₊) ^ ε - 1| * ‖pmRamanujanIntegerBandLogVector ε ⌊X⌋₊‖)
      atTop (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hpow.abs.mul hbdd
  -- the atom term
  have h3 : Tendsto (fun X : ℝ => Real.sqrt 2 * ((2 * ⌊X⌋₊ + 1).divisors.card : ℝ) /
      Real.sqrt ((2 * ⌊X⌋₊ + 1 : ℕ) : ℝ)) atTop (𝓝 0) := tendsto_atom_bound.comp hfloor
  refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_
    (by simpa only [add_zero] using (h2.add h1).add h3)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hn : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
  have h2n : 1 ≤ 2 * ⌊X⌋₊ := by omega
  have hX0 : 0 < X := by linarith
  rw [pmRamanujanNormalizedBandLogVector_eq hX]
  set h := pmRamanujanIntegerBandLogVector ε ⌊X⌋₊
  set r := pmRamanujanBandLogVector ε (2 * ⌊X⌋₊) ⌊2 * X⌋₊ h2n
  have hdecomp : (((X / ⌊X⌋₊) ^ ε : ℝ) : ℂ) • h + ((X ^ ε : ℝ) : ℂ) • r - G =
      ((((X / ⌊X⌋₊) ^ ε - 1 : ℝ)) : ℂ) • h + (h - G) + ((X ^ ε : ℝ) : ℂ) • r := by
    push_cast
    rw [sub_smul, one_smul]
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ le_rfl)) ?_)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 ε)]
    exact rpow_mul_norm_remainder_le hε hX h2n

theorem not_cauchySeq_pmRamanujanIntegerBandLogVector {ε : ℝ} (hε : 0 < ε) :
    ¬ CauchySeq (pmRamanujanIntegerBandLogVector ε) := by
  intro hc
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hc
  exact not_tendsto_pmRamanujanIntegerBandLogVector hε G hG

/-- **Integer-cutoff separation.**  For every `ε > 0` there is `c > 0` such that for every fixed
logarithmic `L²` profile `G` and every integer `B` some integer `n ≥ B` has
`‖n^ε g_{(n,2n]} - G‖ ≥ c`. -/
theorem exists_uniform_pmRamanujanIntegerBand_separation {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ G : SoninL2, ∀ B : ℕ,
      ∃ n : ℕ, B ≤ n ∧ c ≤ ‖pmRamanujanIntegerBandLogVector ε n - G‖ := by
  have hn := not_cauchySeq_pmRamanujanIntegerBandLogVector hε
  rw [Metric.cauchySeq_iff] at hn
  push Not at hn
  obtain ⟨c, hc, h⟩ := hn
  refine ⟨c / 2, half_pos hc, fun G B => ?_⟩
  obtain ⟨n, hn, m, hm, hnm⟩ := h B
  by_cases hnG : c / 2 ≤ dist (pmRamanujanIntegerBandLogVector ε n) G
  · exact ⟨n, hn, by simpa only [dist_eq_norm] using hnG⟩
  · refine ⟨m, hm, ?_⟩
    have ht := dist_triangle (pmRamanujanIntegerBandLogVector ε n) G
      (pmRamanujanIntegerBandLogVector ε m)
    rw [dist_comm G] at ht
    rw [← dist_eq_norm]
    exact le_of_lt (by linarith [lt_of_not_ge hnG])

end RHTower
