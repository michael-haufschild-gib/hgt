import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareRightLine
import GaloisForLFunctions.RHTower.SpurRescale
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import GaloisForLFunctions.BezoutValuationIncidence.PolynomialWindowTranslatedMomentTransfer
import GaloisForLFunctions.BiScaleUncertainty.TwoLagSievePeriod
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The physical damping diagonal of prime pairs

The normalized divisor response approximates von Mangoldt uniformly on a
finite interval. The resulting pair error keeps an explicit damping factor,
so damping can decrease with the physical horizon.

Exact Möbius compensation bounds the normalized coefficients by logarithms.
Transferring that weight to the complementary divisor removes unit cofactors.
On cofactor rectangles, the literal CRT count removes damping uniformly,
including every endpoint error, on a clock that still resolves prime pairs.
-/

namespace TwinPrime

open Finset ArithmeticFunction RHTower
open Filter Topology

noncomputable section

/-- The divisor response at its first-order damping scale. -/
def normalizedDampedResponse (ε : ℝ) (n : ℕ) : ℝ :=
  pmPowerDampedDivisorCoeff ε n / ε

theorem normalizedDampedResponse_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ normalizedDampedResponse ε n :=
  div_nonneg (pmPowerDampedDivisorCoeff_nonneg hε.le n) hε.le

theorem normalizedDampedResponse_le_log {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 2 ≤ n) : normalizedDampedResponse ε n ≤ Real.log n := by
  rw [normalizedDampedResponse, div_le_iff₀ hε]
  simpa only [mul_comm] using
    BAGTrace.pmPowerDampedDivisorCoeff_le_damping_log hε.le (by omega : 1 < n)

private theorem prime_factor_nonneg {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - (p : ℝ) ^ (-ε) := by
  exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hp.one_le) (neg_nonpos.mpr hε))

private theorem prime_factor_le (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    1 - (p : ℝ) ^ (-ε) ≤ ε * Real.log p := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
  linarith [Real.add_one_le_exp (Real.log p * (-ε))]

/-- Two distinct prime factors supply a second damping factor. -/
theorem dampedResponse_le_quadratic_of_not_primePow {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n) :
    pmPowerDampedDivisorCoeff ε n ≤ ε ^ 2 * (Real.log n) ^ 2 / 4 := by
  obtain ⟨p, hpm, q, hqm, hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hnp
  have hp := Nat.prime_of_mem_primeFactors hpm
  have hq := Nat.prime_of_mem_primeFactors hqm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hqL : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_le)
  have hnL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hpnd : p ∣ n := (Nat.mem_primeFactors.mp hpm).2.1
  have hqnd : q ∣ n := (Nat.mem_primeFactors.mp hqm).2.1
  have hprod : p * q ∣ n :=
    ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpnd hqnd
  have hlog : Real.log p + Real.log q ≤ Real.log n := by
    rw [← Real.log_mul hp0.ne' hq0.ne']
    exact Real.log_le_log (mul_pos hp0 hq0)
      (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < n) hprod)
  have hlogs : Real.log p * Real.log q ≤ (Real.log n) ^ 2 / 4 := by
    have hsq : (Real.log p + Real.log q) ^ 2 ≤ (Real.log n) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg hpL hqL) hlog 2
    nlinarith [sq_nonneg (Real.log p - Real.log q)]
  have hsub : ({p, q} : Finset ℕ) ⊆ n.primeFactors := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hpm, hqm⟩
  have hkeep := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun p : ℕ => 1 - (p : ℝ) ^ (-ε)) hsub
    (fun p hp => prime_factor_nonneg hε (Nat.prime_of_mem_primeFactors hp))
    (fun p _ _ => by linarith [Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)])
  rw [Finset.prod_insert (by simpa using hpq), Finset.prod_singleton] at hkeep
  rw [pmPowerDampedDivisorCoeff_eq_prod ε (by omega : n ≠ 0)]
  calc
    _ ≤ (1 - (p : ℝ) ^ (-ε)) * (1 - (q : ℝ) ^ (-ε)) := hkeep
    _ ≤ (ε * Real.log p) * (ε * Real.log q) :=
      mul_le_mul (prime_factor_le ε hp) (prime_factor_le ε hq)
        (prime_factor_nonneg hε hq) (mul_nonneg hε hpL)
    _ = ε ^ 2 * (Real.log p * Real.log q) := by ring
    _ ≤ ε ^ 2 * ((Real.log n) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hlogs (sq_nonneg ε)
    _ = _ := by ring

/-- Uniform first-order approximation, including integers with several prime factors. -/
theorem normalizedDampedResponse_error {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 2 ≤ n) :
    |normalizedDampedResponse ε n - vonMangoldt n| ≤ ε * (Real.log n) ^ 2 / 2 := by
  by_cases hnp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hnp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hpk : p ≤ p ^ k := Nat.le_of_dvd (pow_pos hp.pos k) (dvd_pow_self p hk.ne')
    have hlog : Real.log p ≤ Real.log (p ^ k : ℕ) :=
      Real.log_le_log hp0 (by exact_mod_cast hpk)
    have hlogsq := pow_le_pow_left₀ hpL hlog 2
    have htop : (1 - (p : ℝ) ^ (-ε)) / ε ≤ Real.log p := by
      apply (div_le_iff₀ hε).mpr
      simpa only [mul_comm] using prime_factor_le ε hp
    have hquad := exp_neg_le_quadratic (mul_nonneg hε.le hpL)
    have hbottom : Real.log p - ε * (Real.log p) ^ 2 / 2 ≤
        (1 - (p : ℝ) ^ (-ε)) / ε := by
      apply (le_div_iff₀ hε).mpr
      rw [Real.rpow_def_of_pos hp0]
      have he : Real.log p * (-ε) = -(ε * Real.log p) := by ring
      rw [he]
      nlinarith only [hquad]
    rw [normalizedDampedResponse,
      pmPowerDampedDivisorCoeff_eq_prod ε (pow_ne_zero k hp.ne_zero),
      Nat.primeFactors_pow p hk.ne', hp.primeFactors, Finset.prod_singleton,
      vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htop)]
    calc
      _ ≤ ε * (Real.log p) ^ 2 / 2 := by linarith
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogsq hε.le) (by norm_num)
  · rw [vonMangoldt_eq_zero_iff.mpr hnp, sub_zero,
      abs_of_nonneg (normalizedDampedResponse_nonneg hε n), normalizedDampedResponse]
    apply (div_le_iff₀ hε).mpr
    have hbound := dampedResponse_le_quadratic_of_not_primePow hε.le hn hnp
    nlinarith only [hbound, mul_nonneg (sq_nonneg ε) (sq_nonneg (Real.log n))]

/-- A positive damping clock gives an approximation at every physical index. -/
theorem normalizedDampedResponse_exp_error (t : ℝ) (n : ℕ) :
    |normalizedDampedResponse (Real.exp (-t)) (n + 2) - vonMangoldt (n + 2)| ≤
      Real.exp (-t) * (Real.log (n + 2 : ℕ)) ^ 2 / 2 :=
  normalizedDampedResponse_error (Real.exp_pos _) (by omega)

private theorem damped_pair_error {ε : ℝ} (hε : 0 < ε)
    {n m K : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hnK : n ≤ K) (hmK : m ≤ K) :
    |normalizedDampedResponse ε n * normalizedDampedResponse ε m -
        vonMangoldt n * vonMangoldt m| ≤ ε * (Real.log K) ^ 3 := by
  let L := Real.log K
  have hnL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hmL : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hnL' : Real.log n ≤ L :=
    Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnK)
  have hmL' : Real.log m ≤ L :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmK)
  have hL : 0 ≤ L := hnL.trans hnL'
  have hen : |normalizedDampedResponse ε n - vonMangoldt n| ≤ ε * L ^ 2 / 2 :=
    (normalizedDampedResponse_error hε hn).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnL hnL' 2) hε.le) (by norm_num))
  have hem : |normalizedDampedResponse ε m - vonMangoldt m| ≤ ε * L ^ 2 / 2 :=
    (normalizedDampedResponse_error hε hm).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmL hmL' 2) hε.le) (by norm_num))
  have hrm : normalizedDampedResponse ε m ≤ L :=
    (normalizedDampedResponse_le_log hε hm).trans hmL'
  have hΛn : vonMangoldt n ≤ L := vonMangoldt_le_log.trans hnL'
  have hE : 0 ≤ ε * L ^ 2 / 2 := by positivity
  calc
    _ = |(normalizedDampedResponse ε n - vonMangoldt n) * normalizedDampedResponse ε m +
        vonMangoldt n * (normalizedDampedResponse ε m - vonMangoldt m)| := by
      congr 1
      ring
    _ ≤ |(normalizedDampedResponse ε n - vonMangoldt n) * normalizedDampedResponse ε m| +
        |vonMangoldt n * (normalizedDampedResponse ε m - vonMangoldt m)| := abs_add_le _ _
    _ = |normalizedDampedResponse ε n - vonMangoldt n| * normalizedDampedResponse ε m +
        vonMangoldt n * |normalizedDampedResponse ε m - vonMangoldt m| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (normalizedDampedResponse_nonneg hε m),
        abs_of_nonneg vonMangoldt_nonneg]
    _ ≤ (ε * L ^ 2 / 2) * L + L * (ε * L ^ 2 / 2) :=
      add_le_add (mul_le_mul hen hrm (normalizedDampedResponse_nonneg hε m) hE)
        (mul_le_mul hΛn hem (abs_nonneg _) hL)
    _ = _ := by dsimp [L]; ring

private theorem interval_average_abs_le (f : ℕ → ℝ) (X : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n ∈ Icc 2 X, |f n| ≤ C) : |(∑ n ∈ Icc 2 X, f n) / X| ≤ C := by
  by_cases hX : X = 0
  · simp only [hX, Nat.cast_zero, div_zero, abs_zero, hC]
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  rw [abs_div, abs_of_pos hXpos, div_le_iff₀ hXpos]
  calc
    _ ≤ ∑ n ∈ Icc 2 X, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Icc 2 X, C := sum_le_sum hf
    _ = ((Icc 2 X).card : ℝ) * C := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (X : ℝ) * C := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (Icc 2 X).card ≤ X by rw [Nat.card_Icc]; omega)) hC
    _ = _ := mul_comm _ _

/-- The physical average of the two normalized divisor responses. -/
def dampedPairAverage (ε : ℝ) (X h : ℕ) : ℝ :=
  (∑ n ∈ Icc 2 X, normalizedDampedResponse ε n * normalizedDampedResponse ε (n + h)) / X

/-- The matching von Mangoldt pair average. -/
def mangoldtPairAverage (X h : ℕ) : ℝ :=
  (∑ n ∈ Icc 2 X, vonMangoldt n * vonMangoldt (n + h)) / X

/-- Squarefree projection of the physical divisor response. -/
def projectedDampedPairAverage (ε : ℝ) (X h : ℕ) : ℝ :=
  (∑ n ∈ Icc 2 X, (moebius n : ℝ) ^ 2 * (moebius (n + h) : ℝ) ^ 2 *
    (normalizedDampedResponse ε n * normalizedDampedResponse ε (n + h))) / X

/-- The actual logarithmically weighted prime pairs. -/
def primePairLogAverage (X h : ℕ) : ℝ :=
  (∑ n ∈ Icc 2 X, if n.Prime ∧ (n + h).Prime then
    Real.log n * Real.log (n + h : ℕ) else 0) / X

private theorem moebius_sq_mangoldt (n : ℕ) :
    (moebius n : ℝ) ^ 2 * vonMangoldt n = if n.Prime then Real.log n else 0 := by
  by_cases hp : n.Prime
  · simp only [hp, if_true, moebius_apply_prime hp, Int.cast_neg, Int.cast_one,
      neg_one_sq, one_mul, vonMangoldt_apply_prime hp]
  · rw [if_neg hp]
    by_cases hn : IsPrimePow n
    · rw [moebius_apply_isPrimePow_not_prime hn hp]
      simp only [Int.cast_zero, zero_pow two_ne_zero, zero_mul]
    · rw [vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

private theorem projected_mangoldt_pair (n m : ℕ) :
    (moebius n : ℝ) ^ 2 * (moebius m : ℝ) ^ 2 * (vonMangoldt n * vonMangoldt m) =
      if n.Prime ∧ m.Prime then Real.log n * Real.log m else 0 := by
  calc
    _ = ((moebius n : ℝ) ^ 2 * vonMangoldt n) *
        ((moebius m : ℝ) ^ 2 * vonMangoldt m) := by ring
    _ = _ := by
      rw [moebius_sq_mangoldt, moebius_sq_mangoldt]
      by_cases hn : n.Prime <;> by_cases hm : m.Prime <;>
        simp only [hn, hm, and_self, and_false, false_and, if_true, if_false,
          mul_zero, zero_mul]

private theorem abs_moebius_sq_le_one (n : ℕ) : |(moebius n : ℝ) ^ 2| ≤ 1 := by
  rcases moebius_eq_or n with h | h | h <;> simp only [h] <;> norm_num

private theorem dampedPairAverage_error {ε : ℝ} (hε : 0 < ε) (X h : ℕ) :
    |dampedPairAverage ε X h - mangoldtPairAverage X h| ≤
      ε * (Real.log (X + h + 2 : ℕ)) ^ 3 := by
  rw [dampedPairAverage, mangoldtPairAverage, ← sub_div, ← sum_sub_distrib]
  apply interval_average_abs_le
  · have : 0 ≤ Real.log (X + h + 2 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + h + 2 by omega))
    positivity
  · intro n hn
    have hnI := mem_Icc.mp hn
    exact damped_pair_error hε hnI.1 (by omega) (by omega) (by omega)

private theorem projectedDampedPairAverage_error {ε : ℝ} (hε : 0 < ε) (X h : ℕ) :
    |projectedDampedPairAverage ε X h - primePairLogAverage X h| ≤
      ε * (Real.log (X + h + 2 : ℕ)) ^ 3 := by
  rw [projectedDampedPairAverage, primePairLogAverage, ← sub_div, ← sum_sub_distrib]
  apply interval_average_abs_le
  · have : 0 ≤ Real.log (X + h + 2 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + h + 2 by omega))
    positivity
  · intro n hn
    have hnI := mem_Icc.mp hn
    rw [← projected_mangoldt_pair, ← mul_sub, abs_mul, abs_mul]
    have hw : |(moebius n : ℝ) ^ 2| * |(moebius (n + h) : ℝ) ^ 2| ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (abs_moebius_sq_le_one n)
        (abs_moebius_sq_le_one (n + h)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (mul_le_of_le_one_left (abs_nonneg _) hw).trans
      (damped_pair_error hε hnI.1 (by omega) (by omega) (by omega))

/-- Damping shrinks fast enough to resolve a pair at the physical horizon. -/
def physicalPairDamping (X h : ℕ) : ℝ := (Real.log (X + h + 2 : ℕ))⁻¹ ^ 4

theorem physicalPairDamping_pos (X h : ℕ) : 0 < physicalPairDamping X h := by
  have : 0 < Real.log (X + h + 2 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X + h + 2 by omega))
  exact pow_pos (inv_pos.mpr this) 4

private theorem physicalPairDamping_error_scale (X h : ℕ) :
    physicalPairDamping X h * (Real.log (X + h + 2 : ℕ)) ^ 3 =
      (Real.log (X + h + 2 : ℕ))⁻¹ := by
  have hL : Real.log (X + h + 2 : ℕ) ≠ 0 := ne_of_gt
    (Real.log_pos (by exact_mod_cast (show 1 < X + h + 2 by omega)))
  unfold physicalPairDamping
  field_simp

/-- The shrinking-damping diagonal resolves the von Mangoldt pair average. -/
theorem dampedPairDiagonal_error (X h : ℕ) :
    |dampedPairAverage (physicalPairDamping X h) X h - mangoldtPairAverage X h| ≤
      (Real.log (X + h + 2 : ℕ))⁻¹ := by
  simpa only [physicalPairDamping_error_scale] using
    dampedPairAverage_error (physicalPairDamping_pos X h) X h

/-- With squarefree projection, the diagonal resolves actual prime pairs. -/
theorem primePairDiagonal_error (X h : ℕ) :
    |projectedDampedPairAverage (physicalPairDamping X h) X h - primePairLogAverage X h| ≤
      (Real.log (X + h + 2 : ℕ))⁻¹ := by
  simpa only [physicalPairDamping_error_scale] using
    projectedDampedPairAverage_error (physicalPairDamping_pos X h) X h

private theorem physicalPairError_tendsto_zero (h : ℕ) :
    Tendsto (fun X : ℕ => (Real.log (X + h + 2 : ℕ))⁻¹) atTop (𝓝 0) := by
  have hX : Tendsto (fun X : ℕ => X + h + 2) atTop atTop := by
    simpa only [Nat.add_assoc] using tendsto_add_atTop_nat (h + 2)
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX))

/-- Simultaneous horizon growth and damping decay preserve the Mangoldt pair reading. -/
theorem dampedPairDiagonal_tendsto (h : ℕ) :
    Tendsto (fun X : ℕ => dampedPairAverage (physicalPairDamping X h) X h -
      mangoldtPairAverage X h) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun X => ?_)
    (physicalPairError_tendsto_zero h)
  simpa only [Real.norm_eq_abs] using dampedPairDiagonal_error X h

/-- The projected damping diagonal and the actual prime-pair average differ by `o(1)`. -/
theorem primePairDiagonal_tendsto (h : ℕ) :
    Tendsto (fun X : ℕ => projectedDampedPairAverage (physicalPairDamping X h) X h -
      primePairLogAverage X h) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun X => ?_)
    (physicalPairError_tendsto_zero h)
  simpa only [Real.norm_eq_abs] using primePairDiagonal_error X h

/-- Subtract the zero-damping coefficient before normalizing. -/
def compensatedDampingCoeff (ε : ℝ) (d : ℕ) : ℝ :=
  (moebius d : ℝ) * (1 - (d : ℝ) ^ (-ε)) / ε

private theorem abs_compensatedDampingCoeff_le_log {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    |compensatedDampingCoeff ε d| ≤ Real.log d := by
  by_cases hd : d = 0
  · subst d
    simp [compensatedDampingCoeff]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd1
  have ha : 0 ≤ 1 - (d : ℝ) ^ (-ε) := sub_nonneg.mpr
    (Real.rpow_le_one_of_one_le_of_nonpos hd1 (neg_nonpos.mpr hε.le))
  have hb : 1 - (d : ℝ) ^ (-ε) ≤ ε * Real.log d := by
    rw [Real.rpow_def_of_pos hd0]
    linarith [Real.add_one_le_exp (Real.log d * (-ε))]
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [compensatedDampingCoeff, abs_div, abs_mul, abs_of_pos hε, abs_of_nonneg ha,
    div_le_iff₀ hε]
  exact (mul_le_of_le_one_left ha hμ).trans (by simpa only [mul_comm] using hb)

/-- The coefficient bound is uniform over every value of the positive damping clock. -/
theorem abs_compensatedDampingCoeff_exp_le_log (t : ℝ) (d : ℕ) :
    |compensatedDampingCoeff (Real.exp (-t)) d| ≤ Real.log d :=
  abs_compensatedDampingCoeff_le_log (Real.exp_pos _) d

/-- The physical diagonal pays logarithms, with no inverse damping loss. -/
theorem abs_compensatedDampingCoeff_physical_le_log (X h d : ℕ) :
    |compensatedDampingCoeff (physicalPairDamping X h) d| ≤ Real.log d :=
  abs_compensatedDampingCoeff_le_log (physicalPairDamping_pos X h) d

private theorem sum_moebius_divisors_real (n : ℕ) :
    (∑ d ∈ n.divisors, (moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

private theorem normalizedDampedResponse_eq_compensated_of_ne_one (ε : ℝ) (n : ℕ)
    (hn : n ≠ 1) :
    normalizedDampedResponse ε n = -∑ d ∈ n.divisors, compensatedDampingCoeff ε d := by
  have hz : (∑ d ∈ n.divisors, (moebius d : ℝ)) = 0 := by
    rw [sum_moebius_divisors_real, if_neg hn]
  simp only [normalizedDampedResponse, pmPowerDampedDivisorCoeff, compensatedDampingCoeff,
    mul_sub, mul_one, sub_div, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hz, zero_div, zero_sub, neg_neg]

/-- Complete Möbius cancellation removes the zero-damping axis exactly. -/
theorem normalizedDampedResponse_eq_compensated (ε : ℝ) (n : ℕ) :
    normalizedDampedResponse ε (n + 2) =
      -∑ d ∈ (n + 2).divisors, compensatedDampingCoeff ε d :=
  normalizedDampedResponse_eq_compensated_of_ne_one ε (n + 2) (by omega)

/-- Exact finite pair expansion after both zero-damping axes are cancelled. -/
theorem dampedPairAverage_eq_compensated (ε : ℝ) (X h : ℕ) :
    dampedPairAverage ε X h =
      (∑ n ∈ Icc 2 X, ∑ d ∈ n.divisors, ∑ e ∈ (n + h).divisors,
        compensatedDampingCoeff ε d * compensatedDampingCoeff ε e) / X := by
  unfold dampedPairAverage
  congr 1
  apply sum_congr rfl
  intro n hn
  have hnI := mem_Icc.mp hn
  rw [normalizedDampedResponse_eq_compensated_of_ne_one ε n (by omega),
    normalizedDampedResponse_eq_compensated_of_ne_one ε (n + h) (by omega), neg_mul_neg]
  rw [Finset.sum_mul_sum]

/-- Complementary-divisor weight after the complete Möbius zero sum is removed. -/
def cofactorDampingWeight (ε : ℝ) (m : ℕ) : ℝ :=
  (1 - (m : ℝ) ^ (-ε)) / ε

/-- The compensated convolution keeps damping on the Möbius divisor. -/
def dampedCofactorTerm (ε : ℝ) (d m : ℕ) : ℝ :=
  (moebius d : ℝ) * (d : ℝ) ^ (-ε) * cofactorDampingWeight ε m

theorem cofactorDampingWeight_one (ε : ℝ) : cofactorDampingWeight ε 1 = 0 := by
  simp only [cofactorDampingWeight, Nat.cast_one, Real.one_rpow, sub_self, zero_div]

/-- The full-height unit-cofactor endpoint vanishes identically. -/
theorem dampedCofactorTerm_one (ε : ℝ) (d : ℕ) : dampedCofactorTerm ε d 1 = 0 := by
  rw [dampedCofactorTerm, cofactorDampingWeight_one, mul_zero]

private theorem cofactorDampingWeight_bounds {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    0 ≤ cofactorDampingWeight ε (m + 1) ∧
      cofactorDampingWeight ε (m + 1) ≤ Real.log (m + 1 : ℕ) := by
  have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hm0 : (0 : ℝ) < (m + 1 : ℕ) := lt_of_lt_of_le zero_lt_one hm1
  have ha : 0 ≤ 1 - ((m + 1 : ℕ) : ℝ) ^ (-ε) := sub_nonneg.mpr
    (Real.rpow_le_one_of_one_le_of_nonpos hm1 (neg_nonpos.mpr hε.le))
  refine ⟨div_nonneg ha hε.le, ?_⟩
  rw [cofactorDampingWeight, div_le_iff₀ hε, Real.rpow_def_of_pos hm0]
  linarith [Real.add_one_le_exp (Real.log (m + 1 : ℕ) * (-ε))]

private theorem abs_dampedCofactorTerm_le_log {ε : ℝ} (hε : 0 < ε) (d m : ℕ) :
    |dampedCofactorTerm ε d (m + 1)| ≤ Real.log (m + 1 : ℕ) := by
  by_cases hd : d = 0
  · subst d
    simp only [dampedCofactorTerm, ArithmeticFunction.map_zero, Int.cast_zero,
      zero_mul, abs_zero]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hpow0 : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hpow1 : (d : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hd1 (neg_nonpos.mpr hε.le)
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hw := cofactorDampingWeight_bounds hε m
  rw [dampedCofactorTerm, abs_mul, abs_mul, abs_of_nonneg hpow0, abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_left hw.1
    ((mul_le_of_le_one_left hpow0 hμ).trans hpow1)).trans hw.2

/-- Logarithmic cost belongs to the cofactor, uniformly over the positive clock. -/
theorem abs_dampedCofactorTerm_exp_le_log (t : ℝ) (d m : ℕ) :
    |dampedCofactorTerm (Real.exp (-t)) d (m + 1)| ≤ Real.log (m + 1 : ℕ) :=
  abs_dampedCofactorTerm_le_log (Real.exp_pos _) d m

theorem abs_dampedCofactorTerm_physical_le_log (X h d m : ℕ) :
    |dampedCofactorTerm (physicalPairDamping X h) d (m + 1)| ≤ Real.log (m + 1 : ℕ) :=
  abs_dampedCofactorTerm_le_log (physicalPairDamping_pos X h) d m

private theorem normalizedDampedResponse_eq_cofactors_of_ne_one (ε : ℝ) (n : ℕ)
    (hn : n ≠ 1) :
    normalizedDampedResponse ε n =
      ∑ p ∈ n.divisorsAntidiagonal, dampedCofactorTerm ε p.1 p.2 := by
  have hz : (∑ d ∈ n.divisors, (moebius d : ℝ)) = 0 := by
    rw [sum_moebius_divisors_real, if_neg hn]
  have hterm (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) :
      dampedCofactorTerm ε p.1 p.2 =
        (moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-ε) / ε -
          (n : ℝ) ^ (-ε) / ε * (moebius p.1 : ℝ) := by
    have hprod : (p.1 : ℝ) ^ (-ε) * (p.2 : ℝ) ^ (-ε) = (n : ℝ) ^ (-ε) := by
      rw [← Real.mul_rpow (Nat.cast_nonneg p.1) (Nat.cast_nonneg p.2),
        ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
    unfold dampedCofactorTerm cofactorDampingWeight
    calc
      _ = (moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-ε) / ε -
          ((p.1 : ℝ) ^ (-ε) * (p.2 : ℝ) ^ (-ε)) / ε * (moebius p.1 : ℝ) := by ring
      _ = _ := by rw [hprod]
  symm
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        ((moebius p.1 : ℝ) * (p.1 : ℝ) ^ (-ε) / ε -
          (n : ℝ) ^ (-ε) / ε * (moebius p.1 : ℝ)) := sum_congr rfl hterm
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal (fun d _ =>
        (moebius d : ℝ) * (d : ℝ) ^ (-ε) / ε - (n : ℝ) ^ (-ε) / ε * (moebius d : ℝ)),
        sum_sub_distrib, ← sum_div, ← mul_sum, hz, mul_zero, sub_zero]
      rfl

/-- Exact convolution after the zero Möbius sum is transferred to the cofactor. -/
theorem normalizedDampedResponse_eq_cofactor_compensation (ε : ℝ) (n : ℕ) :
    normalizedDampedResponse ε (n + 2) =
      ∑ p ∈ (n + 2).divisorsAntidiagonal, dampedCofactorTerm ε p.1 p.2 :=
  normalizedDampedResponse_eq_cofactors_of_ne_one ε (n + 2) (by omega)

private theorem normalizedDampedResponse_eq_nonunit_of_ne_one (ε : ℝ) (n : ℕ)
    (hn : n ≠ 1) :
    normalizedDampedResponse ε n =
      ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.2 ≠ 1),
        dampedCofactorTerm ε p.1 p.2 := by
  rw [normalizedDampedResponse_eq_cofactors_of_ne_one ε n hn, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.2 = 1
  · simp only [hp, ne_eq, not_true_eq_false, if_false, dampedCofactorTerm_one]
  · rw [if_pos hp]

/-- The complete response is carried by nonunit complementary divisors. -/
theorem normalizedDampedResponse_eq_nonunit_cofactors (ε : ℝ) (n : ℕ) :
    normalizedDampedResponse ε (n + 2) =
      ∑ p ∈ (n + 2).divisorsAntidiagonal.filter (fun p => p.2 ≠ 1),
        dampedCofactorTerm ε p.1 p.2 :=
  normalizedDampedResponse_eq_nonunit_of_ne_one ε (n + 2) (by omega)

/-- Both unit-cofactor faces vanish before any estimate of the physical pair sum. -/
theorem dampedPairAverage_eq_nonunit_cofactors (ε : ℝ) (X h : ℕ) :
    dampedPairAverage ε X h =
      (∑ n ∈ Icc 2 X,
        ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => p.2 ≠ 1),
        ∑ q ∈ (n + h).divisorsAntidiagonal.filter (fun q => q.2 ≠ 1),
          dampedCofactorTerm ε p.1 p.2 * dampedCofactorTerm ε q.1 q.2) / X := by
  unfold dampedPairAverage
  congr 1
  apply sum_congr rfl
  intro n hn
  have hnI := mem_Icc.mp hn
  rw [normalizedDampedResponse_eq_nonunit_of_ne_one ε n (by omega),
    normalizedDampedResponse_eq_nonunit_of_ne_one ε (n + h) (by omega), sum_mul_sum]

private theorem cofactorDampingWeight_lower {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ (-ε) * Real.log m ≤ cofactorDampingWeight ε m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let u := ε * Real.log m
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_nonneg (-u))
  have hc : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hc] at he
  rw [cofactorDampingWeight, le_div_iff₀ hε, Real.rpow_def_of_pos hm0]
  have hu : Real.log m * (-ε) = -u := by dsimp [u]; ring
  rw [hu]
  calc
    Real.exp (-u) * Real.log m * ε = u * Real.exp (-u) := by dsimp [u]; ring
    _ ≤ 1 - Real.exp (-u) := by nlinarith only [he]

private theorem abs_dampedCofactorTerm_sub_log_le {ε : ℝ} (hε : 0 < ε)
    {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    |dampedCofactorTerm ε d m - (moebius d : ℝ) * Real.log m| ≤
      ε * Real.log (d * m : ℕ) * Real.log m := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmL : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hd0 : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hdle : (d : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hd1 (neg_nonpos.mpr hε.le)
  have hw : 0 ≤ cofactorDampingWeight ε m ∧ cofactorDampingWeight ε m ≤ Real.log m := by
    simpa only [Nat.sub_add_cancel hm] using cofactorDampingWeight_bounds hε (m - 1)
  have hupper : (d : ℝ) ^ (-ε) * cofactorDampingWeight ε m ≤ Real.log m :=
    (mul_le_of_le_one_left hw.1 hdle).trans hw.2
  have hlower : ((d * m : ℕ) : ℝ) ^ (-ε) * Real.log m ≤
      (d : ℝ) ^ (-ε) * cofactorDampingWeight ε m := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m), mul_assoc]
    exact mul_le_mul_of_nonneg_left (cofactorDampingWeight_lower hε hm) hd0
  have hprod : (0 : ℝ) < (d * m : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < d) (by omega : 0 < m)
  have hdef : 1 - ((d * m : ℕ) : ℝ) ^ (-ε) ≤ ε * Real.log (d * m : ℕ) := by
    rw [Real.rpow_def_of_pos hprod]
    linarith [Real.add_one_le_exp (Real.log (d * m : ℕ) * (-ε))]
  have hμ : |(moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [dampedCofactorTerm, mul_assoc, ← mul_sub, abs_mul,
    abs_of_nonpos (sub_nonpos.mpr hupper), neg_sub]
  calc
    _ ≤ Real.log m - (d : ℝ) ^ (-ε) * cofactorDampingWeight ε m :=
      mul_le_of_le_one_left (sub_nonneg.mpr hupper) hμ
    _ ≤ (1 - ((d * m : ℕ) : ℝ) ^ (-ε)) * Real.log m := by nlinarith only [hlower]
    _ ≤ _ := mul_le_mul_of_nonneg_right hdef hmL

/-- A cofactor term approaches its logarithmic extension with an explicit physical error. -/
theorem dampedCofactorTerm_exp_error (t : ℝ) (d m : ℕ) :
    |dampedCofactorTerm (Real.exp (-t)) (d + 1) (m + 1) -
      (moebius (d + 1) : ℝ) * Real.log (m + 1 : ℕ)| ≤
      Real.exp (-t) * Real.log ((d + 1) * (m + 1) : ℕ) * Real.log (m + 1 : ℕ) :=
  abs_dampedCofactorTerm_sub_log_le (Real.exp_pos _) (by omega) (by omega)

/-- The physical response restricted by its complementary divisor. -/
def truncatedCofactorResponse (ε : ℝ) (Z n : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 Z, if m ∣ n then dampedCofactorTerm ε (n / m) m else 0

/-- The logarithmic extension of the truncated response at zero damping. -/
def truncatedLogCofactorResponse (Z n : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 Z, if m ∣ n then (moebius (n / m) : ℝ) * Real.log m else 0

/-- The positive divisor envelope retains the physical cofactor cutoff. -/
def truncatedDivisorLogMass (Z n : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 Z, if m ∣ n then Real.log m else 0

private theorem truncatedDivisorLogMass_nonneg (Z n : ℕ) :
    0 ≤ truncatedDivisorLogMass Z n := by
  apply sum_nonneg
  intro m hm
  split_ifs
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from (by have := mem_Icc.mp hm; omega)))
  · exact le_refl 0

private theorem abs_truncatedCofactorResponse_le {ε : ℝ} (hε : 0 < ε) (Z n : ℕ) :
    |truncatedCofactorResponse ε Z n| ≤ truncatedDivisorLogMass Z n := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro m hm
  have hm1 : 1 ≤ m := by have := mem_Icc.mp hm; omega
  by_cases hmn : m ∣ n
  · simp only [if_pos hmn]
    simpa only [Nat.sub_add_cancel hm1] using abs_dampedCofactorTerm_le_log hε (n / m) (m - 1)
  · simp only [if_neg hmn, abs_zero, le_refl]

private theorem abs_truncatedLogCofactorResponse_le (Z n : ℕ) :
    |truncatedLogCofactorResponse Z n| ≤ truncatedDivisorLogMass Z n := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro m hm
  have hmL : 0 ≤ Real.log m := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ m from (by have := mem_Icc.mp hm; omega)))
  by_cases hmn : m ∣ n
  · simp only [if_pos hmn, abs_mul, abs_of_nonneg hmL]
    apply mul_le_of_le_one_left hmL
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n / m)
  · simp only [if_neg hmn, abs_zero, le_refl]

private theorem truncatedCofactorResponse_error {ε : ℝ} (hε : 0 < ε)
    (Z : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    |truncatedCofactorResponse ε Z n - truncatedLogCofactorResponse Z n| ≤
      ε * Real.log n * truncatedDivisorLogMass Z n := by
  unfold truncatedCofactorResponse truncatedLogCofactorResponse truncatedDivisorLogMass
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro m hm
  have hm1 : 1 ≤ m := by have := mem_Icc.mp hm; omega
  by_cases hmn : m ∣ n
  · simp only [if_pos hmn]
    have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmn
    have hquot : 1 ≤ n / m := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hmle)
    simpa only [Nat.div_mul_cancel hmn] using abs_dampedCofactorTerm_sub_log_le hε hquot hm1
  · simp only [if_neg hmn, sub_self, abs_zero, mul_zero, le_refl]

/-- A positive logarithmic scale for physical cofactor rectangles. -/
def cofactorLogScale (X : ℕ) : ℝ := 1 + Real.log (X + 2 : ℕ)

private theorem one_le_cofactorLogScale (X : ℕ) : 1 ≤ cofactorLogScale X := by
  have h : 0 ≤ Real.log (X + 2 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 2 by omega))
  change 1 ≤ 1 + Real.log (X + 2 : ℕ)
  linarith

private theorem log_le_cofactorLogScale {X m : ℕ} (hm : 1 ≤ m) (hmX : m ≤ X + 2) :
    Real.log m ≤ cofactorLogScale X := by
  have hlog : Real.log m ≤ Real.log (X + 2 : ℕ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmX)
  change Real.log m ≤ 1 + Real.log (X + 2 : ℕ)
  linarith

private theorem gapTwoCofactorCount_le {X a b : ℕ} (hX : 1 ≤ X)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (((Icc 2 X).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ) ≤
      2 * (X : ℝ) / ((a : ℝ) * b) + 1 := by
  let B := max a b
  let P := B.factorial
  let d : Fin 2 → ℕ := fun i => if i = 0 then a else b
  let h : Fin 2 → ℕ := fun i => if i = 0 then 0 else 2
  have hd : ∀ i, d i ∈ Icc 1 B := by
    intro i
    fin_cases i
    · simpa [d, B] using And.intro ha (le_max_left a b)
    · simpa [d, B] using And.intro hb (le_max_right a b)
  have hpred (n : ℕ) : (∀ i, d i ∣ n + h i) ↔ a ∣ n ∧ b ∣ n + 2 := by
    constructor
    · intro hn
      exact ⟨by simpa [d, h] using hn 0, by simpa [d, h] using hn 1⟩
    · rintro ⟨hna, hnb⟩ i
      fin_cases i
      · simpa [d, h] using hna
      · simpa [d, h] using hnb
  have hw := GaloisForLFunctions.BezoutValuationIncidence.abs_card_joint_incidence_window_sub_le
    d h hd 1 (X - 1)
  simp only [hpred, show 1 + 1 = 2 from rfl, show 1 + (X - 1) = X by omega] at hw
  have hset : Icc 1 P = Ioc 0 P := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  change |(((Icc 2 X).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ) -
    ((X - 1 : ℕ) : ℝ) / P * (((Icc 1 P).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ)| ≤ 1 at hw
  rw [hset] at hw
  have hP : Nat.lcm a b ∣ P := Nat.lcm_dvd
    (Nat.dvd_factorial ha (le_max_left a b)) (Nat.dvd_factorial hb (le_max_right a b))
  have hden := GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve.joint_density_complete_period
    (h := 2) (by omega : 0 < a) (by omega : 0 < b) hP (Nat.factorial_pos B)
  have hrate : (((Ioc 0 P).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ) / P ≤
      2 / ((a : ℝ) * b) := by
    rw [hden]
    split_ifs with hg
    · have hg2 : (Nat.gcd a b : ℝ) ≤ 2 := by
        exact_mod_cast Nat.le_of_dvd (by omega : 0 < 2) hg
      exact div_le_div_of_nonneg_right hg2 (by positivity)
    · positivity
  have hmain : ((X - 1 : ℕ) : ℝ) / P *
      (((Ioc 0 P).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ) ≤
        2 * (X : ℝ) / ((a : ℝ) * b) := by
    calc
      _ = ((X - 1 : ℕ) : ℝ) *
          ((((Ioc 0 P).filter fun n => a ∣ n ∧ b ∣ n + 2).card : ℝ) / P) := by ring
      _ ≤ (X : ℝ) * (2 / ((a : ℝ) * b)) :=
        mul_le_mul (by exact_mod_cast Nat.sub_le X 1) hrate (by positivity) (by positivity)
      _ = _ := by ring
  linarith only [(abs_le.mp hw).2, hmain]

private theorem sum_divisorLogMass_pair (X Z W : ℕ) :
    (∑ n ∈ Icc 2 X, truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) =
      ∑ m ∈ Icc 2 Z, ∑ k ∈ Icc 2 W,
        Real.log m * Real.log k *
          (((Icc 2 X).filter fun n => m ∣ n ∧ k ∣ n + 2).card : ℝ) := by
  have ht (n : ℕ) : truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2) =
      ∑ m ∈ Icc 2 Z, ∑ k ∈ Icc 2 W,
        if m ∣ n ∧ k ∣ n + 2 then Real.log m * Real.log k else 0 := by
    rw [truncatedDivisorLogMass, truncatedDivisorLogMass, sum_mul_sum]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro k _
    by_cases hm : m ∣ n <;> by_cases hk : k ∣ n + 2 <;> simp only
      [hm, hk, and_true, and_false, if_true, if_false, zero_mul, mul_zero]
  rw [sum_congr rfl (fun n _ => ht n), sum_comm]
  apply sum_congr rfl
  intro m _
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

private theorem sum_divisorLogMass_pair_le {X : ℕ} (hX : 1 ≤ X) (Z W : ℕ) :
    (∑ n ∈ Icc 2 X, truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) ≤
      2 * (X : ℝ) * ((∑ m ∈ Icc 2 Z, Real.log m / m) *
        (∑ k ∈ Icc 2 W, Real.log k / k)) +
      (∑ m ∈ Icc 2 Z, Real.log m) * (∑ k ∈ Icc 2 W, Real.log k) := by
  rw [sum_divisorLogMass_pair]
  calc
    _ ≤ ∑ m ∈ Icc 2 Z, ∑ k ∈ Icc 2 W,
        (2 * (X : ℝ) * ((Real.log m / m) * (Real.log k / k)) + Real.log m * Real.log k) := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum
      intro k hk
      have hm1 : 1 ≤ m := by have := mem_Icc.mp hm; omega
      have hk1 : 1 ≤ k := by have := mem_Icc.mp hk; omega
      have hlog : 0 ≤ Real.log m * Real.log k := mul_nonneg
        (Real.log_nonneg (by exact_mod_cast hm1)) (Real.log_nonneg (by exact_mod_cast hk1))
      calc
        _ ≤ Real.log m * Real.log k * (2 * (X : ℝ) / ((m : ℝ) * k) + 1) :=
          mul_le_mul_of_nonneg_left (gapTwoCofactorCount_le hX hm1 hk1) hlog
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by
      rw [sum_mul_sum, sum_mul_sum]
      simp only [sum_add_distrib, mul_sum, mul_assoc]

private theorem sum_log_div_le_scale_sq {X Z : ℕ} (hZ : 2 ≤ Z) (hZX : Z ≤ X) :
    (∑ m ∈ Icc 2 Z, Real.log m / m) ≤ cofactorLogScale X ^ 2 := by
  have hH : 0 ≤ cofactorLogScale X := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cofactorLogScale X)
  have hsub : Icc 2 Z ⊆ Icc 1 Z := by
    intro m hm
    have := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hsum : (∑ m ∈ Icc 2 Z, 1 / (m : ℝ)) ≤ 1 + Real.log Z :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (RHTower.Sieve.sum_Icc_one_div_le_one_add_log Z)
  have hlog : 1 + Real.log Z ≤ cofactorLogScale X := by
    change 1 + Real.log Z ≤ 1 + Real.log (X + 2 : ℕ)
    exact add_le_add (le_refl 1) (Real.log_le_log (by exact_mod_cast (show 0 < Z by omega))
      (by exact_mod_cast (show Z ≤ X + 2 by omega)))
  calc
    _ ≤ ∑ m ∈ Icc 2 Z, cofactorLogScale X * (1 / (m : ℝ)) := by
      apply sum_le_sum
      intro m hm
      have hmI := mem_Icc.mp hm
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right
        (log_le_cofactorLogScale (by omega : 1 ≤ m) (by omega : m ≤ X + 2))
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = cofactorLogScale X * (∑ m ∈ Icc 2 Z, 1 / (m : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ cofactorLogScale X * cofactorLogScale X :=
      mul_le_mul_of_nonneg_left (hsum.trans hlog) hH
    _ = _ := (pow_two _).symm

private theorem sum_log_le_scale_mul {X Z : ℕ} (hZX : Z ≤ X) :
    (∑ m ∈ Icc 2 Z, Real.log m) ≤ cofactorLogScale X * Z := by
  have hH : 0 ≤ cofactorLogScale X := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cofactorLogScale X)
  calc
    _ ≤ ∑ _m ∈ Icc 2 Z, cofactorLogScale X := by
      apply sum_le_sum
      intro m hm
      have hmI := mem_Icc.mp hm
      exact log_le_cofactorLogScale (by omega) (by omega)
    _ = ((Icc 2 Z).card : ℝ) * cofactorLogScale X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Z : ℝ) * cofactorLogScale X := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show (Icc 2 Z).card ≤ Z by rw [Nat.card_Icc]; omega)) hH
    _ = _ := mul_comm _ _

private theorem cofactorLogMass_rectangle_bound_aux {X Z W : ℕ}
    (hZ : 2 ≤ Z) (hW : 2 ≤ W) (hZW : Z * W ≤ X) :
    (∑ n ∈ Icc 2 X, truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) ≤
      3 * (X : ℝ) * cofactorLogScale X ^ 4 := by
  have hZX : Z ≤ X := (Nat.le_mul_of_pos_right Z (by omega : 0 < W)).trans hZW
  have hWX : W ≤ X := (Nat.le_mul_of_pos_left W (by omega : 0 < Z)).trans hZW
  have hX : 1 ≤ X := by omega
  have hH : 0 ≤ cofactorLogScale X := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cofactorLogScale X)
  have hlog0 (R : ℕ) : 0 ≤ ∑ m ∈ Icc 2 R, Real.log m := by
    apply sum_nonneg
    intro m hm
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from (by have := mem_Icc.mp hm; omega)))
  have hdiv0 (R : ℕ) : 0 ≤ ∑ m ∈ Icc 2 R, Real.log m / m := by
    apply sum_nonneg
    intro m hm
    exact div_nonneg (Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ m from (by have := mem_Icc.mp hm; omega)))) (Nat.cast_nonneg m)
  have hprod1 := mul_le_mul (sum_log_div_le_scale_sq hZ hZX) (sum_log_div_le_scale_sq hW hWX)
    (hdiv0 W) (sq_nonneg (cofactorLogScale X))
  have hprod2 := mul_le_mul (sum_log_le_scale_mul hZX) (sum_log_le_scale_mul hWX)
    (hlog0 W) (mul_nonneg hH (Nat.cast_nonneg Z))
  have hZWreal : (Z : ℝ) * W ≤ X := by exact_mod_cast hZW
  have hH2 : cofactorLogScale X ^ 2 ≤ cofactorLogScale X ^ 4 := by
    have h1 := one_le_cofactorLogScale X
    have hsq : 1 ≤ cofactorLogScale X ^ 2 := by
      nlinarith only [sq_nonneg (cofactorLogScale X - 1), h1]
    calc
      _ = cofactorLogScale X ^ 2 * 1 := by ring
      _ ≤ cofactorLogScale X ^ 2 * cofactorLogScale X ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ 2 * (X : ℝ) * ((∑ m ∈ Icc 2 Z, Real.log m / m) *
        (∑ k ∈ Icc 2 W, Real.log k / k)) +
        (∑ m ∈ Icc 2 Z, Real.log m) * (∑ k ∈ Icc 2 W, Real.log k) :=
      sum_divisorLogMass_pair_le hX Z W
    _ ≤ 2 * (X : ℝ) * (cofactorLogScale X ^ 2 * cofactorLogScale X ^ 2) +
        (cofactorLogScale X * Z) * (cofactorLogScale X * W) :=
      add_le_add (mul_le_mul_of_nonneg_left hprod1 (by positivity)) hprod2
    _ = 2 * (X : ℝ) * cofactorLogScale X ^ 4 + ((Z : ℝ) * W) * cofactorLogScale X ^ 2 := by ring
    _ ≤ 2 * (X : ℝ) * cofactorLogScale X ^ 4 + (X : ℝ) * cofactorLogScale X ^ 4 := by
      exact add_le_add (le_refl _) (mul_le_mul hZWreal hH2 (sq_nonneg _) (Nat.cast_nonneg X))
    _ = _ := by ring

/-- A fourth power of the logarithmic scale bounds the physical cofactor envelope. -/
theorem cofactorLogMass_rectangle_bound (Z W N : ℕ) :
    (∑ n ∈ Icc 2 ((Z + 2) * (W + 2) + N),
      truncatedDivisorLogMass (Z + 2) n * truncatedDivisorLogMass (W + 2) (n + 2)) ≤
      3 * (((Z + 2) * (W + 2) + N : ℕ) : ℝ) *
        cofactorLogScale ((Z + 2) * (W + 2) + N) ^ 4 :=
  cofactorLogMass_rectangle_bound_aux (by omega) (by omega) (by omega)

/-- The difference of physical pair readings on any selected part of the interval. -/
def cofactorPairDifference (ε : ℝ) (X Z W : ℕ) (S : Finset ℕ) : ℝ :=
  (∑ n ∈ (Icc 2 X) ∩ S,
    (truncatedCofactorResponse ε Z n * truncatedCofactorResponse ε W (n + 2) -
      truncatedLogCofactorResponse Z n * truncatedLogCofactorResponse W (n + 2))) / X

private theorem cofactor_pair_error {ε : ℝ} (hε : 0 < ε) (Z W : ℕ)
    {X n : ℕ} (hn : n ∈ Icc 2 X) :
    |truncatedCofactorResponse ε Z n * truncatedCofactorResponse ε W (n + 2) -
      truncatedLogCofactorResponse Z n * truncatedLogCofactorResponse W (n + 2)| ≤
      2 * ε * cofactorLogScale X *
        (truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) := by
  have hnI := mem_Icc.mp hn
  have hH : 0 ≤ cofactorLogScale X := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cofactorLogScale X)
  have hZ0 := truncatedDivisorLogMass_nonneg Z n
  have hW0 := truncatedDivisorLogMass_nonneg W (n + 2)
  have hen : |truncatedCofactorResponse ε Z n - truncatedLogCofactorResponse Z n| ≤
      ε * cofactorLogScale X * truncatedDivisorLogMass Z n :=
    (truncatedCofactorResponse_error hε Z hnI.1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (log_le_cofactorLogScale (by omega) (by omega)) hε.le) hZ0)
  have hem : |truncatedCofactorResponse ε W (n + 2) - truncatedLogCofactorResponse W (n + 2)| ≤
      ε * cofactorLogScale X * truncatedDivisorLogMass W (n + 2) :=
    (truncatedCofactorResponse_error hε W (by omega)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (log_le_cofactorLogScale (by omega) (by omega)) hε.le) hW0)
  calc
    _ = |(truncatedCofactorResponse ε Z n - truncatedLogCofactorResponse Z n) *
        truncatedCofactorResponse ε W (n + 2) + truncatedLogCofactorResponse Z n *
          (truncatedCofactorResponse ε W (n + 2) - truncatedLogCofactorResponse W (n + 2))| := by
      congr 1
      ring
    _ ≤ |(truncatedCofactorResponse ε Z n - truncatedLogCofactorResponse Z n) *
        truncatedCofactorResponse ε W (n + 2)| + |truncatedLogCofactorResponse Z n *
          (truncatedCofactorResponse ε W (n + 2) - truncatedLogCofactorResponse W (n + 2))| :=
      abs_add_le _ _
    _ ≤ (ε * cofactorLogScale X * truncatedDivisorLogMass Z n) * truncatedDivisorLogMass W (n + 2) +
        truncatedDivisorLogMass Z n * (ε * cofactorLogScale X * truncatedDivisorLogMass W (n + 2)) := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hen (abs_truncatedCofactorResponse_le hε W (n + 2)) (abs_nonneg _)
          (mul_nonneg (mul_nonneg hε.le hH) hZ0))
        (mul_le_mul (abs_truncatedLogCofactorResponse_le Z n) hem (abs_nonneg _) hZ0)
    _ = _ := by ring

private theorem cofactorPairDifference_bound {ε : ℝ} (hε : 0 < ε)
    {X Z W : ℕ} (hZ : 2 ≤ Z) (hW : 2 ≤ W) (hZW : Z * W ≤ X) (S : Finset ℕ) :
    |cofactorPairDifference ε X Z W S| ≤ 6 * ε * cofactorLogScale X ^ 5 := by
  have hX : 0 < X := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hZW
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hH : 0 ≤ cofactorLogScale X := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_cofactorLogScale X)
  have hC : 0 ≤ 2 * ε * cofactorLogScale X := by positivity
  rw [cofactorPairDifference, abs_div, abs_of_pos hXR, div_le_iff₀ hXR]
  calc
    _ ≤ ∑ n ∈ (Icc 2 X) ∩ S,
        |truncatedCofactorResponse ε Z n * truncatedCofactorResponse ε W (n + 2) -
          truncatedLogCofactorResponse Z n * truncatedLogCofactorResponse W (n + 2)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (Icc 2 X) ∩ S, 2 * ε * cofactorLogScale X *
        (truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) :=
      sum_le_sum fun n hn => cofactor_pair_error hε Z W (mem_inter.mp hn).1
    _ ≤ ∑ n ∈ Icc 2 X, 2 * ε * cofactorLogScale X *
        (truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left (fun n _ _ => mul_nonneg hC
        (mul_nonneg (truncatedDivisorLogMass_nonneg Z n) (truncatedDivisorLogMass_nonneg W (n + 2))))
    _ = (2 * ε * cofactorLogScale X) *
        (∑ n ∈ Icc 2 X, truncatedDivisorLogMass Z n * truncatedDivisorLogMass W (n + 2)) :=
      (mul_sum _ _ _).symm
    _ ≤ (2 * ε * cofactorLogScale X) * (3 * (X : ℝ) * cofactorLogScale X ^ 4) :=
      mul_le_mul_of_nonneg_left (cofactorLogMass_rectangle_bound_aux hZ hW hZW) hC
    _ = _ := by ring

/-- Damping small enough to resolve both the full source and its cofactor rectangles. -/
def cofactorPairDamping (X : ℕ) : ℝ := (cofactorLogScale X)⁻¹ ^ 6

theorem cofactorPairDamping_pos (X : ℕ) : 0 < cofactorPairDamping X :=
  pow_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_cofactorLogScale X))) 6

/-- Uniform damping removal, including every selected subset of a physical cofactor rectangle. -/
theorem cofactorDampingRemoval_error (Z W N : ℕ) (S : Finset ℕ) :
    let X := (Z + 2) * (W + 2) + N
    |cofactorPairDifference (cofactorPairDamping X) X (Z + 2) (W + 2) S| ≤
      6 / cofactorLogScale X := by
  dsimp only
  let X := (Z + 2) * (W + 2) + N
  have h := cofactorPairDifference_bound (cofactorPairDamping_pos X)
    (by omega : 2 ≤ Z + 2) (by omega : 2 ≤ W + 2) (show (Z + 2) * (W + 2) ≤ X by dsimp [X]; omega) S
  have hne : cofactorLogScale X ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (one_le_cofactorLogScale X))
  have heq : 6 * cofactorPairDamping X * cofactorLogScale X ^ 5 = 6 / cofactorLogScale X := by
    unfold cofactorPairDamping
    field_simp
  exact h.trans_eq heq

private theorem log_padded_le_twice_cofactorLogScale (X : ℕ) :
    Real.log (X + 4 : ℕ) ≤ 2 * cofactorLogScale X := by
  have hn : X + 4 ≤ (X + 2) ^ 2 := by nlinarith
  calc
    _ ≤ Real.log (((X + 2 : ℕ) : ℝ) ^ 2) := Real.log_le_log
      (by exact_mod_cast (show 0 < X + 4 by omega)) (by exact_mod_cast hn)
    _ = 2 * Real.log (X + 2 : ℕ) := by rw [Real.log_pow]; norm_num
    _ ≤ _ := by unfold cofactorLogScale; linarith

/-- The same faster clock still resolves the actual squarefree-projected prime pairs. -/
theorem primePairCofactorClock_error (X : ℕ) :
    |projectedDampedPairAverage (cofactorPairDamping X) X 2 - primePairLogAverage X 2| ≤
      8 * ((cofactorLogScale X)⁻¹) ^ 3 := by
  have h := projectedDampedPairAverage_error (cofactorPairDamping_pos X) X 2
  have hlog0 : 0 ≤ Real.log (X + 4 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 4 by omega))
  have hp := pow_le_pow_left₀ hlog0 (log_padded_le_twice_cofactorLogScale X) 3
  have hne : cofactorLogScale X ≠ 0 := ne_of_gt
    (lt_of_lt_of_le zero_lt_one (one_le_cofactorLogScale X))
  rw [show X + 2 + 2 = X + 4 by omega] at h
  calc
    _ ≤ cofactorPairDamping X * Real.log (X + 4 : ℕ) ^ 3 := h
    _ ≤ cofactorPairDamping X * (2 * cofactorLogScale X) ^ 3 :=
      mul_le_mul_of_nonneg_left hp (cofactorPairDamping_pos X).le
    _ = _ := by unfold cofactorPairDamping; field_simp; norm_num

private theorem cofactorLogScale_inv_tendsto :
    Tendsto (fun X : ℕ => (cofactorLogScale X)⁻¹) atTop (𝓝 0) := by
  have hbase : Tendsto (fun X : ℕ => (Real.log (X + 2 : ℕ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.add_zero] using physicalPairError_tendsto_zero 0
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun X => ?_) hbase
  have hH0 : 0 ≤ cofactorLogScale X := zero_le_one.trans (one_le_cofactorLogScale X)
  have hlog : 0 < Real.log (X + 2 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X + 2 by omega))
  have hLH : Real.log (X + 2 : ℕ) ≤ cofactorLogScale X := by unfold cofactorLogScale; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hH0)]
  simpa only [one_div] using one_div_le_one_div_of_le hlog hLH

/-- Cofactor-compatible damping preserves the actual prime-pair average in the horizon limit. -/
theorem primePairCofactorClock_tendsto :
    Tendsto (fun X : ℕ => projectedDampedPairAverage (cofactorPairDamping X) X 2 -
      primePairLogAverage X 2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun X : ℕ => 8 * ((cofactorLogScale X)⁻¹) ^ 3) atTop (𝓝 0) := by
    simpa using (cofactorLogScale_inv_tendsto.pow 3).const_mul 8
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun X => ?_) hlim
  simpa only [Real.norm_eq_abs] using primePairCofactorClock_error X

end

end TwinPrime
