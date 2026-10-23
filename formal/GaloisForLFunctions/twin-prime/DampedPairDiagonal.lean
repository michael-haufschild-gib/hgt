import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareRightLine
import GaloisForLFunctions.RHTower.SpurRescale
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The physical damping diagonal of prime pairs

The normalized divisor response approximates von Mangoldt uniformly on a
finite interval. The resulting pair error keeps an explicit damping factor,
so damping can decrease with the physical horizon.
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
    simp only [dampedCofactorTerm, map_zero, Int.cast_zero, zero_mul, abs_zero]
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

end

end TwinPrime

#print axioms TwinPrime.abs_compensatedDampingCoeff_exp_le_log
#print axioms TwinPrime.abs_compensatedDampingCoeff_physical_le_log
#print axioms TwinPrime.normalizedDampedResponse_eq_compensated
#print axioms TwinPrime.dampedPairAverage_eq_compensated
#print axioms TwinPrime.dampedCofactorTerm_one
#print axioms TwinPrime.abs_dampedCofactorTerm_exp_le_log
#print axioms TwinPrime.abs_dampedCofactorTerm_physical_le_log
#print axioms TwinPrime.normalizedDampedResponse_eq_cofactor_compensation
#print axioms TwinPrime.normalizedDampedResponse_eq_nonunit_cofactors
#print axioms TwinPrime.dampedPairAverage_eq_nonunit_cofactors
