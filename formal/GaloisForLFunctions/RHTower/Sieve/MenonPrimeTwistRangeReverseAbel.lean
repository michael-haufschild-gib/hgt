import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeReverseAbel
import GaloisForLFunctions.RHTower.Sieve.PrimePowerDefectBound
import GaloisForLFunctions.RHTower.BourgainPartialSummation

/-!
# Menon reverse Abel selection on a literal prime interval

This file keeps Menon's exceptional prime block on its physical interval.  It reverses Abel
summation using range prefixes, then removes proper prime powers on that same range.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Proper-prime-power mass on the literal interval `(a,b]`. -/
def primePowerDefectIoc (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc a b,
    ((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0)

theorem primePowerDefectIoc_nonneg (a b : ℕ) :
    0 ≤ primePowerDefectIoc a b := by
  unfold primePowerDefectIoc
  refine Finset.sum_nonneg fun n _ => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
  · rw [if_neg hp, sub_zero]
    exact vonMangoldt_nonneg

theorem primePowerDefectIoc_mono_right {a b c : ℕ} (hbc : b ≤ c) :
    primePowerDefectIoc a b ≤ primePowerDefectIoc a c := by
  unfold primePowerDefectIoc
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hbc⟩
  · intro n _hn _hnab
    by_cases hp : n.Prime
    · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]
      exact vonMangoldt_nonneg

/-- Removing proper prime powers on a literal interval costs exactly their untwisted mass there. -/
theorem norm_sum_Ioc_vonMangoldtTwist_sub_prime_le
    (tau : ℝ) (a b : ℕ) :
    ‖(∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n) -
        ∑ n ∈ Finset.Ioc a b, vonMangoldtPrimeTwist tau n‖ ≤
      primePowerDefectIoc a b := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun n hnmem => ?_
  rw [vonMangoldtTwist_sub_prime, norm_mul]
  have hn : 0 < n := by
    have := (Finset.mem_Ioc.mp hnmem).1
    omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
  have hphase : ‖((n : ℕ) : ℂ) ^ (-((tau : ℂ) * Complex.I))‖ = 1 := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
    simp
  have hcoeff : 0 ≤ (vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0 := by
    by_cases hp : n.Prime
    · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]
      exact vonMangoldt_nonneg
  rw [hphase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff]

/-- A uniform bound for all log-weighted prime prefixes on `(a,b]` bounds the ordinary prime
interval with the exact reciprocal-log cost at `a+1`. -/
theorem norm_primeBlockPoly_le_of_vonMangoldtPrimeTwist_Ioc_bound
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ}
    (hprefix : ∀ m ∈ Finset.Ioc a b,
      ‖∑ n ∈ Finset.Ioc a m,
        vonMangoldtPrimeTwist (-(2 * Real.pi * w)) n‖ ≤ V) :
    ‖primeBlockPoly B w‖ ≤ V / Real.log ((a + 1 : ℕ) : ℝ) := by
  let tau : ℝ := -(2 * Real.pi * w)
  let weight : ℕ → ℝ := fun n => 1 / Real.log (n : ℝ)
  have hweight0 : ∀ n, 0 ≤ weight n := by
    intro n
    dsimp only [weight]
    rcases n with _ | n
    · simp
    · have hnNat : 1 ≤ n + 1 := by omega
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hnNat
      exact one_div_nonneg.mpr (Real.log_nonneg hn)
  have hweightStep : ∀ n ∈ Finset.Ioc a b, weight (n + 1) ≤ weight n := by
    intro n hn
    dsimp only [weight]
    exact invLog_antitone (by
      have := (Finset.mem_Ioc.mp hn).1
      omega)
  have habel := RHTower.norm_sum_Ioc_weight_mul_le
    (fun n => vonMangoldtPrimeTwist tau n) weight hab
      hweight0 hweightStep (B := V) (by simpa only [tau] using hprefix)
  have hweighted :
      (∑ n ∈ Finset.Ioc a b,
        ((weight n : ℝ) : ℂ) * vonMangoldtPrimeTwist tau n) =
        ∑ n ∈ Finset.Ioc a b, primeTwist tau n := by
    apply Finset.sum_congr rfl
    intro n _hn
    dsimp only [weight]
    rw [mul_comm, vonMangoldtPrimeTwist_mul_invLog]
  have hsub : Finset.range (a + 1) ⊆ Finset.range (b + 1) := by
    intro n hn
    simp only [Finset.mem_range] at hn ⊢
    omega
  have hset : Finset.range (b + 1) \ Finset.range (a + 1) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hsumRange : ∑ p ∈ B, primeTwist tau p =
      ∑ n ∈ Finset.Ioc a b, primeTwist tau n := by
    rw [sum_primeTwist_range_eq hab.le hB tau,
      ← Finset.sum_sdiff_eq_sub hsub, hset]
  have hBprime : ∀ p ∈ B, p.Prime := fun p hp => (hB p).1 hp |>.1
  rw [primeBlockPoly_eq_neg_sum hBprime w, norm_neg, hsumRange, ← hweighted]
  simpa only [weight, mul_one_div] using habel

/-- Reverse range Abel selection: an exceptional ordinary prime block contains one actual
log-weighted interval prefix, never an unrelated prefix below the block. -/
theorem exists_norm_vonMangoldtPrimeTwist_Ioc_gt_of_primeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ}
    (hlarge : V / Real.log ((a + 1 : ℕ) : ℝ) < ‖primeBlockPoly B w‖) :
    ∃ m ∈ Finset.Ioc a b,
      V < ‖∑ n ∈ Finset.Ioc a m,
        vonMangoldtPrimeTwist (-(2 * Real.pi * w)) n‖ := by
  by_contra hnot
  push Not at hnot
  have hupper := norm_primeBlockPoly_le_of_vonMangoldtPrimeTwist_Ioc_bound
    ha hab hB w (fun m hm => hnot m hm)
  linarith

/-- Exact interval handoff from an ordinary prime block to a full von Mangoldt-twist interval.
The sole correction is the literal proper-prime-power mass on the ambient interval. -/
theorem exists_norm_vonMangoldtTwist_Ioc_gt_of_primeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ}
    (hlarge : (V + primePowerDefectIoc a b) /
        Real.log ((a + 1 : ℕ) : ℝ) < ‖primeBlockPoly B w‖) :
    ∃ m ∈ Finset.Ioc a b,
      V < ‖∑ n ∈ Finset.Ioc a m,
        vonMangoldtTwist (-(2 * Real.pi * w)) n‖ := by
  obtain ⟨m, hm, hmLarge⟩ :=
    exists_norm_vonMangoldtPrimeTwist_Ioc_gt_of_primeBlockPoly_gt
      ha hab hB w hlarge
  have hdefect := norm_sum_Ioc_vonMangoldtTwist_sub_prime_le
    (-(2 * Real.pi * w)) a m
  have hmono : primePowerDefectIoc a m ≤ primePowerDefectIoc a b :=
    primePowerDefectIoc_mono_right (Finset.mem_Ioc.mp hm).2
  have htri := norm_sub_norm_le
    (∑ n ∈ Finset.Ioc a m, vonMangoldtPrimeTwist (-(2 * Real.pi * w)) n)
    (∑ n ∈ Finset.Ioc a m, vonMangoldtTwist (-(2 * Real.pi * w)) n)
  rw [norm_sub_rev] at htri
  refine ⟨m, hm, ?_⟩
  linarith

/-- Exact exceptional harmonic-block handoff with the lower endpoint preserved throughout.
Reverse reciprocal Abel first selects an ordinary-prime subinterval; reverse logarithmic Abel
and the proper-prime-power correction then select a full von Mangoldt interval prefix inside the
same ambient block. -/
theorem exists_norm_vonMangoldtTwist_Ioc_gt_of_harmonicPrimeBlockPoly_gt
    {B : Finset ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hB : ∀ p, p ∈ B ↔ (p.Prime ∧ a < p ∧ p ≤ b))
    (w : ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hlarge :
      ((V + primePowerDefectIoc a b) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly B w‖) :
    ∃ m ∈ Finset.Ioc a b,
      V < ‖∑ n ∈ Finset.Ioc a m,
        vonMangoldtTwist (-(2 * Real.pi * w)) n‖ := by
  let E : ℝ := (V + primePowerDefectIoc a b) /
    Real.log ((a + 1 : ℕ) : ℝ)
  obtain ⟨u, hau, hub, huLarge⟩ :=
    exists_norm_primeBlockPoly_prefix_gt_of_harmonicPrimeBlockPoly_gt
      hab.le hB w (E := E) (by simpa only [E] using hlarge)
  have hlog : 0 < Real.log ((a + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < a + 1)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (add_nonneg hV (primePowerDefectIoc_nonneg a b)) hlog.le
  have hau' : a < u - 1 := by
    by_contra hnot
    have hueq : u - 1 = a := by omega
    have hempty : primesRange a (u - 1) = ∅ := by
      ext p
      simp [hueq, mem_primesRange]
    rw [hempty, primeBlockPoly, Finset.sum_empty, norm_zero] at huLarge
    linarith
  have hub' : u - 1 ≤ b := by omega
  have hdefect : primePowerDefectIoc a (u - 1) ≤ primePowerDefectIoc a b :=
    primePowerDefectIoc_mono_right hub'
  have hthreshold :
      (V + primePowerDefectIoc a (u - 1)) /
          Real.log ((a + 1 : ℕ) : ℝ) ≤ E := by
    dsimp only [E]
    exact div_le_div_of_nonneg_right (by linarith) hlog.le
  have hprimeRange : ∀ p, p ∈ primesRange a (u - 1) ↔
      (p.Prime ∧ a < p ∧ p ≤ u - 1) := fun p => mem_primesRange
  obtain ⟨m, hm, hmLarge⟩ :=
    exists_norm_vonMangoldtTwist_Ioc_gt_of_primeBlockPoly_gt
      ha hau' hprimeRange w (V := V) (lt_of_le_of_lt hthreshold huLarge)
  exact ⟨m, Finset.mem_Ioc.mpr
    ⟨(Finset.mem_Ioc.mp hm).1, (Finset.mem_Ioc.mp hm).2.trans hub'⟩, hmLarge⟩

end

end RHTower.Sieve
