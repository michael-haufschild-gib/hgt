import GaloisForLFunctions.RHTower.Sieve.PrimeWindowPaperScale
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorMean

/-!
# Same-block prime collisions at the Matomäki--Teräväinen scale

The `c₃,n` term of Lemma 2.3 is nonzero only when an integer has two prime factors in one
`(1+δ_A)`-adic block.  Distinct factors are controlled by a factorial pair moment; equal factors
are controlled by square divisibility.  This file substitutes the paper's literal `z₀` and `δ_A`
and combines both cases into a uniform collision envelope.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Reciprocal mass of every paper-width block above `z₀` is at most `2δ_A`. -/
theorem eventually_sum_inv_primesIco_le_two_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ ⦃a b : ℕ⦄,
      mtLowerCutoff X ≤ ((a - 1 : ℕ) : ℝ) → a ≤ b →
      ((b - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((a - 1 : ℕ) : ℝ) →
      ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤ 2 * mtPaperWidth A X := by
  obtain ⟨B, c, N₀, hc, hB, hN₀, hmass⟩ :=
    exists_sum_inv_primesIco_le_logLog_diff_add_exp
  have herr := eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (K := ((10 * A + 1 : ℕ) : ℝ)) hB hc
  rw [eventually_atTop] at herr
  obtain ⟨U, hU⟩ := herr
  have hcutoff : Tendsto mtLowerCutoff atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_mtLowerLogCutoff_atTop
  have hlarge := hcutoff.eventually_ge_atTop (max (N₀ : ℝ) U)
  filter_upwards [hlarge,
    eventually_log_rpow_le_paperWidth_of_mtLowerLogCutoff_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hlargeX hscaleX hX
  intro a b hcut hab hband
  let δ : ℝ := mtPaperWidth A X
  have hu0R : 0 < ((a - 1 : ℕ) : ℝ) :=
    (Real.exp_pos (mtLowerLogCutoff X)).trans_le hcut
  have hu0 : 0 < a - 1 := by exact_mod_cast hu0R
  have ha : 1 ≤ a := by omega
  have hN₀R : (N₀ : ℝ) ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans (hlargeX.trans hcut)
  have hN₀a : N₀ ≤ a - 1 := by exact_mod_cast hN₀R
  have hUR : U ≤ ((a - 1 : ℕ) : ℝ) :=
    (le_max_right _ _).trans (hlargeX.trans hcut)
  have herru := hU (((a - 1 : ℕ) : ℝ)) hUR
  have hlogcut : mtLowerLogCutoff X ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    have hmono := Real.log_le_log (Real.exp_pos (mtLowerLogCutoff X)) hcut
    simpa only [mtLowerCutoff, Real.log_exp] using hmono
  have herrδ :
      2 * B * Real.exp (-c * Real.sqrt (Real.log ((a - 1 : ℕ) : ℝ))) ≤ δ :=
    herru.trans (hscaleX hlogcut)
  have hu3 : 3 ≤ a - 1 := hN₀.trans hN₀a
  have huv : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
  have hlog1 : 1 ≤ Real.log ((a - 1 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hcast : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by exact_mod_cast hu3
    linarith [Real.exp_one_lt_d9]
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    have hlogX : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hX)]
      exact hX
    exact Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _
  have hinc := logLog_sub_le_delta_div_log hu3 huv hδ0 hband
  have hdiv : δ / Real.log ((a - 1 : ℕ) : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log ((a - 1 : ℕ) : ℝ))]
    nlinarith
  have hm := hmass ha hab hN₀a
  linarith

/-- Distinct same-block prime pairs have total mean at most `2Yδ_A` times outer prime mass. -/
theorem eventually_sum_primePairDivisorCount_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (b : ℕ → ℕ) (Y : ℕ),
      (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, mtLowerCutoff X ≤ (p : ℝ)) →
      (∀ p ∈ S, p + 1 ≤ b p) →
      (∀ p ∈ S, ((b p - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * (p : ℝ)) →
      ∑ n ∈ Finset.Icc 1 Y,
          primePairDivisorCount S (fun p => primesIco (p + 1) (b p)) n ≤
        2 * (Y : ℝ) * mtPaperWidth A X * ∑ p ∈ S, 1 / (p : ℝ) := by
  filter_upwards [eventually_sum_inv_primesIco_le_two_paperWidth A] with X hmassX
  intro S b Y hprime hlower hle hband
  have hS : ∀ p ∈ S, 0 < p := fun p hp => (hprime p hp).pos
  have hT : ∀ p ∈ S, ∀ q ∈ primesIco (p + 1) (b p), 0 < q := by
    intro p hp q hq
    exact (mem_primesIco.mp hq).2.2.pos
  have hmass : ∀ p ∈ S,
      ∑ q ∈ primesIco (p + 1) (b p), 1 / (q : ℝ) ≤ 2 * mtPaperWidth A X := by
    intro p hp
    have hpSub : p + 1 - 1 = p := by omega
    simpa only [hpSub] using
      hmassX (a := p + 1) (b := b p) (hlower p hp) (hle p hp) (hband p hp)
  have h := sum_primePairDivisorCount_le_of_fibreMass
    S (fun p => primesIco (p + 1) (b p)) Y hS hT hmass
  nlinarith

/-- The lower-cutoff logarithm eventually dominates `sqrt(log X)`. -/
theorem eventually_sqrt_log_le_mtLowerLogCutoff :
    ∀ᶠ X : ℝ in atTop, Real.sqrt (Real.log X) ≤ mtLowerLogCutoff X := by
  have hll := eventually_logLogPow_le_rpow 3 (ε := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hll, Filter.eventually_gt_atTop (Real.exp (Real.exp 1))]
    with X hllX hX
  have hL : 0 < Real.log X := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp (Real.exp 1) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (Real.exp_pos 1)
    linarith
  have hLL : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    have hexp : Real.exp 1 < Real.log X := by
      have hmono := Real.strictMonoOn_log (Real.exp_pos (Real.exp 1))
        (lt_trans (Real.exp_pos (Real.exp 1)) hX) hX
      simpa only [Real.log_exp] using hmono
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    linarith
  rw [Real.sqrt_eq_rpow]
  change (Real.log X) ^ (1 / 2 : ℝ) ≤
    Real.log X / (Real.log (Real.log X)) ^ 3
  rw [le_div_iff₀ (pow_pos hLL 3)]
  calc
    (Real.log X) ^ (1 / 2 : ℝ) * (Real.log (Real.log X)) ^ 3 ≤
        (Real.log X) ^ (1 / 2 : ℝ) * (Real.log X) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hllX (Real.rpow_nonneg hL.le _)
    _ = Real.log X := by
      rw [← Real.rpow_add hL]
      norm_num

/-- Reciprocal of `z₀` is eventually at most the paper width. -/
theorem eventually_mtLowerCutoff_inv_le_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, (mtLowerCutoff X)⁻¹ ≤ mtPaperWidth A X := by
  have hdecay := eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (B := (1 / 2 : ℝ)) (c := (1 : ℝ)) (K := ((10 * A : ℕ) : ℝ))
    (by norm_num) (by norm_num)
  filter_upwards [eventually_sqrt_log_le_mtLowerLogCutoff, hdecay]
    with X hlower hdecayX
  have hexp : Real.exp (-mtLowerLogCutoff X) ≤
      Real.exp (-Real.sqrt (Real.log X)) := by
    rw [Real.exp_le_exp]
    linarith
  have hdecayX' : Real.exp (-Real.sqrt (Real.log X)) ≤ mtPaperWidth A X := by
    norm_num at hdecayX
    rw [mtPaperWidth]
    push_cast
    exact hdecayX
  calc
    (mtLowerCutoff X)⁻¹ = Real.exp (-mtLowerLogCutoff X) := by
      rw [mtLowerCutoff, Real.exp_neg]
    _ ≤ Real.exp (-Real.sqrt (Real.log X)) := hexp
    _ ≤ mtPaperWidth A X := hdecayX'

/-- Every prime above `z₀` has reciprocal at most `δ_A`. -/
theorem eventually_recip_le_paperWidth_of_mtLowerCutoff_le (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {u : ℝ}, mtLowerCutoff X ≤ u →
      1 / u ≤ mtPaperWidth A X := by
  filter_upwards [eventually_mtLowerCutoff_inv_le_paperWidth A] with X hcutoff
  intro u hu
  have hpos : 0 < mtLowerCutoff X := Real.exp_pos _
  have hrecip : 1 / u ≤ 1 / mtLowerCutoff X := one_div_le_one_div_of_le hpos hu
  have hcutoff' : 1 / mtLowerCutoff X ≤ mtPaperWidth A X := by
    simpa only [one_div] using hcutoff
  exact hrecip.trans hcutoff'

/-- Count of distinct or repeated prime-pair collisions in the prescribed short fibres. -/
def primeBlockCollisionCount (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ) : ℝ :=
  primePairDivisorCount S (fun p => primesIco (p + 1) (b p)) n +
    primeSquareDivisorCount S n

/-- Full same-block collision mean, including equal-prime square divisors. -/
theorem eventually_sum_primeBlockCollisionCount_paperWidth (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (b : ℕ → ℕ) (Y : ℕ),
      (∀ p ∈ S, p.Prime) →
      (∀ p ∈ S, mtLowerCutoff X ≤ (p : ℝ)) →
      (∀ p ∈ S, p + 1 ≤ b p) →
      (∀ p ∈ S, ((b p - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * (p : ℝ)) →
      ∑ n ∈ Finset.Icc 1 Y, primeBlockCollisionCount S b n ≤
        3 * (Y : ℝ) * mtPaperWidth A X * ∑ p ∈ S, 1 / (p : ℝ) := by
  filter_upwards [eventually_sum_primePairDivisorCount_paperWidth A,
    eventually_recip_le_paperWidth_of_mtLowerCutoff_le A] with X hpairsX hrecipX
  intro S b Y hprime hlower hle hband
  have hS : ∀ p ∈ S, 0 < p := fun p hp => (hprime p hp).pos
  have hpairs := hpairsX S b Y hprime hlower hle hband
  have hsquares := sum_primeSquareDivisorCount_le_of_recip S Y hS
    (fun p hp => hrecipX (hlower p hp))
  rw [show (∑ n ∈ Finset.Icc 1 Y, primeBlockCollisionCount S b n) =
      (∑ n ∈ Finset.Icc 1 Y,
        primePairDivisorCount S (fun p => primesIco (p + 1) (b p)) n) +
      ∑ n ∈ Finset.Icc 1 Y, primeSquareDivisorCount S n by
        simp only [primeBlockCollisionCount, Finset.sum_add_distrib]]
  nlinarith

end

end RHTower.Sieve
