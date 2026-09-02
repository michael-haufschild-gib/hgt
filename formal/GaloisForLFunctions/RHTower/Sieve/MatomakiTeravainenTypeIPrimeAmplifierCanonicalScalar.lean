import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierSourceLargeSet

/-!
# Canonical-threshold scalar normalization for the Type-I prime amplifier

The Section-5.1 threshold is `(P^ell)^(-epsilon/10)`.  Since the powered length is positive,
division by this threshold is exactly multiplication by `(P^ell)^(epsilon/10)`.  This file
normalizes that factor in the source-facing Type-I receiver.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Division by the canonical amplifier threshold is the corresponding positive power. -/
theorem mtTypeIPrimeCanonicalThreshold_div_eq
    {P ell : ℕ} (hP : 1 ≤ P) (epsilon : ℝ) :
    (ell : ℝ) / ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) =
      (ell : ℝ) * (((P ^ ell : ℕ) : ℝ)) ^ (epsilon / 10) := by
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  have hMnat : 0 < P ^ ell := pow_pos hPpos ell
  have hM : (0 : ℝ) < ((P ^ ell : ℕ) : ℝ) := by exact_mod_cast hMnat
  have hexponent : -epsilon / 10 = -(epsilon / 10) := by ring
  rw [hexponent, Real.rpow_neg hM.le, div_eq_mul_inv, inv_inv]

/-- Canonical source block with threshold division written as an explicit positive amplifier
power. -/
noncomputable def mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound
    (epsilon alpha : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T : ℝ)
    (_r : Fin ell) : ℝ :=
  (ell : ℝ) * (((P ^ ell : ℕ) : ℝ)) ^ (epsilon / 10) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Canonical and normalized block expressions agree exactly. -/
theorem mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound_eq_normalized
    (epsilon alpha : ℝ) (a : ℕ → ℂ) (A : ℕ) {P ell N : ℕ}
    (hP : 1 ≤ P) (T : ℝ) (r : Fin ell) :
    mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound
        epsilon alpha a A P ell N T r =
      mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound
        epsilon alpha a A P ell N T r := by
  rw [mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound,
    mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound,
    mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound,
    mtTypeIPrimeCanonicalThreshold_div_eq hP epsilon]

/-- Source-facing height dichotomy with canonical threshold normalized to the explicit factor
`ell * (P^ell)^(epsilon/10)`. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceNormalizedHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 2 ≤ N → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound
                epsilon alpha a A P ell N T r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T
                ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceSparseEnergyHeightDichotomy
      hepsilon
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsource, eventually_mtTypeIPrimeScale_two_le] with X hsourceX hP
  intro alpha T a A N N' halpha halpha2 hXT hTX hA hN hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX
    hA hN hNN' hN'le
  dsimp only at hbase
  by_cases hNT : (N : ℝ) ≤ T
  · calc
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound epsilon alpha a A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r := by
              simpa only [hNT, if_true] using hbase
      _ = ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound epsilon alpha a A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r :=
        Finset.sum_congr rfl fun r _ =>
        mtTypeIPrimeHeathBrownCanonicalEnergyBlockMomentBound_eq_normalized
          epsilon alpha a A (one_le_two.trans (hP alpha (by linarith))) T r
      _ = _ := by rw [if_pos hNT]
  · simpa only [hNT, if_false] using hbase

end

end RHTower.Sieve
