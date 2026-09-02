import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeILongFourthEnergy

/-!
# Canonical Type-I receiver with long fourth-moment energy absorbed

The unconditional product-fibre estimate replaces the affine fourth-moment expression by the
paper-shape factor `(A^-2 + T A^-4)` times the square of the literal dyadic coefficient energy.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Long-factor fourth-moment envelope after divisor-fibre energy absorption. -/
def mtTypeILongFourthRpowEnergyBound
    (C eta : ℝ) (a : ℕ → ℂ) (A : ℕ) (T : ℝ) : ℝ :=
  C * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta *
    (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2) +
      (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2) * T) *
    (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) ^ 2

/-- Canonical Type-I block after the long fourth moment is reduced to source energy. -/
noncomputable def mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
    (C eta epsilon alpha : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T : ℝ)
    (_r : Fin ell) : ℝ :=
  (ell : ℝ) * (((P ^ ell : ℕ) : ℝ)) ^ (epsilon / 10) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) *
    Real.sqrt (mtTypeILongFourthRpowEnergyBound C eta a A T)

/-- Long affine energy absorption for one normalized canonical block. -/
theorem mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound_le_longEnergy
    {C eta epsilon alpha T : ℝ} (a : ℕ → ℂ) (A P ell N : ℕ)
    (r : Fin ell)
    (hlong : generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
        mtTypeILongFourthRpowEnergyBound C eta a A T) :
    mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound
        epsilon alpha a A P ell N T r ≤
      mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
        C eta epsilon alpha a A P ell N T r := by
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound,
    mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Source-facing height dichotomy with the complete sub-height long fourth moment reduced to
literal dyadic coefficient energy. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceLongEnergyHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
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
              mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
                C (epsilon / 100) epsilon alpha a A P ell N T r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound D epsilon a A P ell N T
                ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r := by
  obtain ⟨C, hC, hlong⟩ :=
    exists_mtTypeILongFourthAffine_le_rpow_energy
      (show 0 < epsilon / 100 by linarith)
  obtain ⟨D, hD, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceNormalizedHeightDichotomy
      hepsilon
  refine ⟨C, D, hC, hD, ?_⟩
  filter_upwards [hsource] with X hsourceX
  intro alpha T a A N N' halpha halpha2 hXT hTX hA hN hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T a A N N' halpha halpha2 hXT hTX
    hA hN hNN' hN'le
  dsimp only at hbase
  by_cases hNT : (N : ℝ) ≤ T
  · have hN0 : (0 : ℝ) ≤ N := by positivity
    have hT0 : 0 ≤ T := hN0.trans hNT
    have hlong' := hlong a A T hA hT0
    change generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
      generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
      mtTypeILongFourthRpowEnergyBound C (epsilon / 100) a A T at hlong'
    calc
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound epsilon alpha a A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r := by
              simpa only [hNT, if_true] using hbase
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalLongEnergyBlockMomentBound
            C (epsilon / 100) epsilon alpha a A
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r :=
        Finset.sum_le_sum fun r _ =>
          mtTypeIPrimeHeathBrownNormalizedEnergyBlockMomentBound_le_longEnergy
            a A (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N r hlong'
      _ = _ := by rw [if_pos hNT]
  · simpa only [hNT, if_false] using hbase

end

end RHTower.Sieve
