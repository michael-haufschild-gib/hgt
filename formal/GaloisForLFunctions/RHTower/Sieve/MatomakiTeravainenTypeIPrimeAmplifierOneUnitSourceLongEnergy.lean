import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierCanonicalLongEnergyMoment

/-!
# Long-energy absorption for the one-unit Type-I receiver

The ordinary fourth moment of the long factor is replaced by its exact dyadic coefficient-energy
envelope.  This preserves the coefficient-faithful one-unit mixed moment without retaining an
analytic fourth-moment premise.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One-unit source block after reducing the long fourth moment to coefficient energy. -/
noncomputable def mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound
    (C C₀ eta epsilon alpha : ℝ) (a : ℕ → ℂ)
    (A P ell N N' : ℕ) (T V : ℝ) (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (C * T ^ epsilon *
        (T + ((((2 * B) * N' : ℕ) : ℝ))) *
        (1 / (B : ℝ) ^ 2) *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha) *
        (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2) *
    Real.sqrt (mtTypeILongFourthRpowEnergyBound C₀ eta a A T)

/-- Long affine energy absorption for one one-unit source block. -/
theorem mtTypeIPrimeOneUnitSourceBlockMomentBound_le_longEnergy
    {C C₀ eta epsilon alpha T V : ℝ} (a : ℕ → ℂ)
    (A P ell N N' : ℕ) (r : Fin ell)
    (hV : 0 < V)
    (hlong : generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
        mtTypeILongFourthRpowEnergyBound C₀ eta a A T) :
    mtTypeIPrimeOneUnitSourceBlockMomentBound
        C epsilon alpha a A P ell N N' T V r ≤
      mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound
        C C₀ eta epsilon alpha a A P ell N N' T V r := by
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeOneUnitSourceBlockMomentBound,
    mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Source-scale one-unit receiver with long fourth moment reduced unconditionally to literal
dyadic coefficient energy. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_oneUnit_sourceLongEnergy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 1 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < V →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          ∑ r : Fin ell,
            mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound
              C C₀ (epsilon / 100) epsilon alpha a A P ell N N' T V r := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_oneUnit_sourceScale hepsilon
  obtain ⟨C₀, hC₀, hlong⟩ :=
    exists_mtTypeILongFourthAffine_le_rpow_energy
      (show 0 < epsilon / 100 by linarith)
  refine ⟨C, C₀, hC, hC₀, ?_⟩
  filter_upwards [hsource] with X hsourceX
  intro alpha T a A N N' V halpha halpha2 hXT hTX hA hN hNT hNN' hN' hV
  dsimp only
  have hbase := hsourceX alpha T a A N N' V halpha halpha2 hXT hTX
    hA hN hNT hNN' hN' hV
  have hT0 : 0 ≤ T := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    exact hN0.trans hNT
  have hlong' := hlong a A T hA hT0
  change generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
      (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
    generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
      (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
    mtTypeILongFourthRpowEnergyBound C₀ (epsilon / 100) a A T at hlong'
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeOneUnitSourceBlockMomentBound C epsilon alpha a A
          (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeOneUnitSourceBlockMomentBound_le_longEnergy a A
        (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' r hV hlong'

end

end RHTower.Sieve
