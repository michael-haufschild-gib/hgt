import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceHeightReceiver
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierCanonicalLongEnergyMoment

/-!
# Long-energy absorption for the sharp source-saving Type-I layers

The short-factor root has already paid its square-product and divisor losses by height while
retaining both negative amplifier powers.  This module replaces the remaining literal long-factor
fourth moment by its unconditional source-energy envelope.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One sharp source-height layer block after the long fourth moment is reduced to source energy. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound
    (C etaLong etaLayer rho : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T etaLayer rho) *
    Real.sqrt (mtTypeILongFourthRpowEnergyBound C etaLong a A T)

/-- One source-height layer block is bounded by the corresponding long-energy block. -/
theorem mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound_le_longEnergy
    {C etaLong etaLayer rho T V : ℝ} (a : ℕ → ℂ)
    (A P ell N : ℕ) (r : Fin ell)
    (hT : 0 ≤ T) (hV : 0 ≤ V) (hetaLayer : 0 < etaLayer)
    (hlong : generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
        mtTypeILongFourthRpowEnergyBound C etaLong a A T) :
    mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound
        etaLayer rho a A P ell N T V r ≤
      mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound
        C etaLong etaLayer rho a A P ell N T V r := by
  have hsqrt := Real.sqrt_le_sqrt hlong
  have hroot : 0 ≤ mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T etaLayer rho := by
    have hdivisor : 0 ≤ divisorBoundConst etaLayer :=
      (divisorBoundConst_pos hetaLayer).le
    rw [mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hdivisor (Real.rpow_nonneg hT _)))
      (by positivity)
  rw [mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt
    (mul_nonneg (div_nonneg (by positivity) hV) (mul_nonneg (by positivity) hroot))

/-- Literal source-scale sub-height receiver with sharp layer sparsity and unconditional long
fourth-energy absorption. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceLongEnergy
    {epsilon etaLayer : ℝ} (hepsilon : 0 < epsilon) (hetaLayer : 0 < etaLayer) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          ∑ r : Fin ell,
            mtTypeIPrimeHeathBrownLayerSourceLongEnergyBlockMomentBound
              C (epsilon / 100) etaLayer (1 / alpha) a A P ell N T V r := by
  obtain ⟨C, hC, hlong⟩ :=
    exists_mtTypeILongFourthAffine_le_rpow_energy
      (show 0 < epsilon / 100 by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceHeight]
      with X hsource
  intro alpha T a A N N' halpha halpha2 hXT hTX hA hN hNT hNN' hN'le
  dsimp only
  have hbase := hsource alpha T a A N N' epsilon etaLayer
    halpha halpha2 hXT hTX hN hNT hNN' hN'le hetaLayer
  have hT0 : 0 ≤ T := (by positivity : (0 : ℝ) ≤ N).trans hNT
  have hlong' := hlong a A T hA hT0
  change generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
      generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
        (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T ≤
      mtTypeILongFourthRpowEnergyBound C (epsilon / 100) a A T at hlong'
  have hV : 0 ≤ ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound
          etaLayer (1 / alpha) a A (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T
            ((((mtTypeIPrimeScale X alpha ^
              mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
                (-epsilon / 10)) r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound_le_longEnergy
        a A (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N r
          hT0 hV hetaLayer hlong'

end

end RHTower.Sieve
