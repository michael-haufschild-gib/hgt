import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSparseMoment

/-!
# Source-schedule energy absorption for the Heath--Brown Type-I receiver

Equation (5.4) bounds every powered-prime block energy by
`(P^ell)^(1 + 1/alpha)`.  This file inserts that exact source-schedule bound into the sparse
Heath--Brown moment receiver, leaving no arbitrary prime-block energy on its theorem surface.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Type-I block moment with both sparse loss and exact powered-prime energy absorbed. -/
noncomputable def mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound
    (epsilon alpha : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Equation (5.4) removes the literal block energy from the sparse block receiver. -/
theorem mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound_le_energy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (a : ℕ → ℂ)
    (A P ell N : ℕ) (T V alpha : ℝ) (r : Fin ell)
    (hT : 0 ≤ T) (hV : 0 < V)
    (henergy : ∑ m ∈ Finset.Ioc (mtTypeIPrimeHeathBrownBlockLength P ell r)
          (2 * mtTypeIPrimeHeathBrownBlockLength P ell r),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) :
    mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound
        epsilon a A P ell N T V r ≤
      mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound
        epsilon alpha a A P ell N T V r := by
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  have hcoeff :
      0 ≤ mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon :=
    mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient_nonneg hepsilon hT
  have hsqrt := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left henergy hcoeff)
  rw [mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound,
    mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)

/-- Source-scale sub-height receiver after exact equation-(5.4) energy absorption. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_sparseEnergy_sourceScale
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < V →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownSparseEnergyBlockMomentBound
            epsilon alpha a A P ell N T V r := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_sparse_sourceScale hepsilon,
      hlog, hXlarge] with X hsource hlogX hX
  intro alpha T a A N N' V halpha halpha2 hXT hTX hN hNT hNN' hN'le hV
  dsimp only
  have halpha1 : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hlogOne : (1 : ℝ) ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
  have hscale : Real.exp 2 ≤ (Real.log X) ^ alpha := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogOne halpha1
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hTgt : 1 < T := by linarith
  have hT0 : 0 ≤ T := hTgt.le.trans' (by norm_num)
  have hbase := hsource alpha T a A N N' V halpha halpha2 hXT hTX
    hN hNT hNN' hN'le hV
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound epsilon a A
          (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T V r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownSparseEpsilonBlockMomentBound_le_energy hepsilon a A
        (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T V alpha r hT0 hV
          (sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_source_schedule
            (mtTypeIPrimeHeathBrownBlockLength
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r)
            (by linarith) hX hscale hTgt hTX)

end

end RHTower.Sieve
