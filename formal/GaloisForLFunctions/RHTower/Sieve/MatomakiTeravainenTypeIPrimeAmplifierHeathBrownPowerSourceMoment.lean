import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownAbsorbedSourceMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerMoment

/-!
# Height-power source Type-I receiver

On the sub-height branch `N ≤ T`, this transports the factorial-free source receiver to the final
coefficient: a fixed constant times `T^(12 eta)` and the literal two-scale moment bracket.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Height-power Type-I bound charged to one powered-prime block. -/
noncomputable def mtTypeIPrimeHeathBrownPowerBlockMomentBound
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient N B T eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- A factorial-free block is dominated by the final height-power block. -/
theorem mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound_le_power
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hNT : (N : ℝ) ≤ T) (hV : 0 < V) (heta : 0 < eta) :
    mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound eta a A P ell N N' T V r ≤
      mtTypeIPrimeHeathBrownPowerBlockMomentBound eta a A P ell N T V r := by
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hT : 2 ≤ T := hNreal.trans hNT
  let T' : Set.Ioi (0 : ℝ) := ⟨T, zero_lt_two.trans_le hT⟩
  have hcoeff := mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient_le_power
    (N' := N') (B := B) T' hN hN'le hNT hT heta
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hinside := mul_le_mul_of_nonneg_right hcoeff henergy
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound,
    mtTypeIPrimeHeathBrownPowerBlockMomentBound]
  dsimp only [B, T'] at hsqrt ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)

/-- Source-scale sub-height Type-I receiver with all factorial and small-power losses absorbed. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_power_sourceScale :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V eta : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < V → 0 < eta →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownPowerBlockMomentBound
            eta a A P ell N T V r := by
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_absorbed_sourceScale]
      with X hsource
  intro alpha T a A N N' V eta halpha halpha2 hXT hTX hN hNT hNN' hN'le hV heta
  dsimp only
  have hbase := hsource alpha T a A N N' V eta halpha halpha2 hXT hTX
    hN hNN' hN'le hV heta
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound eta a A
          (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound_le_power eta a A
        (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r
          hN hN'le hNT hV heta

/-- Published-epsilon Type-I bound charged to one powered-prime block. -/
noncomputable def mtTypeIPrimeHeathBrownEpsilonBlockMomentBound
    (epsilon : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownEpsilonMomentCoefficient N B T epsilon *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Choosing `eta = epsilon/24` turns the power block into the published-epsilon block. -/
theorem mtTypeIPrimeHeathBrownPowerBlockMomentBound_epsilon_eq
    (epsilon : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ) (r : Fin ell) :
    mtTypeIPrimeHeathBrownPowerBlockMomentBound
        (epsilon / 24) a A P ell N T V r =
      mtTypeIPrimeHeathBrownEpsilonBlockMomentBound
        epsilon a A P ell N T V r := by
  rw [mtTypeIPrimeHeathBrownPowerBlockMomentBound,
    mtTypeIPrimeHeathBrownEpsilonBlockMomentBound]
  rw [mtTypeIPrimeRaisedHeathBrownPowerMomentCoefficient_epsilon_eq]

/-- Source-scale sub-height receiver with all small powers charged to `T^(epsilon/2)`. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_epsilon_sourceScale
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
          mtTypeIPrimeHeathBrownEpsilonBlockMomentBound
            epsilon a A P ell N T V r := by
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_power_sourceScale]
      with X hsource
  intro alpha T a A N N' V halpha halpha2 hXT hTX hN hNT hNN' hN'le hV
  have h := hsource alpha T a A N N' V (epsilon / 24) halpha halpha2 hXT hTX
    hN hNT hNN' hN'le hV (by linarith)
  simpa only [mtTypeIPrimeHeathBrownPowerBlockMomentBound_epsilon_eq] using h

end

end RHTower.Sieve
