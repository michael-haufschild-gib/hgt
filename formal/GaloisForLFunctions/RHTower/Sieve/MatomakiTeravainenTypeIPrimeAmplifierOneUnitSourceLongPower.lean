import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceLongEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeILongCoefficientPowerEnergy

/-!
# Divisor and height-power absorption for the one-unit Type-I receiver

For fixed divisor-majorant data, the literal long-factor energy is replaced first by its explicit
polylogarithmic divisor envelope and then by an arbitrarily small fixed height power.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One-unit source block with long coefficient energy replaced by its divisor envelope. -/
noncomputable def mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound
    (D C₀ eta C epsilon alpha : ℝ) (w A P ell N N' : ℕ)
    (T V : ℝ) (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (D * T ^ epsilon *
        (T + ((((2 * B) * N' : ℕ) : ℝ))) *
        (1 / (B : ℝ) ^ 2) *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha) *
        (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2) *
    Real.sqrt (mtTypeILongFourthDivisorBound C₀ eta C w A T)

/-- Literal long coefficient energy is absorbed into its fixed divisor envelope. -/
theorem mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound_le_divisor
    {D C₀ eta C epsilon alpha T V : ℝ} (a : ℕ → ℂ)
    {w A P ell N N' : ℕ} (r : Fin ell)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T) (hA : 1 ≤ A) (hAT : (A : ℝ) ≤ T)
    (hV : 0 < V)
    (hpoint : ∀ {n : ℕ}, 0 < n → ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) :
    mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound
        D C₀ eta epsilon alpha a A P ell N N' T V r ≤
      mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound
        D C₀ eta C epsilon alpha w A P ell N N' T V r := by
  have hlong := mtTypeILongFourthRpowEnergyBound_le_divisorBound
    (eta := eta) hC₀ hT hA hAT a hpoint
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound,
    mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- One-unit source block after paying the fixed long polylogarithm by `T^rho`. -/
noncomputable def mtTypeIPrimeOneUnitSourceLongPowerBlockMomentBound
    (D C₀ eta rho epsilon alpha : ℝ) (A P ell N N' : ℕ)
    (T V : ℝ) (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (D * T ^ epsilon *
        (T + ((((2 * B) * N' : ℕ) : ℝ))) *
        (1 / (B : ℝ) ^ 2) *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha) *
        (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2) *
    Real.sqrt (mtTypeILongFourthHeightPowerBound C₀ eta rho A T)

/-- The divisor-envelope block is absorbed by its selected long height-power envelope. -/
theorem mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound_le_longPower
    {D C₀ eta rho C epsilon alpha T V : ℝ} {w A P ell N N' : ℕ}
    (r : Fin ell) (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T) (hV : 0 < V)
    (hfactor : mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ rho) :
    mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound
        D C₀ eta C epsilon alpha w A P ell N N' T V r ≤
      mtTypeIPrimeOneUnitSourceLongPowerBlockMomentBound
        D C₀ eta rho epsilon alpha A P ell N N' T V r := by
  have hlong := mtTypeILongFourthDivisorBound_le_heightPower
    (eta := eta) (A := A) hC₀ hT hfactor
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound,
    mtTypeIPrimeOneUnitSourceLongPowerBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Source-scale one-unit receiver after all fixed long-coefficient polylogarithms are absorbed
into `T^(epsilon/100)`. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_oneUnit_sourceLongPower
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (C : ℝ) (w : ℕ) :
    ∃ D C₀ : ℝ, 0 < D ∧ 0 < C₀ ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        (∀ {n : ℕ}, 0 < n → ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) →
        1 ≤ A → (A : ℝ) ≤ T → 1 ≤ N → (N : ℝ) ≤ T →
        N < N' → N' ≤ 2 * N → 0 < V →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          ∑ r : Fin ell,
            mtTypeIPrimeOneUnitSourceLongPowerBlockMomentBound
              D C₀ (epsilon / 100) (epsilon / 100) epsilon alpha
                A P ell N N' T V r := by
  obtain ⟨D, C₀, hD, hC₀, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_oneUnit_sourceLongEnergy hepsilon
  have hfactor := eventually_mtTypeILongCoefficientPolylogFactor_le_rpow
    C w (show 0 < epsilon / 100 by linarith)
  obtain ⟨T₀, hfactorT₀⟩ := Filter.eventually_atTop.1 hfactor
  have hheight : ∀ᶠ X : ℝ in atTop, T₀ ≤ X ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (show 0 < (1 / 4 : ℝ) by norm_num)).eventually_ge_atTop T₀
  refine ⟨D, C₀, hD, hC₀, ?_⟩
  filter_upwards [hsource, hheight] with X hsourceX hheightX
  intro alpha T a A N N' V halpha halpha2 hXT hTX hpoint hA hAT hN hNT
    hNN' hN' hV
  dsimp only
  have hbase := hsourceX alpha T a A N N' V halpha halpha2 hXT hTX
    hA hN hNT hNN' hN' hV
  have hT : (1 : ℝ) ≤ T := by
    exact (by exact_mod_cast hN : (1 : ℝ) ≤ N).trans hNT
  have hfactorT : mtTypeILongCoefficientPolylogFactor C w T ≤
      T ^ (epsilon / 100) := hfactorT₀ T (hheightX.trans hXT)
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound
          D C₀ (epsilon / 100) epsilon alpha a A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r := hbase
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound
          D C₀ (epsilon / 100) C epsilon alpha w A
            (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r :=
      Finset.sum_le_sum fun r _ =>
        mtTypeIPrimeOneUnitSourceLongEnergyBlockMomentBound_le_divisor
          a r hC₀.le hT hA hAT hV hpoint
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeOneUnitSourceDivisorBlockMomentBound_le_longPower
        r hC₀.le hT hV hfactorT

end

end RHTower.Sieve
