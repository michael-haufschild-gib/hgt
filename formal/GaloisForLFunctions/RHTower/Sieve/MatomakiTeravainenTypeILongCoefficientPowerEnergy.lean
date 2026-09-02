import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeILongCoefficientEnergy
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Height-power absorption for the Type-I long coefficient energy

Once the divisor-bound witnesses are fixed, their explicit polylogarithm is eventually smaller
than any prescribed positive power of the height.  Witnesses are fixed before the eventual source
scale; no uniformity over arbitrary divisor exponents is asserted.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Every fixed Type-I coefficient polylogarithm is eventually below an arbitrary positive
height power. -/
theorem eventually_mtTypeILongCoefficientPolylogFactor_le_rpow
    (C : ℝ) (w : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ T : ℝ in atTop,
      mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ rho := by
  let E : ℕ := 2 ^ (2 * w) - 1
  have hpoly := eventually_const_mul_rpow_polylog_le_rpow
    (C := 2 * C ^ 2 * (2 : ℝ) ^ E) (α := (0 : ℝ)) (β := rho) E hrho
  filter_upwards [hpoly] with T hT
  calc
    mtTypeILongCoefficientPolylogFactor C w T =
        (2 * C ^ 2 * (2 : ℝ) ^ E) * T ^ (0 : ℝ) *
          (1 + |Real.log T|) ^ E := by
      rw [mtTypeILongCoefficientPolylogFactor, mul_pow, Real.rpow_zero]
      dsimp only [E]
      ring
    _ ≤ T ^ rho := hT

/-- Long fourth-moment envelope after a fixed divisor polylogarithm is paid by `T^rho`. -/
def mtTypeILongFourthHeightPowerBound
    (C₀ eta rho : ℝ) (A : ℕ) (T : ℝ) : ℝ :=
  C₀ * ((((2 * A) * (2 * A) : ℕ) : ℝ)) ^ eta *
    (5 * Real.pi * Real.exp 1 * (1 / (A : ℝ) ^ 2) +
      (5 * Real.pi / 2) * (1 / ((A : ℝ) ^ 2) ^ 2) * T) *
    (T ^ rho * (A : ℝ)) ^ 2

/-- Polylogarithmic long energy is monotone under its selected height-power envelope. -/
theorem mtTypeILongFourthDivisorBound_le_heightPower
    {C₀ eta rho T C : ℝ} (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    {w A : ℕ}
    (hfactor : mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ rho) :
    mtTypeILongFourthDivisorBound C₀ eta C w A T ≤
      mtTypeILongFourthHeightPowerBound C₀ eta rho A T := by
  have hfactor0 : 0 ≤ mtTypeILongCoefficientPolylogFactor C w T := by
    rw [mtTypeILongCoefficientPolylogFactor]
    positivity
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hA0
  have hsq := pow_le_pow_left₀ (mul_nonneg hfactor0 hA0) hmul 2
  rw [mtTypeILongFourthDivisorBound, mtTypeILongFourthHeightPowerBound]
  gcongr

/-- Canonical Type-I block with the long coefficient polylogarithm replaced by `T^rho`. -/
noncomputable def mtTypeIPrimeHeathBrownCanonicalLongPowerBlockMomentBound
    (C₀ eta rho epsilon alpha : ℝ) (A P ell N : ℕ) (T : ℝ)
    (_r : Fin ell) : ℝ :=
  (ell : ℝ) * (((P ^ ell : ℕ) : ℝ)) ^ (epsilon / 10) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSparseEpsilonMomentCoefficient N T epsilon *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) *
    Real.sqrt (mtTypeILongFourthHeightPowerBound C₀ eta rho A T)

/-- One canonical divisor-envelope block is absorbed by its fixed height-power envelope. -/
theorem mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound_le_longPower
    {C₀ eta rho T C epsilon alpha : ℝ}
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    {w A P ell N : ℕ}
    (hfactor : mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ rho)
    (r : Fin ell) :
    mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
        C₀ eta C epsilon alpha w A P ell N T r ≤
      mtTypeIPrimeHeathBrownCanonicalLongPowerBlockMomentBound
        C₀ eta rho epsilon alpha A P ell N T r := by
  have hlong := mtTypeILongFourthDivisorBound_le_heightPower
    (eta := eta) (A := A) hC₀ hT hfactor
  have hsqrt := Real.sqrt_le_sqrt hlong
  rw [mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound,
    mtTypeIPrimeHeathBrownCanonicalLongPowerBlockMomentBound]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- Source-facing height dichotomy after every fixed long-coefficient polylogarithm is absorbed
into `T^(epsilon/100)`. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceLongPowerHeightDichotomy
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (C : ℝ) (w : ℕ) :
    ∃ C₀ D : ℝ, 0 < C₀ ∧ 0 < D ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        (∀ {n : ℕ}, 0 < n → ‖a n‖ ≤ C * ((n.divisors.card : ℝ) ^ w)) →
        1 ≤ A → (A : ℝ) ≤ T → 2 ≤ N → N < N' → N' ≤ 2 * N →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          if (N : ℝ) ≤ T then
            ∑ r : Fin ell,
              mtTypeIPrimeHeathBrownCanonicalLongPowerBlockMomentBound
                C₀ (epsilon / 100) (epsilon / 100) epsilon alpha A P ell N T r
          else
            ∑ r : Fin ell,
              mtTypeIPrimeBlockMomentBound D epsilon a A P ell N T
                ((((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)) r := by
  obtain ⟨C₀, D, hC₀, hD, hsource⟩ :=
    exists_eventually_setIntegral_mtTypeI_primeAmplifier_sourceDivisorHeightDichotomy
      hepsilon
  have hfactor := eventually_mtTypeILongCoefficientPolylogFactor_le_rpow
    C w (show 0 < epsilon / 100 by linarith)
  obtain ⟨T₀, hfactorT₀⟩ := Filter.eventually_atTop.1 hfactor
  have hheight : ∀ᶠ X : ℝ in atTop, T₀ ≤ X ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (show 0 < (1 / 4 : ℝ) by norm_num)).eventually_ge_atTop T₀
  refine ⟨C₀, D, hC₀, hD, ?_⟩
  filter_upwards [hsource, hheight] with X hsourceX hheightX
  intro alpha T a A N N' halpha halpha2 hXT hTX hpoint hA hAT hN hNN' hN'le
  dsimp only
  have hbase := hsourceX alpha T C w a A N N' halpha halpha2 hXT hTX
    hpoint hA hAT hN hNN' hN'le
  dsimp only at hbase
  have hfactorT : mtTypeILongCoefficientPolylogFactor C w T ≤ T ^ (epsilon / 100) :=
    hfactorT₀ T (hheightX.trans hXT)
  by_cases hNT : (N : ℝ) ≤ T
  · have hT : (1 : ℝ) ≤ T := by
      calc
        (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        _ ≤ T := hNT
    calc
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound
            C₀ (epsilon / 100) C epsilon alpha w A
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r := by
        simpa only [hNT, if_true] using hbase
      _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
          mtTypeIPrimeHeathBrownCanonicalLongPowerBlockMomentBound
            C₀ (epsilon / 100) (epsilon / 100) epsilon alpha A
              (mtTypeIPrimeScale X alpha)
              (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N T r :=
        Finset.sum_le_sum fun r _ =>
          mtTypeIPrimeHeathBrownCanonicalDivisorBlockMomentBound_le_longPower
            hC₀.le hT hfactorT r
      _ = _ := by rw [if_pos hNT]
  · simpa only [hNT, if_false] using hbase

end

end RHTower.Sieve
