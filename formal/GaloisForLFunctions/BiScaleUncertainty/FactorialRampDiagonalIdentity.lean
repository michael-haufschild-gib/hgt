import GaloisForLFunctions.BiScaleUncertainty.ClampedPrimeLogResummation
import GaloisForLFunctions.BiScaleUncertainty.FactorialBiNullPolarSign
import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilGram

/-! Exact prime-free physical expression for the actual pure ramp diagonal.
The logarithmic field is a finite explicit clamp sum; the signed pole is
computed from the two concrete source moments. No diagonal sign is assumed. -/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
set_option autoImplicit false

theorem factorialRampSource_autocorr_tail (n : ℕ) {x : ℝ}
    (hx : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ x) :
    autocorr (factorialRampSource n) x = 0 := by
  unfold autocorr
  have hz : (fun u => factorialRampSource n u*factorialRampSource n (u+x)) = 0 := by
    funext u
    change _ = (0 : ℝ)
    rcases le_total u 0 with hu | hu
    · rw [factorialRampSource_zero_of_nonpos n hu, zero_mul]
    · rw [factorialRampSource_tail n (by linarith), mul_zero]
  rw [hz, integral_zero]

/-- The whole quadratic prime sum, not merely an individual translated field. -/
theorem sum_primeWeight_autocorr_factorialRamp_eq_log (n : ℕ) {K : ℕ}
    (hK : 4*(n+1) ≤ K+2) :
    (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*autocorr (factorialRampSource n) (Real.log m)) =
      ∫ u, factorialRampSource n u*factorialRampLogField n u := by
  let f := factorialRampSource n
  have ha : Integrable (fun u => f u*atomicSource f K u) :=
    (f.continuous.mul (atomicSource f K).continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hp : Integrable (fun u => f u*polarSource f K u) :=
    (f.continuous.mul (polarSource f K).continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hs := integral_source_signedSource f K
  change (∫ u, f u*(atomicSource f K u-polarSource f K u)) = _ at hs
  simp_rw [mul_sub] at hs
  rw [integral_sub ha hp, integral_mul_polarSource] at hs
  have he : (∫ u, f u*atomicSource f K u) =
      ∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*autocorr f (Real.log m) := by
    change (∫ u, f u*atomicSource f K u)-
      (∫ x in Icc 0 (cutoff K), polarDensity x*autocorr f x) =
      (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*autocorr f (Real.log m))-
      (∫ x in Icc 0 (cutoff K), polarDensity x*autocorr f x) at hs
    linarith only [hs]
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    rcases le_total 0 u with hu | hu
    · rw [atomicSource_factorialRamp_eq_log n hu hK]
    · change factorialRampSource n u*_ = _
      rw [factorialRampSource_zero_of_nonpos n hu, zero_mul, zero_mul]

/-- Exact elimination of the literal infinite prime sequence for this autocorrelation. -/
theorem tsum_primeTerm_autocorr_factorialRamp_eq_log (n : ℕ) :
    (∑' m : ℕ, primeTerm (autocorr (factorialRampSource n)) m) =
      ∫ u, factorialRampSource n u*factorialRampLogField n u := by
  let K := 10*(n+1)
  have hc : Real.log (4*((n+1 : ℕ) : ℝ)+1) ≤ cutoff K := by
    have hh := factorial_packet_cutoff (by omega : 1 ≤ n+1) (K := K) (by rfl)
    have hw := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
    linarith
  have ht : ∀ x, cutoff K ≤ x → autocorr (factorialRampSource n) x = 0 :=
    fun x hx => factorialRampSource_autocorr_tail n (hc.trans hx)
  have he := fullPairing_eq_pairing_of_tail (autocorr (factorialRampSource n)) K ht
  have hi := integral_halfLine_eq_of_tail
    (fun x => polarDensity x*autocorr (factorialRampSource n) x) K
    (fun x hx => by rw [ht x hx, mul_zero])
  rw [fullPairing, pairing, hi] at he
  have hsum := sum_primeWeight_autocorr_factorialRamp_eq_log n (K := K) (by dsimp [K]; omega)
  linarith only [he, hsum]

/-- Prime and polar parts together, with the full signed polar correction. -/
theorem fullPairing_autocorr_factorialRamp_eq_log (n : ℕ) :
    fullPairing (autocorr (factorialRampSource n)) =
      (∫ u, factorialRampSource n u*factorialRampLogField n u)+
      ((1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        chebyshevBiNullProducer (n+1))/(n+1 : ℕ) := by
  rw [fullPairing, tsum_primeTerm_autocorr_factorialRamp_eq_log,
    integral_polar_autocorr_factorialRamp_eq]
  ring

theorem factorialSourceLeft_autocorr_eq_ramp (n : ℕ) (x : ℝ) :
    autocorr (factorialSourceLeft n) x = autocorr (factorialRampSource n) x := by
  calc
    _ = autocorr (factorialRampSource n) (-x) := by
      unfold autocorr
      rw [← integral_neg_eq_self
        (fun u => factorialRampSource n u*factorialRampSource n (u+ -x)) volume]
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change sourceFactorialRamp (n+1) (-u)*sourceFactorialRamp (n+1) (-(u+x)) =
          sourceFactorialRamp (n+1) (-u)*sourceFactorialRamp (n+1) (-u+ -x)
        congr 2
        ring
    _ = _ := autocorr_neg _ _

/-- The remaining Gram diagonal is an explicit archimedean/logarithmic inequality.
All von Mangoldt atoms have been evaluated, and the pole lowers the diagonal. -/
theorem factorialSpanWeil_ramp_eq_log (n : ℕ) :
    factorialSpanWeil n 1 0 =
      Zeta23.EF.gammaBracket 0*autocorr (factorialRampSource n) 0+
      biScaleLevyEnergy (factorialRampSource n)-
      2*(∫ u, factorialRampSource n u*factorialRampLogField n u)-
      2*(((1+sourceFactorialCollar (n+1)/2)*harmonicCorrection (n+1)*
        chebyshevBiNullProducer (n+1))/(n+1 : ℕ)) := by
  have hf : autocorr (factorialSourceLeft n) = autocorr (factorialRampSource n) :=
    funext (factorialSourceLeft_autocorr_eq_ramp n)
  have hJ : biScaleLevyEnergy (factorialSourceLeft n) = biScaleLevyEnergy (factorialRampSource n) := by
    unfold biScaleLevyEnergy
    rw [hf]
  rw [factorialSpanWeil_eq_complete]
  simp only [one_smul, zero_smul, add_zero]
  rw [hf, hJ, fullPairing_autocorr_factorialRamp_eq_log]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
