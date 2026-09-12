import GaloisForLFunctions.RHTower.MobiusThetaRawSourceModulation
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology

/-!
# Complete raw reflection current in the canonical cofinal readout

Reflection of the original translated packet at label `n` supplies the existing mate gain
at degree `n^m`. The complete admitted modulation current agrees with the sum of the existing
cofinal-relative readouts of the original prime cycle, with every arithmetic coefficient retained.
The Tate quotient stage is independent of the arithmetic label and native dilation depth.

These readouts have varying degree `n^m`. Their discrepancy from a fixed-degree readout is
retained explicitly. No fixed Gamma/BV agreement or boundary annihilation is asserted.
-/

set_option autoImplicit false

open Complex Real MeasureTheory ArithmeticFunction LSeries
open scoped Moebius LSeries.notation

noncomputable section
namespace RHTower

/-- The raw reflection phase is the native power-degree Deninger mate gain. -/
theorem mobiusThetaRawReflectionPhase_eq_mateGain (n m : ℕ) (v : ℂ) :
    Complex.exp (-I * (star v - v) * ((m : ℝ) * Real.log n : ℝ)) =
      (deningerHalfDensityMateGain (n ^ m) (mobiusThetaCenteredParameter v) : ℂ) := by
  rw [deningerHalfDensityMateGain, Nat.cast_pow, Real.log_pow, Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;> simp [mobiusThetaCenteredParameter] <;> ring

/-- Reflection retains the original coefficient and multiplies it by the actual mate gain. -/
theorem mobiusThetaPrimeRawAmplitude_star (n m : ℕ) (v : ℂ) :
    mobiusThetaPrimeRawAmplitude n m (mobiusThetaCenteredParameter (star v)) =
      (deningerHalfDensityMateGain (n ^ m) (mobiusThetaCenteredParameter v) : ℂ) *
        mobiusThetaPrimeRawAmplitude n m (mobiusThetaCenteredParameter v) := by
  unfold mobiusThetaPrimeRawAmplitude
  rw [← LSeries_term_halfDilation_mul_exp_neg_I_mul_log,
    ← LSeries_term_halfDilation_mul_exp_neg_I_mul_log,
    ← mobiusThetaRawReflectionPhase_eq_mateGain]
  have he : Complex.exp (-I * star v * ((m : ℝ) * Real.log n : ℝ)) =
      Complex.exp (-I * (star v - v) * ((m : ℝ) * Real.log n : ℝ)) *
        Complex.exp (-I * v * ((m : ℝ) * Real.log n : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

private theorem summable_rawAmplitude {p m : ℕ} (hm : m ≠ 0) {v : ℂ}
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    Summable (fun j : ℕ =>
      mobiusThetaPrimeRawAmplitude (p + j) m (mobiusThetaCenteredParameter v)) := by
  have hs : LSeriesSummable (↗(μ : ArithmeticFunction ℤ))
      ((m : ℂ) * mobiusThetaCenteredParameter v) :=
    LSeriesSummable_moebius_iff.mpr (one_lt_natCast_mul_re hm hv)
  unfold LSeriesSummable at hs
  simpa only [mobiusThetaPrimeRawAmplitude, Nat.add_comm] using
    (_root_.summable_nat_add_iff p).2 hs

/-- Existing canonical cofinal-relative readout of an actual prime cycle weighted by one
raw coefficient. The reader degree `d` and Tate stage `r` remain separate. -/
def mobiusThetaRawCofinalReadout
    (p : Nat.Primes) (k m r d : ℕ) (v : ℂ) (j : ℕ) : ℂ :=
  tateClockCofinalRelativeH1Equiv r
    (ccmMobiusThetaCofinalSourceHomologyLanding d k r
      (mobiusThetaCenteredParameter v) (star v)
      (mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter v) •
        ccmRationalAdelicOrdinaryPrimeCycleAtom p))

private theorem cofinalReadout_eq (p : Nat.Primes) (k m r d : ℕ) (v : ℂ) (j : ℕ) :
    mobiusThetaRawCofinalReadout p k m r d v j =
      ((deningerHalfDensityMateGain d (mobiusThetaCenteredParameter v) : ℂ) - 1) *
        mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter v) *
          iteratedDeriv k XiC (star v) := by
  rw [mobiusThetaRawCofinalReadout, ccmMobiusThetaCofinalSourceHomologyLanding_readout]
  simp only [map_smul, smul_eq_mul,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, mul_one]
  ring

/-- The native-degree cofinal readout equals the literal reflected coefficient difference. -/
theorem mobiusThetaRawCofinalReadout_nativeDegree_eq
    (p : Nat.Primes) (k m r : ℕ) (v : ℂ) (j : ℕ) :
    mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j =
      (mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter (star v)) -
        mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter v)) *
          iteratedDeriv k XiC (star v) := by
  rw [cofinalReadout_eq, mobiusThetaPrimeRawAmplitude_star]
  ring

/-- Absolute admission and exact sum of every native-degree cofinal readout. -/
theorem mobiusThetaRawCofinalReadout_nativeDegree_data
    (p : Nat.Primes) (k r : ℕ) {m : ℕ} (hm : m ≠ 0) {v : ℂ}
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re)
    (hr : 1 / (m : ℝ) < (mobiusThetaCenteredParameter (star v)).re) :
    Summable (fun j : ℕ =>
      ‖mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j‖) ∧
    (∑' j : ℕ, mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j) =
      (mobiusThetaRawResidualMultiplier p m (star v) - mobiusThetaRawResidualMultiplier p m v) *
        iteratedDeriv k XiC (star v) := by
  have hs := summable_rawAmplitude (p := (p : ℕ)) hm hv
  have ht := summable_rawAmplitude (p := (p : ℕ)) hm hr
  simp_rw [mobiusThetaRawCofinalReadout_nativeDegree_eq]
  refine ⟨((ht.sub hs).mul_right _).norm, ?_⟩
  rw [tsum_mul_right, ht.tsum_sub hs]
  rfl

/-- The complete admitted raw reflection current agrees with the existing degree-labelled
cofinal readouts. This theorem does not replace those degrees by the fixed BV degree. -/
theorem mobiusThetaRawReflectionCurrent_eq_tsum_cofinalReadout
    (p : Nat.Primes) (k r : ℕ) {m : ℕ} (hm : m ≠ 0) {v : ℂ}
    (hstrip : |(star v).im| < 1)
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re)
    (hr : 1 / (m : ℝ) < (mobiusThetaCenteredParameter (star v)).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawSourceModulationCommutator k p m (star v - v) x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaRawSourceModulationCommutator k p m (star v - v) x) =
      ∑' j : ℕ, mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j := by
  have he : v + (star v - v) = star v := by ring
  have hi := mobiusThetaRawSourceModulationCommutator_fourierLaplace_data p.prop.pos hm k
    (v := v) (delta := star v - v) (by rw [he]; exact hstrip) hv (by rw [he]; exact hr)
  rw [he] at hi
  exact ⟨hi.1, hi.2.trans (mobiusThetaRawCofinalReadout_nativeDegree_data p k r hm hv hr).2.symm⟩

/-- Exact complete correction when comparing native degree `n^m` to one fixed degree `d`.
Absolute admission is retained; no cancellation of this correction is asserted. -/
theorem mobiusThetaRawCofinalReadout_fixedDegreeCorrection_data
    (p : Nat.Primes) (k r d : ℕ) {m : ℕ} (hm : m ≠ 0) {v : ℂ}
    (hv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re)
    (hr : 1 / (m : ℝ) < (mobiusThetaCenteredParameter (star v)).re) :
    Summable (fun j : ℕ => ‖
      mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j -
        mobiusThetaRawCofinalReadout p k m r d v j‖) ∧
    (∑' j : ℕ, (mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j -
      mobiusThetaRawCofinalReadout p k m r d v j)) =
      (mobiusThetaRawResidualMultiplier p m (star v) -
        (deningerHalfDensityMateGain d (mobiusThetaCenteredParameter v) : ℂ) *
          mobiusThetaRawResidualMultiplier p m v) * iteratedDeriv k XiC (star v) := by
  have hs := summable_rawAmplitude (p := (p : ℕ)) hm hv
  have ht := summable_rawAmplitude (p := (p : ℕ)) hm hr
  have he (j : ℕ) :
      mobiusThetaRawCofinalReadout p k m r (((p : ℕ) + j) ^ m) v j -
        mobiusThetaRawCofinalReadout p k m r d v j =
      (mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter (star v)) -
        (deningerHalfDensityMateGain d (mobiusThetaCenteredParameter v) : ℂ) *
          mobiusThetaPrimeRawAmplitude ((p : ℕ) + j) m (mobiusThetaCenteredParameter v)) *
        iteratedDeriv k XiC (star v) := by
    rw [mobiusThetaRawCofinalReadout_nativeDegree_eq, cofinalReadout_eq]
    ring
  simp_rw [he]
  refine ⟨((ht.sub (hs.mul_left _)).mul_right _).norm, ?_⟩
  rw [tsum_mul_right, ht.tsum_sub (hs.mul_left _), tsum_mul_left]
  rfl

end RHTower
