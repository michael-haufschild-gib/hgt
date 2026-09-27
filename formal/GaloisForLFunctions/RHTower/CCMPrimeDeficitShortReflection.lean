import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorReflection
import GaloisForLFunctions.RHTower.LogarithmicWeightedSawtoothConvolution
import GaloisForLFunctions.RHTower.LogarithmicMobiusSawtoothPrefix

/-!
# The actual short prime-deficit reconstruction as a signed pairing

The complete source main terms, the logarithmic sawtooth pairing, and
the decaying-force error are retained together. The pairing uses the
literal Möbius coefficients at the square-root cutoff. Its bound is not
assumed by any theorem here.
-/

noncomputable section
open MeasureTheory ArithmeticFunction
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitDivisorReflectionMain (t : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant + 1) * logarithmicDilationSum (fun u => Real.exp u - 1) t -
    Real.log (2 * Real.pi) / 2 * logarithmicDilationSum (fun u => u) t +
      Real.exp t * ccmPrimeDeficitDivisorMainCoefficient t - ccmPrimeDeficitDilationRemainder t / 2

def ccmPrimeDeficitShortReflectedMainWork (T : ℝ) : ℝ :=
  2 * ccmPrimeDeficitShortMainWork T -
    ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        (moebius a : ℝ) * (moebius b : ℝ) *
          ccmPrimeDeficitDivisorReflectionMain (T - Real.log (a * b : ℕ))

def ccmPrimeDeficitShortReciprocalErrorWork (T : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
    ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      (moebius a : ℝ) * (moebius b : ℝ) *
        ccmPrimeDeficitReciprocalErrorWork (T - Real.log (a * b : ℕ))

def ccmPrimeDeficitShortReciprocalPairing (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T,
    logarithmicFiniteEntryProfile (fun n => (moebius n : ℝ) * (T / 2 - 1 - Real.log n))
      ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth s *
        logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth (T - s)

theorem ccmPrimeDeficitDivisorSource_eq_reflection {t : ℝ} (ht : 0 ≤ t) :
    ccmPrimeDeficitDivisorSource t = ccmPrimeDeficitDivisorReflectionMain t -
      (t - 2) / 2 * logarithmicReciprocalSawtoothCorrelation t -
        ccmPrimeDeficitReciprocalErrorWork t := by
  have hs := ccmPrimeDeficitDivisorSource_centered_eq_dilationRemainder t
  rw [ccmPrimeDeficitDilationRemainder_dilation_reflection ht] at hs
  unfold ccmPrimeDeficitDivisorReflectionMain
  linarith only [hs]

theorem ccmPrimeDeficitShortReciprocalPairing_eq_square (T : ℝ) :
    ccmPrimeDeficitShortReciprocalPairing T =
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          (moebius a : ℝ) * (moebius b : ℝ) *
            ((T - Real.log (a * b : ℕ) - 2) / 2 *
              logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))) := by
  unfold ccmPrimeDeficitShortReciprocalPairing
  simp_rw [logarithmicShortMobiusInverse_eq_finiteEntryProfile]
  exact (weighted_reciprocalSawtooth_square_eq_profile_integral _ T).symm

theorem ccmPrimeDeficitShortQuadraticWork_eq_reflected_pairing {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitShortQuadraticWork T = ccmPrimeDeficitShortReflectedMainWork T +
      ccmPrimeDeficitShortReciprocalPairing T + ccmPrimeDeficitShortReciprocalErrorWork T := by
  rw [ccmPrimeDeficitShortQuadraticWork_eq_divisorSource hT,
    ccmPrimeDeficitShortReciprocalPairing_eq_square]
  unfold ccmPrimeDeficitShortReflectedMainWork ccmPrimeDeficitShortReciprocalErrorWork
  have hs : (∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        (moebius a : ℝ) * (moebius b : ℝ) * ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))) =
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          (moebius a : ℝ) * (moebius b : ℝ) *
            (ccmPrimeDeficitDivisorReflectionMain (T - Real.log (a * b : ℕ)) -
              (T - Real.log (a * b : ℕ) - 2) / 2 *
                logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ)) -
                  ccmPrimeDeficitReciprocalErrorWork (T - Real.log (a * b : ℕ))) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
    have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
    have haT : Real.log a ≤ T / 2 := (Real.log_le_iff_le_exp hap).mpr
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp ha).2)
    have hbT : Real.log b ≤ T / 2 := (Real.log_le_iff_le_exp hbp).mpr
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hb).2)
    have htime : 0 ≤ T - Real.log (a * b : ℕ) := by
      rw [Nat.cast_mul, Real.log_mul hap.ne' hbp.ne']
      linarith only [haT, hbT]
    rw [ccmPrimeDeficitDivisorSource_eq_reflection htime]
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem ccmLogChebyshevDeficitPrimitive_reflected_pairing_conservation
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T = ccmPrimeDeficitShortReflectedMainWork T +
      ccmPrimeDeficitShortReciprocalPairing T + ccmPrimeDeficitShortReciprocalErrorWork T +
        2 * logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T := by
  have h := ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork hT
  rw [ccmPrimeDeficitShortQuadraticWork_eq_reflected_pairing hT] at h
  linarith only [h]

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_reflected_pairing_le
    {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T -
      (ccmPrimeDeficitShortReflectedMainWork T + ccmPrimeDeficitShortReciprocalPairing T +
        ccmPrimeDeficitShortReciprocalErrorWork T)| ≤ 7 * Real.exp (T / 2) := by
  rw [← ccmPrimeDeficitShortQuadraticWork_eq_reflected_pairing hT]
  exact abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le hT

end RHTower
