import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPolarizedGreenIdentity

/-!
# Single-projective-response no-go for BM second harmonics

The outer endpoint of the polarized radial Green current is the antisymmetric determinant of
forbidden/source and decaying/response coefficients. If its two legs use retarded and advanced
projective responses, this determinant factors through their difference. If one projective
response is used on both legs, it vanishes.

The exact BM `--` connection coefficients at conjugate momentum are conjugates of the `++`
coefficients. Their same-branch polarized concomitant is therefore identically zero. A nonzero
Peierls carrier needs distinct augmented retarded and advanced responses, not one projective ratio.
-/

open Complex

namespace RHTower

noncomputable section

/-- Decaying `--` connection coefficient is conjugate decaying `++` coefficient. -/
theorem d4BMCausalDecayingBoundaryCoefficient_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalDecayingBoundaryCoefficient
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalDecayingBoundaryCoefficient
          (d4BMCausalPlusPlusFrequency n chi) chi) := by
  have hgamma :
      (starRingEnd ℂ) (Complex.Gamma (-1 / 2 : ℂ)) =
        Complex.Gamma (-1 / 2 : ℂ) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_neg, map_div₀, map_one, map_ofNat]
  rw [d4BMCausalDecayingBoundaryCoefficient,
    d4BMCausalDecayingBoundaryCoefficient,
    d4BMCausalRadialC_minusMinus_schwarz,
    d4BMCausalHypergeometricA_minusMinus_schwarz,
    d4BMCausalHypergeometricB_minusMinus_schwarz]
  simp only [map_mul, map_div₀, Complex.Gamma_conj, hgamma]
  ring

/-- Forbidden/source `--` coefficient is conjugate forbidden/source `++` coefficient. -/
theorem d4BMCausalForbiddenBoundaryCoefficient_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalForbiddenBoundaryCoefficient
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalForbiddenBoundaryCoefficient
          (d4BMCausalPlusPlusFrequency n chi) chi) := by
  have hgamma :
      (starRingEnd ℂ) (Complex.Gamma (1 / 2 : ℂ)) =
        Complex.Gamma (1 / 2 : ℂ) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_div₀, map_one, map_ofNat]
  rw [d4BMCausalForbiddenBoundaryCoefficient,
    d4BMCausalForbiddenBoundaryCoefficient,
    d4BMCausalRadialC_minusMinus_schwarz,
    d4BMCausalRadialA_minusMinus_schwarz,
    d4BMCausalRadialB_minusMinus_schwarz]
  simp only [map_mul, map_div₀, Complex.Gamma_conj, hgamma]
  ring

/-- Outer-boundary polarized concomitant of two source/response coefficient vectors. -/
def d4BMAdSBoundaryPolarizedConcomitant
    (sourcePP responsePP sourceMM responseMM : ℂ) : ℂ :=
  ((starRingEnd ℂ) responseMM * sourcePP -
    (starRingEnd ℂ) sourceMM * responsePP) / 2

/-- Boundary concomitant factors through advanced-minus-retarded projective response. -/
theorem d4BMAdSBoundaryPolarizedConcomitant_eq_responseJump
    (sourcePP responsePP sourceMM responseMM retardedResponse advancedResponse : ℂ)
    (hpp : responsePP = retardedResponse * sourcePP)
    (hmm : responseMM =
      (starRingEnd ℂ) advancedResponse * sourceMM) :
    d4BMAdSBoundaryPolarizedConcomitant
        sourcePP responsePP sourceMM responseMM =
      (starRingEnd ℂ) sourceMM * sourcePP *
        (advancedResponse - retardedResponse) / 2 := by
  rw [d4BMAdSBoundaryPolarizedConcomitant, hpp, hmm]
  simp only [map_mul, Complex.conj_conj]
  ring

/-- One projective response used on both causal legs has zero polarized concomitant. -/
theorem d4BMAdSBoundaryPolarizedConcomitant_eq_zero_of_sameResponse
    (sourcePP responsePP sourceMM responseMM response : ℂ)
    (hpp : responsePP = response * sourcePP)
    (hmm : responseMM = (starRingEnd ℂ) response * sourceMM) :
    d4BMAdSBoundaryPolarizedConcomitant
        sourcePP responsePP sourceMM responseMM = 0 := by
  rw [d4BMAdSBoundaryPolarizedConcomitant_eq_responseJump
    sourcePP responsePP sourceMM responseMM response response hpp hmm]
  simp

/-- Exact same-branch BM `++` and Schwarz `--` connection data have zero boundary current. -/
theorem d4BMCausalSecondHarmonicSameBranchBoundaryConcomitant_eq_zero
    (n : ℕ) (chi : ℂ) :
    d4BMAdSBoundaryPolarizedConcomitant
      (d4BMCausalForbiddenBoundaryCoefficient
        (d4BMCausalPlusPlusFrequency n chi) chi)
      (d4BMCausalDecayingBoundaryCoefficient
        (d4BMCausalPlusPlusFrequency n chi) chi)
      (d4BMCausalForbiddenBoundaryCoefficient
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi))
      (d4BMCausalDecayingBoundaryCoefficient
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi)) = 0 := by
  rw [d4BMAdSBoundaryPolarizedConcomitant,
    d4BMCausalDecayingBoundaryCoefficient_minusMinus_schwarz,
    d4BMCausalForbiddenBoundaryCoefficient_minusMinus_schwarz,
    Complex.conj_conj, Complex.conj_conj]
  ring

end

end RHTower
