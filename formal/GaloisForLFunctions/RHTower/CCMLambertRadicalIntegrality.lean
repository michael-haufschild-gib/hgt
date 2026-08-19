import GaloisForLFunctions.RHTower.CCMCentralBinomialIntegrality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic

/-!
# Algebraic-integrality gate for CCM Lambert coefficients

For the rank-one Lambert coefficient in CCM equation (53), the radical part is
`sqrt (sigma(ell,i) * sigma(ell,j))`.  Lemma 5.5 proves both sigma factors are
integers.  This file closes the resulting algebraic-integrality statement: any
chosen complex square root of that product is integral over `Z`.

This is deliberately the algebraic-integer gate, not yet the paper's sharper
claim that the radical belongs to the cyclotomic integer ring.  The latter
requires a formal cyclotomic containment theorem, which is a distinct step.
-/

namespace RHTower

noncomputable section

/-- CCM equation (51), as an actual rational number. -/
def ccmFiniteSemilocalSigma (ell m : ℕ) : ℚ :=
  (Nat.centralBinom ell : ℚ) * (Nat.centralBinom m : ℚ) *
    ccmFiniteSemilocalHarmonic ell m ^ 2

/-- The radicand occurring in CCM equation (53). -/
def ccmLambertRadicand (ell i j : ℕ) : ℚ :=
  ccmFiniteSemilocalSigma ell i * ccmFiniteSemilocalSigma ell j

/-- Lemma 5.5(iii) for the named sigma coefficient. -/
theorem ccmFiniteSemilocalSigma_integral (ell m : ℕ) :
    CCMRationalIntegral (ccmFiniteSemilocalSigma ell m) := by
  simpa [ccmFiniteSemilocalSigma] using
    ccmFiniteSemilocalHarmonic_sigma_integral ell m

/-- Every complex square root of a CCM Lambert radicand is an algebraic
integer.  This is the coefficient-wise integral gate needed before the
cyclotomic localization in CCM Theorem 5.6(i). -/
theorem ccmLambertRadical_isIntegral (ell i j : ℕ) (z : ℂ)
    (hz : z ^ 2 = (ccmLambertRadicand ell i j : ℂ)) :
    IsIntegral ℤ z := by
  obtain ⟨a, ha⟩ := ccmFiniteSemilocalSigma_integral ell i
  obtain ⟨b, hb⟩ := ccmFiniteSemilocalSigma_integral ell j
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  rw [hz, ccmLambertRadicand, ha, hb]
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (a : ℂ)).mul
    (isIntegral_algebraMap : IsIntegral ℤ (b : ℂ))

end

end RHTower
