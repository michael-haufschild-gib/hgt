import GaloisForLFunctions.RHTower.PolarPrimeChannelContinuation
import GaloisForLFunctions.RHTower.CCMInverseTiltedCriticalMellinFactorization

/-!
# Critical-Mellin four-coordinate collapse universality law

Four source constructions produced separately named critical-Mellin coordinates: the convergent
complex Laplace colligation, the polar-prime complex carrier, the canonical continued defect, and
the zeta-pole-filled inverse-tilted defect.  Their statements reveal that these are not merely
analogous.  The polar-prime carrier and continued defect are globally identical, and all four
coordinates coincide on the right half-plane.  Consequently every finite complex CCM incidence
can be written directly using the same regularized germ whose extended holomorphy classifies RH.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The polar-prime complex carrier is globally the canonical continued critical-Mellin defect;
the right-half-plane assumption previously attached to their source constructions is unnecessary
for this value identity. -/
theorem criticalMellinDefectChannelComplex_eq_continuedCriticalMellinDefect
    (u : ℂ) :
    criticalMellinDefectChannelComplex u = continuedCriticalMellinDefect u := by
  rw [criticalMellinDefectChannelComplex, vonMangoldtPrimeChannelComplex,
    continuedCriticalMellinDefect, logDeriv_apply]
  ring

/-- **Four-coordinate collapse law.**  On `Re u > 0`, the Laplace, polar-carrier, continued, and
pole-filled inverse-tilted critical-Mellin coordinates all have exactly the same value. -/
theorem criticalMellin_fourCoordinateCollapse {u : ℂ} (hu : 0 < u.re) :
    criticalMellinDefectLaplaceChannelComplex u =
      criticalMellinDefectChannelComplex u ∧
    criticalMellinDefectChannelComplex u = continuedCriticalMellinDefect u ∧
    continuedCriticalMellinDefect u = regularizedCriticalMellinDefect u := by
  have hLaplace := criticalMellinDefectLaplaceChannelComplex_eq_continued hu
  have hCarrier :=
    criticalMellinDefectChannelComplex_eq_continuedCriticalMellinDefect u
  have hRegularized := regularizedCriticalMellinDefect_eq_continued hu
  exact ⟨hLaplace.trans hCarrier.symm, hCarrier, hRegularized.symm⟩

/-- The finite critical-Mellin Gram written in the pole-filled inverse-tilted coordinate. -/
def regularizedCriticalMellinRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => regularizedCriticalMellinDefect (w i + star (w j))

/-- Every positive-node CCM critical-Mellin Gram is exactly the Gram of the RH-classifying
regularized germ. -/
theorem criticalMellinDefectRightHalfPlaneGram_eq_regularized
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    criticalMellinDefectRightHalfPlaneGram w =
      regularizedCriticalMellinRightHalfPlaneGram w := by
  ext i j
  have huij : 0 < (w i + star (w j)).re := by
    change 0 < (w i + (starRingEnd ℂ) (w j)).re
    rw [Complex.add_re, Complex.conj_re]
    linarith [hw i, hw j]
  have h := criticalMellin_fourCoordinateCollapse huij
  exact h.1.trans (h.2.1.trans h.2.2)

/-- **Regularized finite CCM incidence law.**  The universal Cauchy Gram decomposes into its
prime and shifted-polar Grams plus the same pole-filled critical-Mellin germ used by the global RH
holomorphy criterion. -/
theorem cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_regularizedCriticalMellin
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    cauchyRightHalfPlaneGram w = vonMangoldtPrimeRightHalfPlaneGram w -
      shiftedPolarRightHalfPlaneGram w +
        regularizedCriticalMellinRightHalfPlaneGram w := by
  rw [cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect w hw,
    criticalMellinDefectRightHalfPlaneGram_eq_regularized w hw]

end

end RHTower
