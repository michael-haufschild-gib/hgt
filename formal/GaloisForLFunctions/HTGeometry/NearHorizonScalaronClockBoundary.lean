import GaloisForLFunctions.HTGeometry.KerrNewmanChargedScalarGammaBoundary
import GaloisForLFunctions.HTGeometry.MobiusObservationHypertranscendence

/-!
# Near-horizon scalar-curvature clock boundary

For a neutral massive scalar mode on a finite-temperature `AdS₂` black-hole throat, the
frequency-dependent retarded core is

`Gamma(z + (1 + gap)/2) / Gamma(z + (1 - gap)/2)`,

where `z = -i*omega/(2*pi*T)` and

`gap² = (2*ell + 1)² + 4*radius²*mass²`.

In `f(R) = R + alpha*R²` gravity, the linearized Ricci scalar is the propagating scalaron with
`mass² = 1/(6*alpha)`.  Hence its throat gap obeys

`gap² = (2*ell + 1)² + 2*radius²/(3*alpha)`.

The physical derivation of the scalaron equation, throat reduction, and retarded Green function is
external to Lean.  This file formalizes the resulting exact differential boundary, the discrete
integer-gap resonance equation, preservation under every nondegenerate rational Möbius exterior
matching, and preservation by the observable Wigner--Smith/logarithmic clock.

The source formulas are:

* Y. S. Myung, T. Moon, and E. J. Son, *Stability of f(R) black holes*,
  arXiv:1103.0343, especially the scalaron equations and mass formula;
* T. Faulkner, H. Liu, J. McGreevy, and D. Vegh,
  *Emergent quantum criticality, Fermi surfaces, and AdS2*, arXiv:0907.2694,
  especially the finite-temperature `AdS₂` scalar Green function and matching formula.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Squared effective `AdS₂` gap of a neutral scalar mode after spherical-harmonic reduction. -/
def scalarCurvatureThroatGapSquared
    (ell : ℕ) (radius massSquared : ℂ) : ℂ :=
  (2 * (ell : ℂ) + 1) ^ 2 + 4 * radius ^ 2 * massSquared

/-- Scalaron mass squared in `f(R) = R + alpha*R²`. -/
def starobinskyScalaronMassSquared (alpha : ℂ) : ℂ :=
  1 / (6 * alpha)

/-- Squared scalaron gap on an `AdS₂ × S²` throat of radius `radius`. -/
def starobinskyScalaronThroatGapSquared
    (ell : ℕ) (radius alpha : ℂ) : ℂ :=
  scalarCurvatureThroatGapSquared ell radius
    (starobinskyScalaronMassSquared alpha)

/-- The scalaron squared gap reduces to its explicit `R²`-coupling law. -/
theorem starobinskyScalaronThroatGapSquared_eq
    (ell : ℕ) (radius alpha : ℂ) :
    starobinskyScalaronThroatGapSquared ell radius alpha =
      (2 * (ell : ℂ) + 1) ^ 2 + 2 * radius ^ 2 / (3 * alpha) := by
  unfold starobinskyScalaronThroatGapSquared scalarCurvatureThroatGapSquared
    starobinskyScalaronMassSquared
  ring

/-- Integer-gap resonance equation for the scalaron channel. -/
def IsStarobinskyScalaronGapResonance
    (ell : ℕ) (radius alpha : ℂ) (k : ℤ) : Prop :=
  3 * alpha * ((k : ℂ) ^ 2 - (2 * (ell : ℂ) + 1) ^ 2) =
    2 * radius ^ 2

/-- For nonzero `alpha`, landing on an integer squared gap is exactly the displayed discrete
resonance equation. -/
theorem starobinskyScalaronThroatGapSquared_eq_intSquare_iff_resonance
    (ell : ℕ) (radius alpha : ℂ) (k : ℤ) (halpha : alpha ≠ 0) :
    starobinskyScalaronThroatGapSquared ell radius alpha = (k : ℂ) ^ 2 ↔
      IsStarobinskyScalaronGapResonance ell radius alpha k := by
  rw [starobinskyScalaronThroatGapSquared_eq]
  unfold IsStarobinskyScalaronGapResonance
  constructor <;> intro h
  · field_simp [halpha] at h
    linear_combination -h
  · have hden : (3 : ℂ) * alpha ≠ 0 :=
      mul_ne_zero (by norm_num) halpha
    have hquot :
        2 * radius ^ 2 / (3 * alpha) =
          (k : ℂ) ^ 2 - (2 * (ell : ℂ) + 1) ^ 2 := by
      apply (div_eq_iff hden).2
      simpa [mul_comm] using h.symm
    rw [hquot]
    ring

/-- The lowest kinematic integer `2*ell+1` can never be a scalaron resonance at nonzero throat
radius.  A propagating scalaron therefore cannot masquerade as the massless gap in that channel. -/
theorem not_isStarobinskyScalaronGapResonance_base
    (ell : ℕ) (radius alpha : ℂ) (hradius : radius ≠ 0) :
    ¬ IsStarobinskyScalaronGapResonance ell radius alpha
      (Int.ofNat (2 * ell + 1)) := by
  intro h
  have hcast : ((Int.ofNat (2 * ell + 1) : ℤ) : ℂ) =
      2 * (ell : ℂ) + 1 := by
    norm_num [Int.cast_ofNat]
  rw [IsStarobinskyScalaronGapResonance, hcast, sub_self, mul_zero] at h
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hradius)) h.symm

/-- Normalized finite-temperature scalaron throat response, parameterized by its effective gap. -/
def scalaronThroatGammaResponseMero (gap : ℂ) : meroField Set.univ :=
  kerrNewmanChargedScalarGammaResponseMero gap

/-- Exact Gamma quotient underlying the scalaron clock response. -/
theorem scalaronThroatGammaResponseMero_eq_gammaRatio
    (gap : ℂ) :
    scalaronThroatGammaResponseMero gap =
      gammaShiftMero ((1 + gap) / 2) /
        gammaShiftMero ((1 - gap) / 2) :=
  kerrNewmanChargedScalarGammaResponseMero_eq_gammaRatio gap

/-- **Near-horizon scalaron complexity boundary.**  The normalized response is DA exactly on the
integer effective-gap lattice. -/
theorem differentialAlgebraicOver_scalaronThroatGammaResponseMero_iff_integerGap
    (gap : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (scalaronThroatGammaResponseMero gap) ↔
      ∃ k : ℤ, gap = (k : ℂ) :=
  differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap gap

/-- Off the integer effective-gap lattice, the scalaron throat response is HT. -/
theorem hypertranscendentalOver_scalaronThroatGammaResponseMero_iff_nonintegerGap
    (gap : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (scalaronThroatGammaResponseMero gap) ↔
      ∀ k : ℤ, gap ≠ (k : ℂ) :=
  hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap gap

/-- A DA scalaron response whose declared gap satisfies the `R²` throat law forces one of the
discrete coupling-radius resonances. -/
theorem exists_resonance_of_differentialAlgebraicOver_scalaronThroatGammaResponseMero
    (ell : ℕ) (radius alpha gap : ℂ) (halpha : alpha ≠ 0)
    (hgap : gap ^ 2 =
      starobinskyScalaronThroatGapSquared ell radius alpha)
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (scalaronThroatGammaResponseMero gap)) :
    ∃ k : ℤ, IsStarobinskyScalaronGapResonance ell radius alpha k := by
  obtain ⟨k, hk⟩ :=
    (differentialAlgebraicOver_scalaronThroatGammaResponseMero_iff_integerGap
      gap).1 hDA
  refine ⟨k, (starobinskyScalaronThroatGapSquared_eq_intSquare_iff_resonance
    ell radius alpha k halpha).1 ?_⟩
  rw [← hgap, hk]

/-- Absence of every integer resonance forces HT of any gap satisfying the scalaron throat law. -/
theorem hypertranscendentalOver_scalaronThroatGammaResponseMero_of_no_resonance
    (ell : ℕ) (radius alpha gap : ℂ) (halpha : alpha ≠ 0)
    (hgap : gap ^ 2 =
      starobinskyScalaronThroatGapSquared ell radius alpha)
    (hno : ∀ k : ℤ,
      ¬ IsStarobinskyScalaronGapResonance ell radius alpha k) :
    HypertranscendentalOver (RatFunc ℂ)
      (scalaronThroatGammaResponseMero gap) := by
  intro hDA
  obtain ⟨k, hk⟩ :=
    exists_resonance_of_differentialAlgebraicOver_scalaronThroatGammaResponseMero
      ell radius alpha gap halpha hgap hDA
  exact hno k hk

/-- Rational Möbius exterior matching of the normalized throat response.  The coefficients may be
rational functions of normalized frequency; a constant leading-order matching is a special case. -/
def matchedScalaronThroatResponseMero
    (gap : ℂ) (a b c d : RatFunc ℂ) : meroField Set.univ :=
  HTGeometry.mobiusObservable a b c d
    (scalaronThroatGammaResponseMero gap)

/-- Nondegenerate rational exterior matching cannot change the exact DA phase boundary. -/
theorem differentialAlgebraicOver_matchedScalaronThroatResponseMero_iff_integerGap
    (gap : ℂ) (a b c d : RatFunc ℂ) (hdet : a * d - b * c ≠ 0) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (matchedScalaronThroatResponseMero gap a b c d) ↔
      ∃ k : ℤ, gap = (k : ℂ) := by
  rw [matchedScalaronThroatResponseMero,
    HTGeometry.differentialAlgebraicOver_mobiusObservable_iff
      (scalaronThroatGammaResponseMero gap) a b c d hdet,
    differentialAlgebraicOver_scalaronThroatGammaResponseMero_iff_integerGap]

/-- Nondegenerate rational exterior matching cannot erase the off-lattice HT phase. -/
theorem hypertranscendentalOver_matchedScalaronThroatResponseMero_iff_nonintegerGap
    (gap : ℂ) (a b c d : RatFunc ℂ) (hdet : a * d - b * c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
        (matchedScalaronThroatResponseMero gap a b c d) ↔
      ∀ k : ℤ, gap ≠ (k : ℂ) := by
  rw [matchedScalaronThroatResponseMero,
    HTGeometry.hypertranscendentalOver_mobiusObservable_iff
      (scalaronThroatGammaResponseMero gap) a b c d hdet,
    hypertranscendentalOver_scalaronThroatGammaResponseMero_iff_nonintegerGap]

/-- Directly observable Wigner--Smith/logarithmic clock of the matched scalaron response. -/
def matchedScalaronThroatWignerSmithLogClockMero
    (gap : ℂ) (a b c d : RatFunc ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock
    (matchedScalaronThroatResponseMero gap a b c d)

/-- The measured logarithmic delay has the same exact integer-gap DA/HT boundary. -/
theorem hypertranscendentalOver_matchedScalaronThroatWignerSmithLogClockMero_iff_nonintegerGap
    (gap : ℂ) (a b c d : RatFunc ℂ) (hdet : a * d - b * c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
        (matchedScalaronThroatWignerSmithLogClockMero gap a b c d) ↔
      ∀ k : ℤ, gap ≠ (k : ℂ) := by
  rw [matchedScalaronThroatWignerSmithLogClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff,
    hypertranscendentalOver_matchedScalaronThroatResponseMero_iff_nonintegerGap
      gap a b c d hdet]

end

end GaloisForLFunctions
