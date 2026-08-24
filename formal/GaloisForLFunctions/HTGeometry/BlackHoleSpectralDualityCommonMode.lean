import Mathlib.Analysis.Complex.Trigonometric

/-!
# Black-hole spectral duality selects mirror-common modes

For thermal correlators dual to four-dimensional black-hole perturbations, Darboux/electric--
magnetic duality mixes longitudinal and transverse quasinormal spectra.  Grozdanov--Vrbica define

`S(ω) = (1 + ω / ω_*) * ∏ₙ (1 - ω / ω⁺ₙ) * (1 + ω / ω⁻ₙ)`

and derive the exact odd-part law

`S(ω) - S(-ω) = 2 * I * λ * sinh(β * ω / 2)`.

This module formalizes the sharp zero-selection consequence of that gravity-specific law.  If a
mode is dark in both mirror orientations, it is a Matsubara mode and in particular has purely
imaginary frequency.  Equivalently, every off-axis zero in one orientation must mix into a
nonzero response in the other orientation.

This conclusion does not follow from generic KMS, CCR, passivity, group, inverse, or Krein laws.
No claim is made here that a Riemann-Xi zero is a mirror-common black-hole mode; deriving that
source-faithful realization is a separate physical problem.

Physics provenance: S. Grozdanov and M. Vrbica, *Duality Constraints on Thermal Spectra of 3d
Conformal Field Theories and 4d Quasinormal Modes*, arXiv:2406.19790, especially equations (1),
(2), and (8).  The thermal product input is M. Dodelson, C. Iossa, R. Karlsson, and
A. Zhiboedov, *A thermal product formula*, arXiv:2304.12339.
-/

open Complex

namespace GaloisForLFunctions

/-- A zero of complex hyperbolic sine lies on the imaginary axis. -/
lemma re_eq_zero_of_complex_sinh_eq_zero {z : ℂ} (hz : Complex.sinh z = 0) :
    z.re = 0 := by
  have hexp : Complex.exp z = Complex.exp (-z) := by
    have htwo := Complex.two_sinh z
    rw [hz, mul_zero] at htwo
    exact sub_eq_zero.mp htwo.symm
  have hre : z.re = (-z).re :=
    Complex.norm_exp_eq_iff_re_eq.mp (congrArg norm hexp)
  simp only [neg_re] at hre
  linarith

/-- Exact odd-part constraint on the mixed longitudinal/transverse QNM product `S`.

The underlying infinite product and its convergence are upstream analytic data.  This predicate
records only the universal identity selected by four-dimensional black-hole duality. -/
def BlackHoleSpectralDualityOddPart
    (S : ℂ → ℂ) (β : ℝ) (weight : ℂ) : Prop :=
  ∀ ω, S ω - S (-ω) =
    2 * Complex.I * weight * Complex.sinh (((β : ℂ) * ω) / 2)

namespace BlackHoleSpectralDualityOddPart

/-- A mirror-common zero annihilates the exact Matsubara factor. -/
theorem common_zero_sinh_eq_zero
    {S : ℂ → ℂ} {β : ℝ} {weight ω : ℂ}
    (hweight : weight ≠ 0)
    (hdual : BlackHoleSpectralDualityOddPart S β weight)
    (hω : S ω = 0) (hnegω : S (-ω) = 0) :
    Complex.sinh (((β : ℂ) * ω) / 2) = 0 := by
  have h := hdual ω
  rw [hω, hnegω, sub_self] at h
  have hcoeff : 2 * Complex.I * weight ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hweight
  exact (mul_eq_zero.mp h.symm).resolve_left hcoeff

/-- **Black-hole mirror-common-mode selection.**  At nonzero inverse temperature and nonzero
spectral weight, every common zero of the two frequency orientations is purely imaginary. -/
theorem common_zero_re_eq_zero
    {S : ℂ → ℂ} {β : ℝ} {weight ω : ℂ}
    (hβ : β ≠ 0) (hweight : weight ≠ 0)
    (hdual : BlackHoleSpectralDualityOddPart S β weight)
    (hω : S ω = 0) (hnegω : S (-ω) = 0) :
    ω.re = 0 := by
  have hsinh : Complex.sinh (((β : ℂ) * ω) / 2) = 0 :=
    common_zero_sinh_eq_zero hweight hdual hω hnegω
  have hre : (((β : ℂ) * ω) / 2).re = 0 :=
    re_eq_zero_of_complex_sinh_eq_zero hsinh
  norm_num [Complex.div_re, Complex.mul_re] at hre
  exact hre.resolve_left hβ

/-- **Tilted-sector mixing.**  An off-axis zero in one QNM-product orientation cannot remain dark
in the reflected longitudinal/transverse orientation. -/
theorem tilted_zero_forces_mirror_nondegenerate
    {S : ℂ → ℂ} {β : ℝ} {weight ω : ℂ}
    (hβ : β ≠ 0) (hweight : weight ≠ 0)
    (hdual : BlackHoleSpectralDualityOddPart S β weight)
    (htilt : ω.re ≠ 0) (hω : S ω = 0) :
    S (-ω) ≠ 0 := by
  intro hnegω
  exact htilt (common_zero_re_eq_zero hβ hweight hdual hω hnegω)

/-- Reflected form of tilted-sector mixing. -/
theorem tilted_mirror_zero_forces_original_nondegenerate
    {S : ℂ → ℂ} {β : ℝ} {weight ω : ℂ}
    (hβ : β ≠ 0) (hweight : weight ≠ 0)
    (hdual : BlackHoleSpectralDualityOddPart S β weight)
    (htilt : ω.re ≠ 0) (hnegω : S (-ω) = 0) :
    S ω ≠ 0 := by
  intro hω
  exact htilt (common_zero_re_eq_zero hβ hweight hdual hω hnegω)

end BlackHoleSpectralDualityOddPart

end GaloisForLFunctions
