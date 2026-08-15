import GaloisForLFunctions.SelbergClass.MeromorphicTensor
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Reciprocal-Gamma clearing for multiple standard twists

Kaczorowski--Perelli's meromorphic continuation is gamma-cleared: on every
spectral fibre the quotient by `Gamma (L s)` is entire for an affine complex
functional `L`.  The correct global presentation of the original tensor is
therefore `G / (1 / Gamma ∘ L)`, not an unevaluable abstract fraction-field
element.

This module supplies that denominator and the associated concrete
`MeromorphicTensorPresentation`.  It does not assume or assert the published
continuation theorem: a later proof must construct its entire numerator `G`.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

/-- The reciprocal Gamma function remains entire after precomposition by a
complex affine functional on `ℂ^N`. -/
theorem reciprocalGamma_comp_affine_entire
    (N : ℕ) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) :
    AnalyticOnNhd ℂ (fun z : Fin N → ℂ => (Complex.Gamma (L z + b))⁻¹) Set.univ := by
  have hGamma : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) Set.univ :=
    Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ
  have hAffine : AnalyticOnNhd ℂ (fun z : Fin N → ℂ => L z + b) Set.univ := by
    intro z _
    exact (L.analyticAt z).add analyticAt_const
  change AnalyticOnNhd ℂ
    ((fun s : ℂ => (Complex.Gamma s)⁻¹) ∘ fun z : Fin N → ℂ => L z + b) Set.univ
  exact hGamma.comp hAffine (by intro z _; exact Set.mem_univ z)

/-- The entire reciprocal-Gamma denominator for a gamma-cleared tensor. -/
noncomputable def reciprocalGammaAffineEntire
    (N : ℕ) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) :
    entireSubring (Fin N → ℂ) :=
  ⟨fun z => (Complex.Gamma (L z + b))⁻¹,
    reciprocalGamma_comp_affine_entire N L b⟩

/-- Exact zero locus of the reciprocal-Gamma affine denominator.  These are the
polar hyperplanes of a gamma-cleared presentation. -/
theorem reciprocalGammaAffineEntire_eval_eq_zero_iff
    (N : ℕ) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (s : Fin N → ℂ) :
    ((reciprocalGammaAffineEntire N L b : entireSubring (Fin N → ℂ)) :
      (Fin N → ℂ) → ℂ) s = 0 ↔ ∃ m : ℕ, L s + b = -(m : ℂ) := by
  change (Complex.Gamma (L s + b))⁻¹ = 0 ↔ ∃ m : ℕ, L s + b = -(m : ℂ)
  rw [inv_eq_zero, Complex.Gamma_eq_zero_iff]

/-- A simple geometric certificate that an affine reciprocal-Gamma denominator
is not the zero entire function: its affine argument attains `1`. -/
theorem reciprocalGammaAffineEntire_ne_zero_of_exists_eq_one
    {N : ℕ} (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hpoint : ∃ z : Fin N → ℂ, L z + b = 1) :
    reciprocalGammaAffineEntire N L b ≠ 0 := by
  intro hzero
  obtain ⟨z, hz⟩ := hpoint
  have hz0 := congrArg (fun f : entireSubring (Fin N → ℂ) =>
    (f : (Fin N → ℂ) → ℂ) z) hzero
  simp [reciprocalGammaAffineEntire, hz, Complex.Gamma_one] at hz0

/-- The explicit meromorphic tensor represented by a gamma-cleared entire
numerator.  The `hden` proof is data, not an analytic-continuation assumption;
`reciprocalGammaAffineEntire_ne_zero_of_exists_eq_one` supplies it whenever
the affine argument reaches `1`. -/
noncomputable def gammaClearedPresentation {N : ℕ}
    (G : entireSubring (Fin N → ℂ)) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hden : reciprocalGammaAffineEntire N L b ≠ 0) :
    MeromorphicTensorPresentation N where
  numerator := G
  denominator := reciprocalGammaAffineEntire N L b
  denominator_ne_zero := hden

/-- Function-level form of a gamma-cleared presentation. -/
theorem gammaClearedPresentation_value {N : ℕ}
    (G : entireSubring (Fin N → ℂ)) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hden : reciprocalGammaAffineEntire N L b ≠ 0) (s : Fin N → ℂ) :
    (gammaClearedPresentation G L b hden).value s =
      (G : (Fin N → ℂ) → ℂ) s / (Complex.Gamma (L s + b))⁻¹ := rfl

/-- The regular locus of a gamma-cleared presentation is precisely the
complement of the affine Gamma-polar hyperplanes. -/
theorem gammaClearedPresentation_regularSet {N : ℕ}
    (G : entireSubring (Fin N → ℂ)) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hden : reciprocalGammaAffineEntire N L b ≠ 0) :
    (gammaClearedPresentation G L b hden).regularSet =
      {s | ∀ m : ℕ, L s + b ≠ -(m : ℂ)} := by
  ext s
  change (Complex.Gamma (L s + b))⁻¹ ≠ 0 ↔ ∀ m : ℕ, L s + b ≠ -(m : ℂ)
  constructor
  · intro hs m hm
    apply hs
    exact (reciprocalGammaAffineEntire_eval_eq_zero_iff N L b s).mpr ⟨m, hm⟩
  · intro hs hzero
    obtain ⟨m, hm⟩ := (reciprocalGammaAffineEntire_eval_eq_zero_iff N L b s).mp hzero
    exact hs m hm

end GaloisForLFunctions.SelbergClass
