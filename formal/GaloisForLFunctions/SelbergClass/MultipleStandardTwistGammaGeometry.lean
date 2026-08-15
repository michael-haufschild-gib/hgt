import GaloisForLFunctions.SelbergClass.MultipleStandardTwistGammaClearing
import GaloisForLFunctions.SelbergClass.MeromorphicTensorAgreement

/-!
# Affine Gamma-hyperplane geometry for multiple standard twists

This module proves only geometry of displayed reciprocal-Gamma denominator. It
supplies neither continuation theorem nor residue claim.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

/-- A nonzero complex linear functional attains every prescribed affine value. -/
theorem exists_affine_eq_of_ne_zero {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b w : ℂ) (hL : L ≠ 0) :
    ∃ z : Fin N → ℂ, L z + b = w := by
  have hx : ∃ x : Fin N → ℂ, L x ≠ 0 := by
    by_contra h
    push Not at h
    apply hL
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hx
  refine ⟨((w - b) / L x) • x, ?_⟩
  rw [L.map_smul]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Specialization of `exists_affine_eq_of_ne_zero` at Gamma-normalizing value `1`. -/
theorem exists_affine_eq_one_of_ne_zero {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (hL : L ≠ 0) :
    ∃ z : Fin N → ℂ, L z + b = 1 :=
  exists_affine_eq_of_ne_zero L b 1 hL

/-- A nonzero affine functional makes its reciprocal-Gamma entire denominator
nonzero as an entire function. -/
theorem reciprocalGammaAffineEntire_ne_zero_of_linear_ne_zero {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (hL : L ≠ 0) :
    reciprocalGammaAffineEntire N L b ≠ 0 :=
  reciprocalGammaAffineEntire_ne_zero_of_exists_eq_one L b
    (exists_affine_eq_one_of_ne_zero L b hL)

/-- `m`-th affine hyperplane where reciprocal-Gamma denominator vanishes. -/
def gammaCandidateHyperplane {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (m : ℕ) : Set (Fin N → ℂ) :=
  {s | L s + b = -(m : ℂ)}

/-- Union of affine Gamma hyperplanes. It is a candidate polar set of a
displayed quotient, not assertion of an uncancelled pole. -/
def gammaCandidatePolarSet {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) : Set (Fin N → ℂ) :=
  {s | ∃ m : ℕ, s ∈ gammaCandidateHyperplane L b m}

/-- Membership in candidate polar set is explicit Gamma-hyperplane condition. -/
theorem mem_gammaCandidatePolarSet_iff {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (s : Fin N → ℂ) :
    s ∈ gammaCandidatePolarSet L b ↔ ∃ m : ℕ, L s + b = -(m : ℂ) := by
  rfl

/-- Candidate polar set is union of named affine Gamma hyperplanes. -/
theorem gammaCandidatePolarSet_eq_iUnion {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) :
    gammaCandidatePolarSet L b = ⋃ m : ℕ, gammaCandidateHyperplane L b m := by
  ext s
  simp only [gammaCandidatePolarSet, Set.mem_setOf_eq, Set.mem_iUnion]

/-- Every Gamma candidate hyperplane is nonempty if defining linear part is nonzero. -/
theorem gammaCandidateHyperplane_nonempty {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) (m : ℕ) (hL : L ≠ 0) :
    (gammaCandidateHyperplane L b m).Nonempty := by
  obtain ⟨z, hz⟩ := exists_affine_eq_of_ne_zero L b (-(m : ℂ)) hL
  exact ⟨z, hz⟩

/-- Zero set of affine reciprocal-Gamma entire function is exactly union of
candidate Gamma hyperplanes. -/
theorem reciprocalGammaAffineEntire_zeroSet_eq_gammaCandidatePolarSet {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) :
    {s | ((reciprocalGammaAffineEntire N L b : entireSubring (Fin N → ℂ)) :
      (Fin N → ℂ) → ℂ) s = 0} = gammaCandidatePolarSet L b := by
  ext s
  change (Complex.Gamma (L s + b))⁻¹ = 0 ↔ s ∈ gammaCandidatePolarSet L b
  rw [mem_gammaCandidatePolarSet_iff]
  exact reciprocalGammaAffineEntire_eval_eq_zero_iff N L b s

/-- Nonzero locus of reciprocal-Gamma denominator is complement of candidate
Gamma-polar union. -/
theorem reciprocalGammaAffineEntire_nonzeroSet_eq_compl_gammaCandidatePolarSet {N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ) :
    {s | ((reciprocalGammaAffineEntire N L b : entireSubring (Fin N → ℂ)) :
      (Fin N → ℂ) → ℂ) s ≠ 0} = (gammaCandidatePolarSet L b)ᶜ := by
  ext s
  change (Complex.Gamma (L s + b))⁻¹ ≠ 0 ↔ s ∉ gammaCandidatePolarSet L b
  rw [mem_gammaCandidatePolarSet_iff]
  exact not_congr (reciprocalGammaAffineEntire_eval_eq_zero_iff N L b s)

/-- In gamma-cleared quotient presentation, displayed candidate polar set is
exactly Gamma-hyperplane union. -/
theorem gammaClearedPresentation_candidatePolarSet {N : ℕ}
    (G : entireSubring (Fin N → ℂ)) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hden : reciprocalGammaAffineEntire N L b ≠ 0) :
    (gammaClearedPresentation G L b hden).candidatePolarSet = gammaCandidatePolarSet L b := by
  ext s
  rw [MeromorphicTensorPresentation.mem_candidatePolarSet_iff]
  change (Complex.Gamma (L s + b))⁻¹ = 0 ↔ s ∈ gammaCandidatePolarSet L b
  rw [mem_gammaCandidatePolarSet_iff]
  exact reciprocalGammaAffineEntire_eval_eq_zero_iff N L b s

/-- Displayed regular locus of gamma-cleared presentation is complement of
Gamma-hyperplane union. -/
theorem gammaClearedPresentation_regularSet_eq_compl_gammaCandidatePolarSet {N : ℕ}
    (G : entireSubring (Fin N → ℂ)) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (hden : reciprocalGammaAffineEntire N L b ≠ 0) :
    (gammaClearedPresentation G L b hden).regularSet = (gammaCandidatePolarSet L b)ᶜ := by
  rw [MeromorphicTensorPresentation.regularSet_eq_compl_candidatePolarSet,
    gammaClearedPresentation_candidatePolarSet]

end GaloisForLFunctions.SelbergClass
