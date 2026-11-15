import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentComponents

/-!
# An explicit integral level for every paired moment system

Restrict the functional `c ↦ t * ∑ i, c i` to any relation space.
Every coordinate unit relation then has level `t`. Consequently every
nonzero parameter gives an integral paired quotient, over every field.
At zero, the exact component count is `2^s`, where `s` is the number of
coordinate unit vectors in the relation space; elsewhere it is one.

In particular `t = 1` supplies an explicit integral level without any
genericity argument or infinite-field assumption.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- The affine level realized by the constant neutral point with value `t`. -/
def uniformMomentLevel (L : Submodule K (ι → K)) (t : K) : L →ₗ[K] K :=
  ((aeval (fun _ : ι => t) : MvPolynomial ι K →ₐ[K] K).toLinearMap.comp
    (momentLinearForm K)).comp L.subtype

/-- The uniform level is the sum of the relation coefficients, scaled by the parameter. -/
theorem uniformMomentLevel_apply (L : Submodule K (ι → K)) (t : K) (c : L) :
    uniformMomentLevel K L t c = (∑ i, c.1 i) * t := by
  change eval (fun _ : ι => t) (momentLinearForm K c.1) = _
  rw [eval_momentLinearForm, Finset.sum_mul]

/-- Every coordinate unit relation has the same level, namely the parameter. -/
theorem uniformMomentLevel_basis (L : Submodule K (ι → K)) (t : K) (i : ι)
    (h : Pi.basisFun K ι i ∈ L) :
    uniformMomentLevel K L t ⟨Pi.basisFun K ι i, h⟩ = t := by
  change aeval (fun _ : ι => t) (momentLinearForm K (Pi.basisFun K ι i)) = t
  simp only [momentLinearForm, Basis.constr_basis, aeval_X]

/-- A coordinate can vanish only at the zero parameter, and only if its unit vector is a relation. -/
theorem uniformMomentIdeal_X_mem_iff (L : Submodule K (ι → K)) (t : K) (i : ι) :
    (X i : MvPolynomial ι K) ∈ affineMomentIdeal K L (uniformMomentLevel K L t) ↔
      Pi.basisFun K ι i ∈ L ∧ t = 0 := by
  rw [affineMomentIdeal_X_mem_iff]
  simp only [uniformMomentLevel_basis, exists_prop]

/-- All nonzero parameters are integral; zero is integral exactly when no unit coordinate is a relation. -/
theorem uniformPairedQuotient_isDomain_iff (L : Submodule K (ι → K)) (t : K) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸
      (affineMomentIdeal K L (uniformMomentLevel K L t)).map (invariantSubstitution K)) ↔
      t ≠ 0 ∨ ∀ i, Pi.basisFun K ι i ∉ L := by
  rw [affinePairedQuotient_isDomain_iff]
  simp only [uniformMomentLevel_basis]
  constructor
  · intro h
    by_cases ht : t = 0
    · exact Or.inr (fun i hi => h i hi ht)
    · exact Or.inl ht
  · rintro (ht | h) i hi
    · exact ht
    · exact False.elim (h i hi)

/-- The constant neutral point `1` gives an integral level for every relation space. -/
theorem unitLevelPairedQuotient_isDomain (L : Submodule K (ι → K)) :
    IsDomain (MvPolynomial (ι ⊕ ι) K ⧸
      (affineMomentIdeal K L (uniformMomentLevel K L 1)).map (invariantSubstitution K)) :=
  (uniformPairedQuotient_isDomain_iff K L 1).mpr (Or.inl one_ne_zero)

/-- Every paired linear moment system admits an integral affine level over its original field. -/
theorem exists_domain_affinePairedLevel (L : Submodule K (ι → K)) :
    ∃ ℓ : L →ₗ[K] K, IsDomain (MvPolynomial (ι ⊕ ι) K ⧸
      (affineMomentIdeal K L ℓ).map (invariantSubstitution K)) :=
  ⟨uniformMomentLevel K L 1, unitLevelPairedQuotient_isDomain K L⟩

/-- Uniform-level branch coordinates are precisely unit relations at zero parameter. -/
def uniformZeroCoordinateEquiv (L : Submodule K (ι → K)) (t : K) :
    AffineMomentZeroCoordinate K L (uniformMomentLevel K L t) ≃
      {i : ι // Pi.basisFun K ι i ∈ L ∧ t = 0} :=
  Equiv.subtypeEquivRight (fun _ => by simp only [uniformMomentLevel_basis, exists_prop])

/-- Exact component count throughout the uniform level family. -/
theorem card_uniformPairedIrreducibleComponents (L : Submodule K (ι → K)) (t : K) :
    Nat.card (irreducibleComponents (PrimeSpectrum.zeroLocus
      (((affineMomentIdeal K L (uniformMomentLevel K L t)).map (invariantSubstitution K)) :
        Set (MvPolynomial (ι ⊕ ι) K)))) =
      if t = 0 then 2 ^ Fintype.card {i : ι // Pi.basisFun K ι i ∈ L} else 1 := by
  rw [card_affinePairedIrreducibleComponents,
    Fintype.card_congr (uniformZeroCoordinateEquiv K L t)]
  by_cases ht : t = 0 <;> simp [ht]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.uniformPairedQuotient_isDomain_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.unitLevelPairedQuotient_isDomain
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_domain_affinePairedLevel
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_uniformPairedIrreducibleComponents
