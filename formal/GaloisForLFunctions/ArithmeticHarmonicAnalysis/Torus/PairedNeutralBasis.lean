import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedWeightQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A relative monomial basis for paired polynomial rings

Under `hᵢ ↦ zᵢwᵢ`, the paired polynomial ring is free over the neutral
polynomial ring. Its basis consists of the minimal monomials indexed by
integral weights. Each polynomial has finitely many neutral coefficients,
and the existing weight extraction maps recover them exactly.

This assembles Brown's weight normal forms into a basis for the whole ring.
For every neutral ideal, membership in its extension is equivalent to
membership of every extracted coefficient in the original ideal.

The neutral scalar action is scoped to `PairedNeutral`; ordinary field
scalars retain their existing meaning.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

namespace PairedNeutral
/-- Neutral variables act by multiplication by the paired products. -/
scoped instance algebra : Algebra (MvPolynomial ι K) (MvPolynomial (ι ⊕ ι) K) :=
  (invariantSubstitution K).toAlgebra
end PairedNeutral

open scoped PairedNeutral

omit [Fintype ι] in
theorem pairedNeutral_smul (f : MvPolynomial ι K) (P : MvPolynomial (ι ⊕ ι) K) :
    f • P = invariantSubstitution K f * P := rfl

/-- The monomial with exactly the exponents forced by an integral weight. -/
def minimalPairedMonomial (q : ι → ℤ) : MvPolynomial (ι ⊕ ι) K :=
  monomial (normalWeightExponent q 0) 1

/-- Assemble finitely many neutral coefficients against their minimal weight monomials. -/
def pairedNeutralAssembly :
    ((ι → ℤ) →₀ MvPolynomial ι K) →ₗ[MvPolynomial ι K] MvPolynomial (ι ⊕ ι) K :=
  Finsupp.linearCombination (MvPolynomial ι K) (minimalPairedMonomial K)

/-- Extraction is the coordinate functional dual to the minimal monomial family. -/
theorem pairedWeightExtraction_smul_minimal (q r : ι → ℤ) (f : MvPolynomial ι K) :
    pairedWeightExtraction K q (f • minimalPairedMonomial K r) = if r = q then f else 0 := by
  rw [pairedNeutral_smul, pairedWeightExtraction_invariant_mul]
  have hz : neutralExponent (normalWeightExponent r 0) = 0 := neutralExponent_normal r 0
  simp only [minimalPairedMonomial, pairedWeightExtraction_monomial, pairedWeight_normal,
    hz]
  split_ifs <;> simp

theorem pairedWeightExtraction_assembly (q : ι → ℤ) (c : (ι → ℤ) →₀ MvPolynomial ι K) :
    pairedWeightExtraction K q (pairedNeutralAssembly K c) = c q := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Finsupp.add_apply]
  | single r f =>
    rw [pairedNeutralAssembly, Finsupp.linearCombination_single, pairedWeightExtraction_smul_minimal]
    simp only [Finsupp.single_apply]

theorem pairedNeutralAssembly_injective : Function.Injective (pairedNeutralAssembly (ι := ι) K) := by
  intro c d h
  apply Finsupp.ext
  intro q
  have he := congrArg (pairedWeightExtraction K q) h
  simpa only [pairedWeightExtraction_assembly] using he

/-- Every ordinary monomial has a unique weight and neutral remainder. -/
theorem pairedNeutralAssembly_surjective : Function.Surjective (pairedNeutralAssembly (ι := ι) K) := by
  intro P
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨c, rfl⟩ := hP
    obtain ⟨d, rfl⟩ := hQ
    exact ⟨c + d, map_add _ c d⟩
  | monomial d a =>
    refine ⟨Finsupp.single (pairedWeight d) (monomial (neutralExponent d) a), ?_⟩
    rw [pairedNeutralAssembly, Finsupp.linearCombination_single, pairedNeutral_smul,
      minimalPairedMonomial, mul_comm, invariantSubstitution_monomial,
      ← pairedWeight_monomial_factor]
    have he := congrArg Subtype.val
      ((weightExponentEquiv (pairedWeight d)).apply_symm_apply ⟨d, rfl⟩)
    exact congrArg (fun e => monomial e a) he

/-- All paired polynomials, coordinatized over the neutral ring by finitely supported weights. -/
def pairedNeutralEquiv :
    MvPolynomial (ι ⊕ ι) K ≃ₗ[MvPolynomial ι K] ((ι → ℤ) →₀ MvPolynomial ι K) :=
  (LinearEquiv.ofBijective (pairedNeutralAssembly K)
    ⟨pairedNeutralAssembly_injective K, pairedNeutralAssembly_surjective K⟩).symm

theorem pairedNeutralEquiv_apply (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    pairedNeutralEquiv K P q = pairedWeightExtraction K q P := by
  have h := pairedWeightExtraction_assembly K q (pairedNeutralEquiv K P)
  have he : pairedNeutralAssembly K (pairedNeutralEquiv K P) = P :=
    (pairedNeutralEquiv K).symm_apply_apply P
  rw [he] at h
  exact h.symm

/-- Minimal monomials form a basis over the ring of neutral variables. -/
def pairedNeutralBasis : Basis (ι → ℤ) (MvPolynomial ι K) (MvPolynomial (ι ⊕ ι) K) :=
  Basis.ofRepr (pairedNeutralEquiv K)

theorem pairedNeutralBasis_apply (q : ι → ℤ) :
    pairedNeutralBasis K q = minimalPairedMonomial K q := by
  change pairedNeutralAssembly K (Finsupp.single q 1) = _
  simp [pairedNeutralAssembly]

/-- The paired polynomial ring is free as a module over the neutral polynomial ring. -/
theorem pairedNeutral_free : Module.Free (MvPolynomial ι K) (MvPolynomial (ι ⊕ ι) K) :=
  Module.Free.of_basis (pairedNeutralBasis K)

theorem pairedNeutralBasis_repr (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    (pairedNeutralBasis K).repr P q = pairedWeightExtraction K q P :=
  pairedNeutralEquiv_apply K P q

theorem minimalPairedMonomial_zero : minimalPairedMonomial (ι := ι) K 0 = 1 := by
  have hz : normalWeightExponent (0 : ι → ℤ) 0 = 0 := by
    ext (i | i) <;> simp
  rw [minimalPairedMonomial, hz]
  rfl

/-- The finite weight expansion reconstructs the original polynomial exactly. -/
theorem pairedNeutralExpansion (P : MvPolynomial (ι ⊕ ι) K) :
    P = (pairedNeutralEquiv K P).sum (fun q f => f • minimalPairedMonomial K q) := by
  exact ((pairedNeutralEquiv K).symm_apply_apply P).symm

/-- Arbitrary neutral relations act independently on all weight coefficients. -/
theorem mem_extended_ideal_iff_extractions (J : Ideal (MvPolynomial ι K))
    (P : MvPolynomial (ι ⊕ ι) K) :
    P ∈ J.map (invariantSubstitution K) ↔ ∀ q, pairedWeightExtraction K q P ∈ J := by
  constructor
  · intro h q
    exact pairedWeightExtraction_mem K q J h
  · intro h
    rw [pairedNeutralExpansion K P]
    apply (J.map (invariantSubstitution K)).sum_mem
    intro q _
    change pairedNeutralEquiv K P q • minimalPairedMonomial K q ∈ _
    rw [pairedNeutral_smul]
    apply (J.map (invariantSubstitution K)).mul_mem_right
    apply Ideal.mem_map_of_mem
    rw [pairedNeutralEquiv_apply]
    exact h q

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralBasis
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralEquiv_apply
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutral_free
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.mem_extended_ideal_iff_extractions
