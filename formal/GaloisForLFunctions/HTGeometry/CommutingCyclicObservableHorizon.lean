import GaloisForLFunctions.HTGeometry.CommutingCyclicHorizonLinearity
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The full algebraic-independence horizon of a graded cyclic observable

Let `I` be a homogeneous annihilator in the commutative law algebra and let `x` be a degree-one law
form.  The cyclic state orbit is the family of classes of `1, x, x², ...` modulo `I`.  Its canonical
images in the symmetric observable algebra are algebraically independent exactly when `x` is not
in `rad(I)`.

Consequently the full algebraic-dependence horizon of the canonical graded cyclic observable jet
sequence is precisely the linear radical pullback already identified by the finite-rule theorem.
This file does not yet identify the sequence with iterates of constructed commuting derivations;
that differential-domain realization is a separate theorem surface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

variable {K : Type u} {ι : Type v} [Field K]

/-- The `n`-th cyclic power state modulo the annihilator ideal. -/
def cyclicPowerState (I : Ideal (MvPolynomial ι K))
    (x : MvPolynomial ι K) (n : ℕ) : MvPolynomial ι K ⧸ I :=
  Ideal.Quotient.mk I (x ^ n)

/-- A finite scalar relation among quotient power states vanishes exactly when the corresponding
polynomial relation belongs to the annihilator ideal. -/
theorem cyclicPower_linearCombination_eq_zero_iff
    (I : Ideal (MvPolynomial ι K)) (x : MvPolynomial ι K)
    (s : Finset ℕ) (a : ℕ → K) :
    (∑ n ∈ s, a n • cyclicPowerState I x n) = 0 ↔
      (∑ n ∈ s, C (a n) * x ^ n) ∈ I := by
  change (∑ n ∈ s, a n • (Ideal.Quotient.mkₐ K I) (x ^ n)) = 0 ↔ _
  simp_rw [← map_smul]
  rw [← map_sum, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- Finite cyclic relations are exactly failures of linear independence of the complete quotient
power orbit. -/
theorem hasFiniteCyclicLinearRelation_iff_not_linearIndependent
    (I : Ideal (MvPolynomial ι K)) (x : MvPolynomial ι K) :
    HasFiniteCyclicLinearRelation I x ↔
      ¬ LinearIndependent K (cyclicPowerState I x) := by
  rw [not_linearIndependent_iff]
  constructor
  · rintro ⟨s, a, hnonzero, hrel⟩
    exact ⟨s, a, (cyclicPower_linearCombination_eq_zero_iff I x s a).2 hrel, hnonzero⟩
  · rintro ⟨s, a, hrel, hnonzero⟩
    exact ⟨s, a, hnonzero, (cyclicPower_linearCombination_eq_zero_iff I x s a).1 hrel⟩

/-- In a homogeneous cyclic law module, the complete power orbit is linearly independent exactly
off the radical horizon. -/
theorem homogeneous_cyclicPowerState_linearIndependent_iff
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (x : MvPolynomial ι K) (hx : x.IsHomogeneous 1) :
    LinearIndependent K (cyclicPowerState I x) ↔ x ∉ I.radical := by
  rw [← not_iff_not, not_not, ← hasFiniteCyclicLinearRelation_iff_not_linearIndependent,
    homogeneous_finiteCyclicRelation_iff_radical I hI x hx]

/-- The canonical observable jet attached to the cyclic power state in its symmetric algebra. -/
def cyclicSymmetricObservableJet (I : Ideal (MvPolynomial ι K))
    (x : MvPolynomial ι K) (n : ℕ) :
    SymmetricAlgebra K (MvPolynomial ι K ⧸ I) :=
  SymmetricAlgebra.ι K (MvPolynomial ι K ⧸ I) (cyclicPowerState I x n)

/-- **Complete graded cyclic observable theorem.**  The entire observable jet sequence is
algebraically independent exactly off the radical of the homogeneous annihilator. -/
theorem homogeneous_cyclicSymmetricObservableJet_algebraicIndependent_iff
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (x : MvPolynomial ι K) (hx : x.IsHomogeneous 1) :
    AlgebraicIndependent K (cyclicSymmetricObservableJet I x) ↔ x ∉ I.radical := by
  change AlgebraicIndependent K
      (fun n => SymmetricAlgebra.ι K (MvPolynomial ι K ⧸ I) (cyclicPowerState I x n)) ↔ _
  rw [symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent,
    homogeneous_cyclicPowerState_linearIndependent_iff I hI x hx]

/-- The canonical cyclic observable jets in one direction of law space. -/
def commutingCyclicObservableJet [Fintype ι]
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    ℕ → SymmetricAlgebra K (MvPolynomial ι K ⧸ I) :=
  cyclicSymmetricObservableJet I (lawLinearForm c)

/-- **Full graded cyclic horizon classification.**  For a homogeneous annihilator, algebraic
dependence of the complete canonical observable jet occurs exactly on the linear radical horizon. -/
theorem not_algebraicIndependent_commutingCyclicObservableJet_iff
    [Fintype ι] (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (c : ι → K) :
    (¬ AlgebraicIndependent K (commutingCyclicObservableJet I c)) ↔
      c ∈ commutingCyclicNilpotenceHorizon I := by
  rw [show AlgebraicIndependent K (commutingCyclicObservableJet I c) ↔
      lawLinearForm c ∉ I.radical by
    exact homogeneous_cyclicSymmetricObservableJet_algebraicIndependent_iff
      I hI (lawLinearForm c) (lawLinearForm_isHomogeneous c)]
  change (¬ lawLinearForm c ∉ I.radical) ↔ lawLinearForm c ∈ I.radical
  simp

end

end GaloisForLFunctions.HTGeometry
