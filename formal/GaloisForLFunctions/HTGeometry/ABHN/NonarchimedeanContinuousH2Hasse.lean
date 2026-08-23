import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldContinuousCyclicGaloisH2TorsionInvariant

/-!
# Hasse principles for continuous unramified local H²

A finite unramified root lift is packaged as intrinsic data, hiding the dependent local-ring,
valuation-ring, fraction-field, and finite-dimensional instance chain.  Its canonical finite-level
`RatModInt` invariant is a complete invariant of continuous degree-two unit Galois cohomology.
The corresponding complex character is equally faithful and lies in the cyclotomic sector whose
order is the residue degree.

This is local cohomological class-field infrastructure.  It does not assert the still-missing
comparison between continuous `H²` and the Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

universe u

/-- Intrinsic data of one finite unramified root lift over a nonarchimedean local field. -/
structure NonarchimedeanFiniteUnramifiedRootLift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] where
  polynomial : Polynomial 𝒪[K]
  residuePolynomial : Polynomial 𝓀[K]
  monic : polynomial.Monic
  residueMonic : residuePolynomial.Monic
  reduction_eq : polynomial.map (Ideal.Quotient.mk 𝓂[K]) = residuePolynomial
  residueIrreducible : Irreducible residuePolynomial

namespace NonarchimedeanFiniteUnramifiedRootLift

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Residue degree of an unramified root lift is nonzero. -/
theorem natDegree_ne_zero (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    D.polynomial.natDegree ≠ 0 := by
  intro hzero
  apply nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
    D.residuePolynomial D.reduction_eq D.residueIrreducible
  rw [Polynomial.degree_eq_natDegree D.monic.ne_zero, hzero]
  rfl

/-- Canonical finite-level local invariant attached to packaged unramified lift data. -/
noncomputable def continuousH2NTorsionInvariant
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
    K D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible

/-- Local Hasse congruence: torsion invariant values determine continuous `H²` classes. -/
theorem continuousH2_congr_hasse_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.continuousH2NTorsionInvariant
    ∀ x y, x = y ↔ e x = e y := by
  dsimp only
  intro x y
  exact D.continuousH2NTorsionInvariant.injective.eq_iff.symm

/-- Local Hasse vanishing: zero invariant is exactly zero continuous `H²` class. -/
theorem continuousH2_eq_zero_hasse_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.continuousH2NTorsionInvariant
    ∀ x, x = 0 ↔ e x = 0 := by
  dsimp only
  intro x
  constructor
  · rintro rfl
    exact map_zero _
  · intro hx
    apply D.continuousH2NTorsionInvariant.injective
    simpa using hx

/-- One complex cyclotomic phase is already a faithful local `H²` observable. -/
theorem continuousH2_phase_congr_hasse_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.continuousH2NTorsionInvariant
    ∀ x y, x = y ↔
      ratModIntNTorsionStdAddChar D.polynomial.natDegree D.natDegree_ne_zero (e x) =
        ratModIntNTorsionStdAddChar D.polynomial.natDegree D.natDegree_ne_zero (e y) := by
  dsimp only
  intro x y
  constructor
  · rintro rfl
    rfl
  · intro h
    apply D.continuousH2NTorsionInvariant.injective
    exact ratModIntNTorsionStdAddChar_injective D.polynomial.natDegree
      D.natDegree_ne_zero h

/-- Phase-one test is exactly vanishing of the continuous local `H²` class. -/
theorem continuousH2_phase_eq_one_hasse_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.continuousH2NTorsionInvariant
    ∀ x, x = 0 ↔
      ratModIntNTorsionStdAddChar D.polynomial.natDegree D.natDegree_ne_zero (e x) = 1 := by
  dsimp only
  intro x
  rw [D.continuousH2_eq_zero_hasse_iff]
  constructor
  · intro hx
    rw [hx]
    exact (ratModIntNTorsionStdAddChar D.polynomial.natDegree
      D.natDegree_ne_zero).map_zero_eq_one
  · intro hx
    apply ratModIntNTorsionStdAddChar_injective D.polynomial.natDegree D.natDegree_ne_zero
    simpa using hx

/-- Every local `H²` phase lies in the residue-degree cyclotomic sector. -/
theorem continuousH2_phase_pow_natDegree_eq_one
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.continuousH2NTorsionInvariant
    ∀ x, (ratModIntNTorsionStdAddChar D.polynomial.natDegree
      D.natDegree_ne_zero (e x)) ^ D.polynomial.natDegree = 1 := by
  dsimp only
  intro x
  exact ratModIntNTorsionStdAddChar_pow_eq_one D.polynomial.natDegree
    D.natDegree_ne_zero _

end NonarchimedeanFiniteUnramifiedRootLift

end

end GaloisForLFunctions.HTGeometry.ABHN
