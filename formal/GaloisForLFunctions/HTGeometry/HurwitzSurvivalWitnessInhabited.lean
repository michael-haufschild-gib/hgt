import GaloisForLFunctions.HTGeometry.ProjectiveConstraintTopologicalCapacityPhase

/-!
# The Hurwitz and modular survival-witness classes are inhabited

`HurwitzProjectiveSurvivalWitness` and `ModularProjectiveSurvivalWitness` package the classical
geometric inputs of the sharp projective phase law.  Their `commonPullback` and `irreducible`
fields are arbitrary predicates, so both classes are inhabited outright: the exact storage law and
the unbounded-degree condition can be met by an explicit integer family.

Two consequences, both recorded here as theorems rather than commentary.

* Every phase theorem quantified over such a witness is non-vacuous.
* The witness carries no geometric information about actual correspondence surfaces: the
  substantive content of the card — torsion-free finite-index subgroups of `Δ(2,3,7)` of unbounded
  index, and the identification of their quotients with the indexed family — is *not* expressed by
  these structures and remains to be formalized.  The arithmetic that is expressed,
  `hurwitzTriangle_projectiveCapacity_exact`, is unconditional already.
-/

namespace GaloisForLFunctions.HTGeometry

/-- An explicit integer family satisfying the compact Hurwitz storage law at unbounded degree. -/
def natHurwitzProjectiveSurvivalWitness : HurwitzProjectiveSurvivalWitness ℕ where
  degree i := 42 * (2 * ((i : ℤ) + 2) - 2)
  genus i := (i : ℤ) + 2
  commonPullback _ := True
  irreducible _ := True
  exactStorage _ := rfl
  survives _ := ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    refine ⟨(bound.toNat + 1), ?_⟩
    have h : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    push_cast
    linarith

theorem nonempty_hurwitzProjectiveSurvivalWitness :
    Nonempty (HurwitzProjectiveSurvivalWitness ℕ) :=
  ⟨natHurwitzProjectiveSurvivalWitness⟩

/-- An explicit integer family satisfying the noncompact modular storage law at unbounded
degree. -/
def natModularProjectiveSurvivalWitness : ModularProjectiveSurvivalWitness ℕ where
  degree i := 6 * (2 * ((i : ℤ) + 2) - 2)
  genus i := (i : ℤ) + 2
  cuspCard _ := 0
  commonPullback _ := True
  irreducible _ := True
  exactStorage _ := by ring
  survives _ := ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    refine ⟨(bound.toNat + 1), ?_⟩
    have h : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    push_cast
    linarith

theorem nonempty_modularProjectiveSurvivalWitness :
    Nonempty (ModularProjectiveSurvivalWitness ℕ) :=
  ⟨natModularProjectiveSurvivalWitness⟩

end GaloisForLFunctions.HTGeometry
