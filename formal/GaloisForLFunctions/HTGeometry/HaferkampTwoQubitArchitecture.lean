import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProduct
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarReindex
import GaloisForLFunctions.QECLean.Foundations.Tensor

/-!
# Fixed two-qubit architectures and their Haar-random contraction maps

This is the literal finite-register architecture layer used in
Haferkamp--Faist--Kothakonda--Eisert--Yunger Halpern (2022): each ordered
location addresses two distinct qubits, each local parameter belongs to
`SU(4)`, and the contraction is the time-ordered product of the lifted local
gates.  The gate law is the independent finite product of normalized Haar
measures constructed in `FiniteSpecialUnitaryHaarProduct`.
-/

open Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Split a finite Boolean register into two ordered distinguished qubits and
all remaining coordinates. -/
def splitTwoQubitConfig
    {Q : Type*} [DecidableEq Q] (a b : Q) (hab : a ≠ b) :
    (Q → Bool) ≃
      ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool)) where
  toFun x := ((x a, x b), fun q => x q.1)
  invFun p q :=
    if hqa : q = a then p.1.1
    else if hqb : q = b then p.1.2
    else p.2 ⟨q, hqa, hqb⟩
  left_inv x := by
    funext q
    by_cases hqa : q = a
    · simp [hqa]
    · by_cases hqb : q = b
      · subst q
        simp [hab.symm]
      · simp [hqa, hqb]
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [hab.symm]
    · funext q
      simp [q.property.1, q.property.2]

/-- Forget determinant one, retaining the unitary gate carried by a special
unitary matrix. -/
def specialUnitaryAsUnitary
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (Bool × Bool) ℂ :=
  ⟨U.1, Matrix.specialUnitaryGroup_le_unitaryGroup U.2⟩

/-- Lift an `SU(4)` gate to two distinct coordinates of an arbitrary finite
qubit register, acting as identity on every other coordinate. -/
def twoQubitLift
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (Q → Bool) ℂ :=
  unitaryGroupReindex (splitTwoQubitConfig a b hab).symm
    (Quantum.tensorGate (specialUnitaryAsUnitary U) 1)

/-- A lifted local `SU(4)` gate has determinant one on the full register. -/
theorem twoQubitLift_mem_specialUnitary
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ((twoQubitLift a b hab U : Matrix.unitaryGroup (Q → Bool) ℂ) :
      Matrix (Q → Bool) (Q → Bool) ℂ) ∈
        Matrix.specialUnitaryGroup (Q → Bool) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · exact (twoQubitLift a b hab U).2
  · change Matrix.det
      (Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab).symm
        ((Quantum.tensorGate (specialUnitaryAsUnitary U) 1 :
          Matrix.unitaryGroup
            ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool)) ℂ) :
          Matrix ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool))
            ((Bool × Bool) × ({q : Q // q ≠ a ∧ q ≠ b} → Bool)) ℂ)) = 1
    have hone :
        ((1 : Matrix.unitaryGroup ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ) :
          Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
            ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ) = 1 := rfl
    rw [Matrix.det_reindexAlgEquiv, Quantum.tensorGate_val,
      Matrix.det_kronecker, hone, Matrix.det_one]
    have hdet : U.1.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
    simp [specialUnitaryAsUnitary, hdet]

/-- A fixed ordered two-qubit architecture with exactly `R` gate locations on
an `n`-qubit register. -/
structure TwoQubitArchitecture (n R : ℕ) where
  sites : Fin R → Fin n × Fin n
  distinct : ∀ r, (sites r).1 ≠ (sites r).2

namespace TwoQubitArchitecture

/-- Lift the local `SU(4)` parameter at one architecture location. -/
def gateLift {n R : ℕ} (A : TwoQubitArchitecture n R) (r : Fin R)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  twoQubitLift (A.sites r).1 (A.sites r).2 (A.distinct r) U

/-- Time-ordered contraction map from one local `SU(4)` choice per location
to the implemented `n`-qubit unitary. -/
def contraction {n R : ℕ} (A : TwoQubitArchitecture n R)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  (List.ofFn fun r => A.gateLift r (gates r)).prod

/-- Independent Haar law for every local `SU(4)` parameter of a fixed
architecture. -/
def gateLaw {n R : ℕ} (_A : TwoQubitArchitecture n R) :
    Measure (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :=
  finiteSpecialUnitaryHaarProduct (Fin R) (Bool × Bool)

/-- The fixed-architecture gate law is normalized. -/
theorem gateLaw_apply_univ {n R : ℕ} (A : TwoQubitArchitecture n R) :
    A.gateLaw Set.univ = 1 :=
  finiteSpecialUnitaryHaarProduct_apply_univ (Fin R) (Bool × Bool)

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
