import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture

/-!
# Totalized two-qubit lifts

The light-cone block stores a plain list of pairs.  This totalized lift gives
the identity at a degenerate pair and agrees definitionally with the ordinary
two-qubit lift at every valid block location.  It lets generic list-word
machinery state one uniform interpretation function.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Interpret any ordered pair as a register unitary; degenerate pairs are
assigned the identity. -/
def totalTwoQubitLift {Q : Type*} [Fintype Q] [DecidableEq Q] (edge : Q × Q)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Matrix.unitaryGroup (Q → Bool) ℂ :=
  if h : edge.1 = edge.2 then 1 else twoQubitLift edge.1 edge.2 h U

/-- At a genuine two-qubit location, the totalized interpretation is exactly
the ordinary register lift. -/
theorem totalTwoQubitLift_eq_twoQubitLift
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (edge : Q × Q) (hedge : edge.1 ≠ edge.2)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    totalTwoQubitLift edge U = twoQubitLift edge.1 edge.2 hedge U := by
  simp [totalTwoQubitLift, hedge]

/-- The identity local gate always has identity totalized lift. -/
theorem totalTwoQubitLift_one {Q : Type*} [Fintype Q] [DecidableEq Q]
    (edge : Q × Q) :
    totalTwoQubitLift edge 1 = 1 := by
  by_cases hedge : edge.1 = edge.2
  · simp [totalTwoQubitLift, hedge]
  · rw [totalTwoQubitLift_eq_twoQubitLift edge hedge]
    have hlocal : specialUnitaryAsUnitary
        (1 : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) = 1 := rfl
    rw [twoQubitLift, hlocal]
    apply Subtype.ext
    ext x y
    rw [unitaryGroupReindex_coe, Quantum.tensorGate_val]
    by_cases hxy : x = y
    · subst y
      simp
    · by_cases hlocal : (splitTwoQubitConfig edge.1 edge.2 hedge x).1 =
        (splitTwoQubitConfig edge.1 edge.2 hedge y).1
      · by_cases hrest : (splitTwoQubitConfig edge.1 edge.2 hedge x).2 =
          (splitTwoQubitConfig edge.1 edge.2 hedge y).2
        · exfalso
          apply hxy
          apply (splitTwoQubitConfig edge.1 edge.2 hedge).injective
          exact Prod.ext hlocal hrest
        · simp [hrest, hxy]
      · simp [hlocal, hxy]

end

end GaloisForLFunctions.HTGeometry
