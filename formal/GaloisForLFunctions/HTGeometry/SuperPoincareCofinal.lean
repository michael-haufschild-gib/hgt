import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalConservativity

noncomputable section

namespace HTGeometry.ConstraintRelativity

/-- Filtration parity and prolongation form a split supertranslation sector. -/
def cofinalParityProlongD1N2Split (k : Type*) [Field k] :
    SuperPoincare.D1N2Split (Module.End k (ℕ → k)) :=
  SuperPoincare.D1N2Split.ofEqNeg
    (parityInv k) (prolong k) (parityInv_comp_prolong k)

/-- Filtration parity generates identity momentum. -/
theorem cofinalParityProlong_momentum0_eq_one
    (k : Type*) [Field k] :
    (cofinalParityProlongD1N2Split k).momentum0 = 1 := by
  apply LinearMap.ext
  exact parityInv_involutive k

/-- Prolongation momentum is the two-step filtration shift. -/
theorem cofinalParityProlong_momentum1_apply
    (k : Type*) [Field k] (x : ℕ → k) (n : ℕ) :
    (cofinalParityProlongD1N2Split k).momentum1 x n =
      if n < 2 then 0 else x (n - 2) := by
  change prolong k (prolong k x) n = _
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n => simp

end HTGeometry.ConstraintRelativity
