import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Coupling boxes and removable interior bonds -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- Bonds in the nine-dimensional coefficient box of radius h. -/
def weakEdges (u : PathShell n) (h : ℝ) : Finset (Fin (n+1)) :=
  univ.filter fun e => ∀ ab : Fin 3×Fin 3, |u (.inr (e,ab))|≤h

/-- Discard weak odd bonds, keeping the two end bonds. -/
def removable (u : PathShell n) (h : ℝ) : Finset (Fin (n+1)) :=
  (weakEdges u h).filter fun e => e.val%2=1 ∧ e.val<n

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
