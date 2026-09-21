import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFriedrichs

/-!
# Exceptional Maass source in the cuspidal Friedrichs carrier

The exceptional Maass source is already a nonzero element of the exact closed
cuspidal `L²` carrier on which the compact-resolvent Friedrichs operator acts.
This fixes the carrier interface for the remaining Green-identity step: that
step must prove that this literal vector belongs to the operator domain and
has eigenvalue `1 + lam`.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

/-- The actual exceptional source, corestricted to the closed cuspidal carrier
of the compact Friedrichs operator. -/
def sourceCuspidalL2Vector : CuspidalL2 N :=
  cuspidalFormInclusionClosure N (sourceCuspidalFormVector N lam f)

/-- Forgetting the closed-carrier membership recovers the original literal
quotient `L²` source. -/
theorem sourceCuspidalL2Vector_val :
    (sourceCuspidalL2Vector N lam f : DeckL2 N) = sourceLp N f := by
  exact cuspidalFormInclusion_sourceCuspidalFormVector N lam f

/-- The source remains nonzero after corestriction to the closed cuspidal
carrier. -/
theorem sourceCuspidalL2Vector_ne_zero : sourceCuspidalL2Vector N lam f ≠ 0 := by
  intro h
  apply sourceLp_ne_zero N f
  rw [← sourceCuspidalL2Vector_val N lam f, h]
  rfl

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
