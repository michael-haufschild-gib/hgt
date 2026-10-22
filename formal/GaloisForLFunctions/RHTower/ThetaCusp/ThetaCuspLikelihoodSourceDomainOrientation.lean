import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodModularSeamWindow
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSwapBulkStratification

/-!
# Source-domain orientation for theta likelihood prime faces

The explicit zero-likelihood boundary is the exact source threshold for positivity of every
likelihood temperature.  This converts the prime-face and two-leg bulk orientation laws from
coordinate-sign interfaces to their natural source domains.
-/

namespace RHTower

noncomputable section

/-- Prime boundary-face orientation at every source point above the exact likelihood boundary. -/
theorem thetaCuspSourceBoundaryFacePrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
    {k : ℕ} (hk : k.Prime) {x : ℝ}
    (hx : thetaCuspLikelihoodBoundaryPoint < x)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k x z *
      (starRingEnd ℂ)
        (thetaCuspSourceBoundaryFaceMassShellPhase k x z)).im < 0 :=
  thetaCuspSourceBoundaryFacePrimeMassShellPhase_current_lt_zero hk
    ((thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt x).2 hx) hz

/-- Two-leg prime bulk orientation on the exact open source domain. -/
theorem thetaCuspSourceSwapPrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
    {k : ℕ} (hk : k.Prime) {x y : ℝ}
    (hx : thetaCuspLikelihoodBoundaryPoint < x)
    (hy : thetaCuspLikelihoodBoundaryPoint < y)
    {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceSwapMassShellPhaseDerivative k x y z *
      (starRingEnd ℂ) (thetaCuspSourceSwapMassShellPhase k x y z)).im < 0 := by
  have hBx : 0 < thetaCuspLikelihoodCoordinate x :=
    (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt x).2 hx
  have hBy : 0 < thetaCuspLikelihoodCoordinate y :=
    (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt y).2 hy
  exact thetaCuspSourceSwapPrimeMassShellPhase_current_lt_zero hk
    hBx.le hBy.le (add_pos hBx hBy) hz

/-- Prime boundary-face orientation at the modular center, with no source-sign premise. -/
theorem thetaCuspSourceBoundaryFacePrimeMassShellPhase_center_current_lt_zero
    {k : ℕ} (hk : k.Prime) {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceBoundaryFaceMassShellPhaseDerivative k 0 z *
      (starRingEnd ℂ)
        (thetaCuspSourceBoundaryFaceMassShellPhase k 0 z)).im < 0 :=
  thetaCuspSourceBoundaryFacePrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
    hk thetaCuspLikelihoodBoundaryPoint_neg hz

/-- Two-leg prime bulk orientation at the modular center, with all source signs discharged. -/
theorem thetaCuspSourceSwapPrimeMassShellPhase_center_current_lt_zero
    {k : ℕ} (hk : k.Prime) {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspSourceSwapMassShellPhaseDerivative k 0 0 z *
      (starRingEnd ℂ) (thetaCuspSourceSwapMassShellPhase k 0 0 z)).im < 0 :=
  thetaCuspSourceSwapPrimeMassShellPhase_current_lt_zero_of_boundaryPoint_lt
    hk thetaCuspLikelihoodBoundaryPoint_neg
      thetaCuspLikelihoodBoundaryPoint_neg hz

end

end RHTower
