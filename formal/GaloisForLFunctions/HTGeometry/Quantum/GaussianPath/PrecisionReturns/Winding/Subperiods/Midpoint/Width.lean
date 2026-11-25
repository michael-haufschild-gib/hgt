import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange

/-! # Physical scalar distance and shortest spectral arc in turns -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux
noncomputable section

/-- Width of the shortest enclosing spectral arc in complete turns. -/
def turnWidth {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ) : ℝ :=
  orbitSpectralEnclosingArcLength H t/(2*π)

theorem turnWidth_range {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ) : turnWidth H t∈Ico (0:ℝ) 1 :=
  ⟨div_nonneg (spectralEnclosingArcLength_nonneg _) two_pi_pos.le,
    (div_lt_one two_pi_pos).mpr (spectralEnclosingArcLength_lt_two_pi _)⟩

theorem arc_iff_width {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ) (u : Icc (0:ℝ) 1) :
    flow (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) t ∈ enclosingUnitArc u ↔ turnWidth H t≤u := by
  let θ := fun j => -(t*H.2.isHermitian.eigenvalues j)
  have hs : flow (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) t =
      fun j => ((θ j/(2*π):ℝ):UnitAddCircle) := by
    funext j
    unfold flow
    congr 1
    dsimp only [θ]
    ring
  rw [hs,mem_enclosingUnitArc_iff_spectralEnclosingArcLength_full θ u]
  change orbitSpectralEnclosingArcLength H t≤2*π*(u:ℝ) ↔ _/(2*π)≤(u:ℝ)
  rw [div_le_iff₀ two_pi_pos,mul_comm (u:ℝ)]

theorem scalar_distance_eq_chord {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ) :
    orbitCircuitDistance H 0 t=zeroGateArcTolerance (turnWidth H t) := by
  rw [orbitCircuitDistance_zeroGate_eq_enclosingArc,zeroGateArcTolerance,turnWidth]
  congr 2
  field_simp [pi_ne_zero]
  ring

#print axioms scalar_distance_eq_chord
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
