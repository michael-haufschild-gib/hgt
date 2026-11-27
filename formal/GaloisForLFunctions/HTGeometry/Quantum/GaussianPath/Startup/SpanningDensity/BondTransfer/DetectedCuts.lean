import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.CrowdedCut
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PhysicalFloor

/-! # Finite count of detectable bonds across a fitting circuit cut -/

open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon
noncomputable section

/-- Beyond the two endpoint strips and failed weak boundaries, at most
order R/r² detectable bonds cross any cut of a quarter-error circuit.
The strip length and transfer threshold may vary with the prefix. -/
theorem detected_cut_count {n : ℕ} (ω : PathPauliDisorder) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    {r t γ : ℝ} (hr : 0<r) (R k : ℕ) (hk : 16<(k:ℝ)*r)
    (hweak : 36* |t| *γ≤r/16) (z : ℂ) (hz : ‖z‖=1)
    (hf : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4) :
    (detectable c (pathPauliDisorderShell ω n) t r).card<
      2*(2*R+2)*(k*k)+(missedBonds n R γ ω).card+2*R := by
  by_contra! h
  have hkpos : 0<k := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh,Nat.cast_zero,zero_mul] at hk
    norm_num at hk
  have hov := crowded_cut_overlap (Nat.mul_pos hkpos hkpos) R ω C c (by linarith only [hr] : r/16<r) hweak h
  have hs := overlap_of_square_packets hr (by norm_num : (0:ℝ)<1/2)
    (by linarith only [hr] : r/16≤r/4) (le_of_eq (by ring) : r/16≤r*(1/2)/8)
    (by linarith only [hk]) _ hov
  have hfit := overlap_of_fit _ _ (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) t)
    C.eval.2 z hz hf
  linarith only [hs,hfit]

#print axioms detected_cut_count
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
