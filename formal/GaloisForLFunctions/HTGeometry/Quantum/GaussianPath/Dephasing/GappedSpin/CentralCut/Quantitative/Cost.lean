import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.SupportedPhases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.PacketSplit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations

/-! # Explicit error for the two overlapping half-chain phase circuits -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open DiagonalSynthesis WeakBonds.SingleCut
noncomputable section

/-- Each factor commutes with the full longitudinal generator. Their
shared spin therefore costs at most twice the supported phase error. -/
theorem conserved_cost_at_gap {n : ℕ} (a : Fin (n+1)) (u : PathShell n)
    (hL : 2 ≤ (Finset.Iic a.succ).card) (hR : 2 ≤ (Finset.Ici a.succ).card)
    (hlong : longitudinalAt a.succ u) (d : (Fin (n+2)→Bool)→ℝ)
    {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (t : ℝ) :
    let H := pathHamiltonian u
    let δ := 4*sqrt packConstant/g*‖H-diagonal (fun i => (d i:ℂ))‖
    HasProjectiveCircuitApproximation (n+2) (δ+δ)
      (blockCost (Finset.Iic a.succ).card+blockCost (Finset.Ici a.succ).card)
      (unitaryEvolution H t) := by
  intro H δ
  let L := pathHamiltonian (restricted (onLeft a) u)
  let R := pathHamiltonian (restricted (fun l => ¬onLeft a l) u)
  obtain ⟨hs,hc,hl,hr⟩ := conserved_split a u hlong
  have hH : H=L+R := hs
  have hLR : Commute L R := hc
  have com {X Y : Register (n+2)} (hc : Commute X Y) :
      Commute X (unitaryEvolution Y t) := ((hc.smul_right (-Complex.I)).smul_right t).exp_right
  have lcomm : Commute H (unitaryEvolution L t) := by
    rw [hH]; exact (com (Commute.refl L)).add_left (com hLR.symm)
  have rcomm : Commute H (unitaryEvolution R t) := by
    rw [hH]; exact (com hLR).add_left (com (Commute.refl R))
  have huL := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian (restricted (onLeft a) u)) t
  have huR := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian (restricted (fun l => ¬onLeft a l) u)) t
  have h₁ := supported_phase_cost _ hL H _ huL (isSiteSupported_unitaryEvolution hl t) lcomm d hg hsep
  have h₂ := supported_phase_cost _ hR H _ huR (isSiteSupported_unitaryEvolution hr t) rcomm d hg hsep
  rw [hH,unitaryEvolution_add_of_commuting hLR]
  exact LocalPatches.approx_product huR h₁ h₂

#print axioms conserved_cost_at_gap
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
