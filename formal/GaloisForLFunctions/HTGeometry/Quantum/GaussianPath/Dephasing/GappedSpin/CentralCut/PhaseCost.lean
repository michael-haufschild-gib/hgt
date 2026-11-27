import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.PacketSplit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.CutPackets
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations

/-! # All-time diagonal phase budgets on both sides of a conserved spin -/
open Set Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds.SingleCut DiagonalSynthesis
noncomputable section

/-- Near a simple diagonal matrix, each half evolution can use the
diagonal phase budget of its own support. The shared central spin is
counted in both budgets. No time-dependent error accumulates here. -/
theorem eventual_conserved_cost {n : ℕ} (a : Fin (n+1))
    (hL : 2≤(Finset.Iic a.succ).card) (hR : 2≤(Finset.Ici a.succ).card)
    (d : (Fin (n+2)→Bool)→ℂ) (hd : Function.Injective d) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ H : Register (n+2) in 𝓝 (diagonal d), ∀ u : PathShell n,
      H=pathHamiltonian u → longitudinalAt a.succ u → ∀ t : ℝ,
      HasProjectiveCircuitApproximation (n+2) ε
        (blockCost (Finset.Iic a.succ).card+blockCost (Finset.Ici a.succ).card) (unitaryEvolution H t) := by
  filter_upwards [eventually_cheap_supported _ hL d hd (half_pos hε),
    eventually_cheap_supported _ hR d hd (half_pos hε)] with H hleft hright
  intro u hu h t
  let L := pathHamiltonian (restricted (onLeft a) u)
  let R := pathHamiltonian (restricted (fun l => ¬onLeft a l) u)
  obtain ⟨hs,hc,hl,hr⟩ := conserved_split a u h
  have hH : H=L+R := hu.trans hs
  have hLR : Commute L R := hc
  have com {X Y : Register (n+2)} (hc : Commute X Y) :
      Commute X (unitaryEvolution Y t) := ((hc.smul_right (-Complex.I)).smul_right t).exp_right
  have lcomm : Commute H (unitaryEvolution L t) := by
    rw [hH]; exact (com (Commute.refl L)).add_left (com hLR.symm)
  have rcomm : Commute H (unitaryEvolution R t) := by
    rw [hH]; exact (com hLR).add_left (com (Commute.refl R))
  have hLU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian (restricted (onLeft a) u)) t
  have hRU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian (restricted (fun l => ¬onLeft a l) u)) t
  have h₁ := hleft ⟨unitaryEvolution L t,hLU⟩ (isSiteSupported_unitaryEvolution hl t) lcomm.eq
  have h₂ := hright ⟨unitaryEvolution R t,hRU⟩ (isSiteSupported_unitaryEvolution hr t) rcomm.eq
  rw [hH,unitaryEvolution_add_of_commuting hLR]
  exact (add_halves ε) ▸ LocalPatches.approx_product hRU h₁ h₂

#print axioms eventual_conserved_cost
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
