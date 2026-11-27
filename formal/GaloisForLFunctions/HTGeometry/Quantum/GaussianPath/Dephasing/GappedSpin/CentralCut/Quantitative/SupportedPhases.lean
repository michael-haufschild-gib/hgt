import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.UnitaryPhases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.CutPackets

/-! # Quantitative diagonal synthesis on the support of a commuting unitary -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open DiagonalSynthesis DiagonalSynthesis.CommutatorBounds WeakBonds.SingleCut
noncomputable section

/-- Normalizing the diagonal of a supported unitary retains its support.
Only the spectrum of the reference diagonal enters the error. -/
theorem supported_phase_cost {N : ℕ} (S : Finset (Fin N)) (hS : 2 ≤ S.card)
    (H U : Register N) (hu : U∈unitary (Register N))
    (hs : IsSiteSupported (A:=fun _:Fin N => Bool) S U) (hc : Commute H U)
    (d : (Fin N→Bool)→ℝ) {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) :
    HasProjectiveCircuitApproximation N
      (4*sqrt packConstant/g*‖H-diagonal (fun i => (d i:ℂ))‖) (blockCost S.card) U := by
  obtain ⟨w,hw,he,hfit⟩ := commuting_diagonal_approximation H U hu hc.eq d hg hsep
  have hdiag : IsSiteSupported (A:=fun _ : Fin N => Bool) S (diagonal w) := by
    constructor
    · rintro x y ⟨i,_,hi⟩
      exact diagonal_apply_ne _ (fun h => hi (congrFun h i))
    · intro x y u v hx hy hout hout'
      have hxy : x=y ↔ u=v := by
        constructor
        · rintro rfl
          exact funext fun i => by
            by_cases hi : i∈S
            · exact (hx i hi).symm.trans (hy i hi)
            · exact hout' i hi
        · rintro rfl
          exact funext fun i => by
            by_cases hi : i∈S
            · exact (hx i hi).trans (hy i hi).symm
            · exact hout i hi
      by_cases heq : x=y
      · have huv := hxy.mp heq
        subst y; subst v
        rw [diagonal_apply_eq,diagonal_apply_eq]
        exact he _ _ (hs.2 x x u u hx hx (fun _ _ => rfl) (fun _ _ => rfl))
      · rw [diagonal_apply_ne _ heq,diagonal_apply_ne _ (fun e => heq (hxy.mpr e))]
  obtain ⟨z,hz,C,hC,hW⟩ := supported_diagonal S hS w hw hdiag
  exact ⟨z,hz,C,hC,hW ▸ hfit⟩

#print axioms supported_phase_cost
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
