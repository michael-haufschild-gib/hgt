import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointCap

/-! # An explicit coefficient radius for cheap physical increments -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds.SingleCut
noncomputable section

/-- A box of radius β3⁻ᴷ/M in the M physical coordinates suffices.
Only the fourteen transverse entries incur further time dependence. -/
theorem uniform_central_box :
    ∃ β∈Set.Ioc (0:ℝ) (1/2), ∀ {n : ℕ} (a b : Fin (n+1)), a.succ=b.castSucc →
      2 ≤ (Iic a.succ).card → 2 ≤ (Ici a.succ).card →
      let M : ℝ := Fintype.card (PathLabel n)
      let r := β/(M*3^(n+2))
      ∃ w : PathShell n, (∀ i : Fin (n+2), 1 ≤ w (.inl (i,2))) ∧
        (∀ e : Fin (n+1), w (.inr (e,(2,2)))=1) ∧ (∀ l, ¬IsDiagLabel l → w l=0) ∧
        (∀ l : PathLabel n, |w l| ≤ 2+(if l=.inl (a.succ,2) then 2*M+3 else 0)) ∧
        ∀ u : PathShell n, (∀ l, |u l-w l| ≤ r) →
        ∀ T ≥ (1:ℝ), (∀ l∈transverseLabels a b, |u l| ≤ 1/(1800*sqrt T)) →
        ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation (n+2) (1/100)
          (blockCost (Iic a.succ).card+blockCost (Ici a.succ).card)
          (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨β,hβ,h⟩ := uniform_joint_central_box
  refine ⟨β,hβ,?_⟩
  intro n a b hab hL hR M r
  obtain ⟨w,hi,he,hz,hsize,hw⟩ := h a b hab hL hR
  exact ⟨w,hi,he,hz,hsize,fun u hu => (hw u hu).2⟩

#print axioms uniform_central_box
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
