import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.CarrierGap

/-! # A simple diagonal carrier with a dominant field at any chosen site -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section
variable {n : ℕ}

/-- Increasing one longitudinal field separates its two spin sectors.
Inside each sector the original base-three energy gaps are preserved. -/
theorem exists_gapped_carrier (q : Fin (n+2)) :
    ∃ u : PathShell n, ∃ h>(0:ℝ), ∃ d : (Fin (n+2)→Bool)→ℂ,
      Function.Injective d ∧ pathHamiltonian u=diagonal d ∧ core q u=u ∧
      ‖pathHamiltonian u-h • spin q‖+2<h ∧
      (∀ i : Fin (n+2), 1≤u (.inl (i,2))) ∧ (∀ e : Fin (n+1), u (.inr (e,(2,2)))=1) ∧
      (∀ l, ¬IsDiagLabel l → u l=0) := by
  obtain ⟨u,h,hh,d,hs,hmat,hcore,hgap,hi,he,hoz,_,_⟩ := quantitative_gapped_carrier q
  refine ⟨u,h,hh,(fun x => (d x:ℂ)),?_,hmat,hcore,?_,hi,he,hoz⟩
  · intro x y hxy
    by_contra hn
    have hb := hs x y hn
    rw [Complex.ofReal_injective hxy,sub_self,abs_zero] at hb
    exact (by positivity : 0 < 1/(3:ℝ)^(n+2)).not_ge hb
  · linarith only [hgap]

#print axioms exists_gapped_carrier
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
