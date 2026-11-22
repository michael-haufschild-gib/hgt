import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.SelectedGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit

/-! # The first-return gap with the near-Hilbert crossing recomputed -/
open Matrix Filter Set MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open PrescribedTimes PrecisionReturns EmptyVisitFlux FirstGate

/-- Recompute both the first near-Hilbert crossing and the ensuing first
empty visit after varying all the couplings. On a set of asymptotic
relative volume one at the original draw, the product of that absolute
return date and one specified ordered energy gap is exactly constant. -/
theorem gaussian_recomputed_first_return_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      let σ := crossingOrigin n (nearHilbertContinuousCircuitBudget (n+2)) (9/80) x
      let v := selectedDate n x
      0 < σ ∧ σ < v ∧ ∃ i j : Labels n, levels n x i < levels n x j ∧
        fullDensityAt {y | selectedDate n y*(levels n y i-levels n y j)=v*(levels n x i-levels n x j)} x := by
  let ε : ℝ := 1/10
  let r := SharpOccupation.physicalArc ε
  have hε : 0 < ε := by norm_num [ε]
  have hs : ε < sqrt 2 := by dsimp only [ε]; nlinarith only [sq_sqrt (by norm_num : (0:ℝ) ≤ 2),sqrt_nonneg 2]
  filter_upwards [gaussian_selected_gap_density r,LocalPatches.gaussian_first_crossing_local_width] with ω hd hc
  filter_upwards [hc] with k hk
  intro n x σ v
  let H := prefixGenerator n x
  let P := nearHilbertContinuousCircuitBudget (n+2)
  let E := H.2.isHermitian.eigenvalues
  let w (l : Fin (n+2)→Bool) := -E l/(2*π)
  obtain ⟨τ,hτ,hcross,hbefore,_⟩ := hk
  have hH : H.val=pathHamiltonian (pathPauliDisorderShell ω n) := numberedGenerator_shell _
  have hpath (s : ℕ) (t : ℝ) : pathGateDistance n s x t=orbitCircuitDistance H s t := rfl
  have hdist (s : ℕ) (t : ℝ) : orbitCircuitDistance H s t=orbitCircuitDistance
      (⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩ : selfAdjoint (Register (n+2))) s t := by
    unfold orbitCircuitDistance
    rw [hH]
  have hwidth : 0 ≤ LocalPatches.localCrossingWidth (n+2) := by unfold LocalPatches.localCrossingWidth; positivity
  have hτpos := hwidth.trans_lt hτ
  have hστ : σ=τ := crossingOrigin_eq_of_first hτpos.le ((hpath P τ).trans ((hdist P τ).trans hcross))
    (fun t ht => (hpath P t).trans_lt ((hdist P t).trans_lt (hbefore t ht)))
  have hfar : ε < orbitCircuitDistance H 0 σ := by
    by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mpr h
    have he := (hasProjectiveCircuitApproximation_iff_infDist _ P ε).mp ⟨z,hz,C,hC.trans (Nat.zero_le _),herr⟩
    change orbitCircuitDistance H P σ ≤ ε at he
    rw [hστ,hdist,hcross] at he
    norm_num [ε] at he
  have hv : v=firstVisit H σ 0 ε := selectedDate_eq n x
  obtain ⟨hτv,he⟩ := first_empty_entry_of_outside H hε hs hfar
  have hx := (SharpOccupation.physicalArc_spec hε hs).1
  obtain ⟨i,j,hface⟩ := (entry_iff_closed_face w hx.1.le hx.2).mp (hv ▸ he)
  obtain ⟨m,hm⟩ := lift_gap (fun l => -E l) v i j hface.2.1
  obtain ⟨p,hp⟩ := level_labels n x
  let a := p.symm i
  let b := p.symm j
  have hai : levels n x a=E i := by simpa only [a,Equiv.apply_symm_apply] using hp a
  have hbj : levels n x b=E j := by simpa only [b,Equiv.apply_symm_apply] using hp b
  have hgap : levels n x a < levels n x b := by
    rw [hai,hbj]
    exact neg_lt_neg_iff.mp ((div_lt_div_iff_of_pos_right (by positivity : 0 < 2*π)).mp hface.1)
  have hlevel : v*(levels n x a-levels n x b)=2*π*((m:ℝ)+r) := by
    rw [hai,hbj]
    have hm' := (div_eq_iff (by positivity : 2*π≠0)).mp hm
    linarith only [hm']
  refine ⟨hστ ▸ hτpos,hv ▸ hτv,a,b,hgap,?_⟩
  rw [hlevel]
  exact hd n a b m hlevel

#print axioms gaussian_recomputed_first_return_gap
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
