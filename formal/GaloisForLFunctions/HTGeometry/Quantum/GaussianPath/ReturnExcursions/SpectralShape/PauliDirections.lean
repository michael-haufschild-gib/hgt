import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.LocalDirections

/-! # Separated squared skewness on two unit path fields -/

namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section

/-- A single onsite Pauli and a normalized sum on the same bond give separated
values of the standardized third moment. -/
theorem separated_directions (n : ℕ) :
    ∃ u v : PathShell n, ‖u‖=1 ∧ ‖v‖=1 ∧ thirdMoment u=0 ∧ thirdMoment v^2=4/3 := by
  obtain ⟨u,v,hu,hv,hm,hm',_⟩ := local_directions (n:=n) 0
  exact ⟨u,v,hu,hv,hm,hm'⟩

/-- The leading coefficient on a unit coupling line is bounded away from zero
uniformly in the proposed squared skewness and in the number of sites. -/
theorem uniform_direction (n : ℕ) (c : ℝ) :
    ∃ v : PathShell n, ‖v‖=1 ∧ 2/3≤|skewConstraint c v| := by
  obtain ⟨u,v,hu,hv,hm,hm'⟩ := separated_directions n
  by_cases hc : 2/3≤|c|
  · exact ⟨u,hu,by simpa [skewConstraint,hu,hm] using hc⟩
  · refine ⟨v,hv,?_⟩
    simp only [skewConstraint,hm',hv,one_pow,mul_one]
    exact (by linarith only [le_abs_self c,lt_of_not_ge hc] : (2:ℝ)/3≤4/3-c).trans (le_abs_self _)

#print axioms uniform_direction
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
