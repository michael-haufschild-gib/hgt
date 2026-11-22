import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Calibration
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliLineObstruction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathOverlap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliNoncontextualCircuit

/-! # An exterior-independent correlation on every path bond -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
variable {n : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Central $ZZ$ interaction and the $X$ reporter at its left endpoint. -/
def bondLabel (e : Fin (n+1)) : PathLabel n := .inr (e,2,2)
def bondReporter (e : Fin (n+1)) := onsiteWord e.castSucc 0

/-- Remove precisely those interactions meeting the calibrated bond. -/
def exteriorShell (u : PathShell n) (e : Fin (n+1)) : PathShell n :=
  WithLp.toLp 2 fun l => if l ∈ pathOverlaps (bondLabel e) then 0 else u l

private theorem exterior_commutes (u : PathShell n) (e : Fin (n+1))
    (q : Fin (n+2) → Option (Fin 3))
    (hq : labelSupport q ⊆ labelSupport (pathWord (bondLabel e))) :
    Commute (pathHamiltonian (exteriorShell u e)) (finitePauliMatrix q) := by
  classical
  rw [pathHamiltonian_eq_sum]
  apply Commute.sum_left
  intro l _
  by_cases h : l ∈ pathOverlaps (bondLabel e)
  · change Commute (((if l ∈ pathOverlaps (bondLabel e) then 0 else u l : ℝ):ℂ) • _) _
    simp only [if_pos h,Complex.ofReal_zero,zero_smul,Commute.zero_left]
  · have hd : Disjoint (labelSupport (pathWord (bondLabel e))) (labelSupport (pathWord l)) :=
      not_not.mp (mt mem_pathOverlaps.mpr h)
    exact (commute_finitePauliMatrix_of_disjoint (hd.symm.mono_right hq)).smul_left _

/-- The endpoint reporter anticommutes with the longitudinal bond. -/
theorem bond_reporter_anticommutes (e : Fin (n+1)) :
    let P := finitePauliMatrix (pathWord (bondLabel e))
    let Y := finitePauliMatrix (bondReporter e)
    P*Y=-(Y*P) := by
  apply finitePauliMatrix_anticommute_of_not_commute
  intro h
  have hz := (commute_onsite_coupling_iff e.castSucc 0 e (2,2)).mp h.symm
  exact (by decide : (0:Fin 3)≠2) (hz.1 rfl)

/-- Varying at most 42 Gaussian coordinates suffices to set the Choi
correlation to one at any nonzero time, for every choice of the exterior. -/
theorem path_bond_calibration (u : PathShell n) (e : Fin (n+1)) (t : ℝ) (ht : t≠0) :
    let P := finitePauliMatrix (pathWord (bondLabel e))
    let Y := finitePauliMatrix (bondReporter e)
    (pathOverlaps (bondLabel e)).card≤42 ∧
      fieldTrace (pathHamiltonian (exteriorShell u e)) P Y (Complex.I • (P*Y)) t (π/(4*t) : ℝ)=1 := by
  intro P Y
  refine ⟨pathOverlaps_card_le _,?_⟩
  let E : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (exteriorShell u e),isSelfAdjoint_pathHamiltonian _⟩
  apply calibrated_fieldTrace E P Y (exterior_commutes u e _ (fun _ h => h)) _
    (finitePauliMatrix_mul_self _) (finitePauliMatrix_mul_self _) _ t ht
  · apply exterior_commutes
    intro i hi
    have hh := mem_labelSupport.mp hi
    have he : i=e.castSucc := by
      by_contra hn
      exact hh (by simp only [bondReporter,onsiteWord,if_neg hn])
    rw [he,mem_labelSupport]
    simp [bondLabel,pathWord,couplingWord]
  · exact bond_reporter_anticommutes e

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
