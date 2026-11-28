import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.Laboratory

/-! # The original first wait and the signed macroscopic detuning sum -/

open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
open AngularWindings.PhysicalTubes PrecisionReturns PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- For each elapsed horizon either the original first dip lies later, or
one physical circuit of the specified budget has the stated signed
macroscopic detuning sum on the window fixed at the robust crossing. -/
theorem first_wait_or_window_sum (k : ℕ) (ω : PathPauliDisorder) (L : ℝ) (s : ℕ) :
    let K := k+3
    let D := 2^K
    let H := generator (pathPauliDisorderShell ω (k+1))
    let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
    let v := firstVisit H σ s (1/10)
    let w := L+clearanceTime H
    let q := D/2
    let B : ℝ := D.choose q
    L<v-σ ∨ ∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10) ∧
      clearanceTime H/w*(B*(1-(9/80:ℝ)^2/2)^min q (D-q))^2-B*(2^(D/4)*(3/2)^D) ≤
        windowSum (univ.powersetCard q) (circuitMinor H C.eval) H.2.isHermitian.eigenvalues (D/4) σ w := by
  intro K D H σ v w q B
  by_cases ht : L<v-σ
  · exact Or.inl ht
  right
  obtain ⟨hσ,z,hz,C,hC,hf⟩ := (firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)).1
  have hv : v∈Icc σ (σ+L) := ⟨hσ,by linarith only [le_of_not_gt ht]⟩
  have hw : v∈laboratoryDates H C.eval (1/10) := ⟨z,hz,hf⟩
  have hd : Fintype.card (Fin K → Bool)=D := by simp [D]
  have hq : q≤Fintype.card (Fin K → Bool) := hd ▸ Nat.div_le_self ..
  refine ⟨C,hC,hw,?_⟩
  have h := laboratory_window (I:=Fin K → Bool) H C.eval hv hw q (D/4) hq
  simpa only [hd,B,w] using h

#print axioms first_wait_or_window_sum
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
