import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.AnalyticFibers
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.LineBranches

/-! # Algebraic germs for the energies along a single unrevealed field -/

open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
open SelectedDates.AlgebraicCurves
noncomputable section

/-- At each simple field value the sorted energies admit holomorphic
algebraic continuations in the field increment, with no eigenvector choices. -/
theorem sorted_field_germ {I : Type*} [Fintype I] [DecidableEq I] {A Z : Matrix I I ℂ}
    (ha : A.IsHermitian) (hz : Z.IsHermitian) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    {t : ℝ} (hi : Function.Injective (hH t).eigenvalues) (j : Fin (Fintype.card I)) :
    ∃ g : ℂ→ℂ, ∃ hg : AnalyticAt ℂ g 0, IsAlgebraic (RatFunc ℂ) (ofMero g hg.meromorphicAt) ∧
      (fun v : ℝ => g v) =ᶠ[𝓝 0] fun v =>
        (sortedFieldLevels (fun y => (hH y).eigenvalues) (t+v) j : ℂ) := by
  let e := Fintype.equivFin I
  let P : Fin 2→Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
    ![reindex e e A,reindex e e Z]
  have hP (i : Fin 2) : (P i).IsHermitian := by
    fin_cases i
    · exact ha.reindex e
    · exact hz.reindex e
  let w (y : ℝ) : Fin 2→ℝ := ![1,y]
  have he (y : ℝ) : spectralEnsembleMatrix P (w y)=reindex e e (A+(y:ℂ) • Z) := by
    ext i l
    simp [spectralEnsembleMatrix,Fin.sum_univ_two,P,w,reindex_apply]
  have hsort (y : ℝ) : sortedEnsembleSpectrum hP (w y)=sortedFieldLevels (fun u => (hH u).eigenvalues) y := by
    refine Eq.trans ?_ (sortedTuple_eigenvalues_reindex e (hH y))
    have same {B C : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ}
        (hb : B.IsHermitian) (hc : C.IsHermitian) (h : B=C) :
        sortedTuple hb.eigenvalues=sortedTuple hc.eigenvalues := by subst C; rfl
    exact same _ _ (he y)
  have hin : Function.Injective (isHermitian_spectralEnsembleMatrix hP (w t)).eigenvalues := by
    rw [injective_iff_injective_sortedTuple]
    change Function.Injective (sortedEnsembleSpectrum hP (w t))
    rw [hsort]
    exact injective_sortedTuple (hi.comp e.symm.injective)
  let d : Fin 2 → ℝ := ![0,1]
  obtain ⟨g,hg,hag,hr⟩ := line_energy_germ hP (w t) d hin j
  refine ⟨g,hg,hag,hr.trans (.of_forall fun v => ?_)⟩
  have hw : (fun a => w t a+v*d a)=w (t+v) := by
    funext i
    fin_cases i <;> simp [w,d]
  rw [hw,hsort]

#print axioms sorted_field_germ
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
