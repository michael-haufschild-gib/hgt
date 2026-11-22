import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.FieldBranchRows
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic

/-! # A rectangular polynomial minor detects independent physical eigenbranches -/
open Matrix MvPolynomial Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {n D d : ℕ}

def hasFieldMinor (H : Matrix (Fin D) (Fin D) ℂ) (u : Fin D → Fin n → ℂ) (w : Fin d → List (Fin n)) : Prop :=
  ∃ f : Fin d → (Fin n → ℂ) → ℂ,
    (∀ j, AnalyticAt ℂ (f j) 0 ∧ ∀ᶠ h in 𝓝 0,
      matrixCharpolyRelation (H+diagonal (fun k => fieldEnergy (u k) h),f j h)=0) ∧
    Function.Injective (fun j => f j 0) ∧ (Matrix.of fun i j => mixed (w i) (f j) 0).det≠0

/-- At a real simple background, a same-order minor of the cleared rows is nonzero
exactly when a choice of distinct physical levels has independent longitudinal derivatives. -/
theorem cleared_minor_iff_field (H : Matrix (Fin D) (Fin D) ℂ) (hH : H.IsHermitian)
    (hsep : H.charpoly.Separable) (u : Fin D → Fin n → ℂ) (w : Fin d → List (Fin n))
    (L : ℕ) (hw : ∀ i, (w i).length=L) :
    let E (j) := (hH.eigenvalues j:ℂ)
    let p := fieldCharacteristic H u
    let χ j (o : Option (Fin n)) := o.elim (E j) 0
    let A := Matrix.of fun i j => eval (χ j) (jetRow p L (some (w i)))
    (∃ s : Fin d → Fin D, (A.submatrix id s).det≠0) ↔ hasFieldMinor H u w := by
  classical
  intro E p χ A
  have hE : Function.Injective E := by
    rw [hH.charpoly_eq] at hsep
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep
  have hz (j : Fin D) : H.charpoly.eval (E j)=0 := by
    rw [hH.charpoly_eq,Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [E])
  let c (j : Fin D) := (eval (χ j) (pderiv none p))^(2*L)
  have hc (j) : c j ≠ 0 := pow_ne_zero _ (field_separant H u hsep _ (hz j))
  have hRel (s : Fin d → Fin D) (f : Fin d → (Fin n → ℂ) → ℂ)
      (hf : ∀ j, AnalyticAt ℂ (f j) 0 ∧ ∀ᶠ h in 𝓝 0,
        matrixCharpolyRelation (H+diagonal (fun k => fieldEnergy (u k) h),f j h)=0)
      (he : ∀ j, f j 0=E (s j)) :
      (A.submatrix id s).det≠0 ↔ (Matrix.of fun i j => mixed (w i) (f j) 0).det≠0 := by
    have hh : A.submatrix id s = (Matrix.of fun i j => mixed (w i) (f j) 0) * diagonal (c ∘ s) := by
      ext i j
      rw [Matrix.mul_diagonal]
      have hv := field_row_of_branch H u hsep (f j) (hf j).1 (hf j).2 (w i)
      dsimp only at hv
      rw [hw i,he j] at hv
      exact hv
    rw [hh,Matrix.det_mul,Matrix.det_diagonal]
    have hn : (∏ j, (c ∘ s) j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc (s j))
    exact ⟨fun h => left_ne_zero_of_mul h,fun h => mul_ne_zero h hn⟩
  constructor
  · rintro ⟨s,hs⟩
    choose f hfa he hr using fun j => simple_field_branch H u hsep (E (s j)) (hz (s j))
    have hf := fun j => And.intro (hfa j) (hr j)
    have hi : Function.Injective s := by
      intro i j hij
      by_contra hn
      exact hs (Matrix.det_zero_of_column_eq hn (fun k => by simp [Matrix.submatrix_apply,hij]))
    refine ⟨f,hf,?_,(hRel s f hf he).mp hs⟩
    intro i j hij
    exact hi (hE ((he i).symm.trans (hij.trans (he j))))
  · rintro ⟨f,hf,_,hm⟩
    have hex (j) : ∃ i, f j 0 = E i := by
      apply exists_eigenvalue_eq_of_charpolyDet_eq_zero hH
      simpa [fieldEnergy,matrixCharpolyRelation] using (hf j).2.self_of_nhds
    choose s hs using hex
    exact ⟨s,(hRel s f hf hs).mpr hm⟩

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
