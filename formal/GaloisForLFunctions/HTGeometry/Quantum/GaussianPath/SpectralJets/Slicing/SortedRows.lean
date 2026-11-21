import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedGerms
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality

/-! # Rational mixed derivatives of the sorted real spectrum -/

open MvPolynomial Matrix Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R]

/-- Evaluate one row numerator or denominator at a sorted energy. -/
def sortedEval {P : Fin n → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (q : MvPolynomial (Option (Fin n)) ℂ) (θ : Fin n → ℝ) (j : Fin D) : ℂ :=
  eval (fun o : Option (Fin n) => o.elim (sortedEnsembleSpectrum hP θ j : ℂ) (realEmbed θ)) q

theorem continuous_sortedEval {P : Fin n → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (q : MvPolynomial (Option (Fin n)) ℂ) (j : Fin D) : Continuous (fun y => sortedEval hP q y j) := by
  apply q.continuous_eval.comp
  apply continuous_pi
  intro o
  cases o with
  | none => exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_sortedEnsembleSpectrum hP))
  | some i => exact Complex.continuous_ofReal.comp (continuous_apply i)

/-- At every simple Hermitian specialization, all sorted real mixed derivatives
are the corresponding rational functions of the sorted energies. -/
theorem sorted_root_differentials (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hmap : (fun a => (A a).map φ) = P)
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin n → ℝ) (hθ : θ ∈ simpleEnsembleLocus hP)
    (i : Fin D) :
    let p := map φ (characteristic A)
    sortedEval hP (pderiv none p) θ i ≠ 0 ∧ ∀ w,
      AnalyticAt ℝ (realMixed w (fun y => sortedEnsembleSpectrum hP y i)) θ ∧
      (realMixed w (fun y => sortedEnsembleSpectrum hP y i) θ : ℂ) =
        sortedEval hP (numerator p w) θ i / sortedEval hP (pderiv none p) θ i^(2*w.length) := by
  subst P
  intro p
  let x := realEmbed θ
  let H := isHermitian_spectralEnsembleMatrix hP θ
  let j := Tuple.sort H.eigenvalues i
  obtain ⟨f,hf,hs,_⟩ := simple_pencil_branch_detector A φ x H hθ
  have hbase : f j x = (sortedEnsembleSpectrum hP θ i : ℂ) := (hf j).2.1
  have hon (q : MvPolynomial (Option (Fin n)) ℂ) : onRoot q (f j) x = sortedEval hP q θ i := by
    unfold onRoot sortedEval
    rw [hbase]
  have hsimple := injective_sortedEnsembleSpectrum hP hθ
  obtain ⟨l,hl⟩ := branch_sorted_germ hP hsimple (hf j).1.continuousAt (hf j).2.2
  have he : l=i := hsimple (Complex.ofReal_injective (hl.self_of_nhds.symm.trans hbase))
  subst l
  have hr : ∀ᶠ y in 𝓝 x, onRoot p (f j) y = 0 := by
    filter_upwards [(hf j).2.2] with y hy
    rw [onRoot,show p = map φ (characteristic A) from rfl,eval_map]
    exact (eval_characteristic A φ y (f j y)).trans hy
  refine ⟨fun h => hs j ((hon _).trans h),?_⟩
  intro w
  refine ⟨analyticAt_realMixed_of_germ (hf j).1 hl w,?_⟩
  rw [← mixed_of_real_germ (hf j).1 hl w]
  have h := (eventually_mixed_quotient p (hf j).1 hr (hs j) w).self_of_nhds
  exact h.trans (by rw [hon,hon])

#print axioms sorted_root_differentials
end
end GaloisForLFunctions.HTGeometry.SpectralJets
