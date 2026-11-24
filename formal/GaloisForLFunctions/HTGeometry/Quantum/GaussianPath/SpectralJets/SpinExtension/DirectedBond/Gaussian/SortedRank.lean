import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.TypicalRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedRows

/-! # Full rank for ordinary real derivatives of the ordered physical energies -/
open Filter Topology Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem sorted_minor {D n : ℕ} {P : Fin n→Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {θ : Fin n→ℝ} (hθ : θ∈simpleEnsembleLocus hP)
    (k : Fin D) (w : Fin D→List (Fin n)) (F : Fin D→(Fin n→ℂ)→ℂ)
    (hf : ∀ l, AnalyticAt ℂ (F l) (realEmbed θ) ∧
      F l (realEmbed θ)=((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues l:ℂ) ∧
      ∀ᶠ z in 𝓝 (realEmbed θ), matrixCharpolyRelation (∑ a, z a • P a,F l z)=0)
    (hd : (of fun i l => if i=k then (1:ℂ) else mixed (w i) (F l) (realEmbed θ)).det≠0) :
    (of fun i l => if i=k then (1:ℝ) else realMixed (w i) (fun y => sortedEnsembleSpectrum hP y l) θ).det≠0 := by
  let E := (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues
  let σ := (Tuple.sort E).symm
  let A := of fun i l => if i=k then (1:ℝ) else realMixed (w i) (fun y => sortedEnsembleSpectrum hP y l) θ
  have hs := injective_sortedEnsembleSpectrum hP hθ
  have he (l v) : mixed v (F l) (realEmbed θ) =
      (realMixed v (fun y => sortedEnsembleSpectrum hP y (σ l)) θ:ℂ) := by
    obtain ⟨j,hj⟩ := branch_sorted_germ hP hs (hf l).1.continuousAt (hf l).2.2
    have hσ : F l (realEmbed θ)=(sortedEnsembleSpectrum hP θ (σ l):ℂ) := by
      rw [(hf l).2.1]
      exact congrArg Complex.ofReal (sortedTuple_symm_apply E l).symm
    have hjσ := hs (Complex.ofReal_injective (hj.self_of_nhds.symm.trans hσ))
    exact mixed_of_real_germ (hf l).1 (hjσ ▸ hj) v
  have hM : (of fun i l => if i=k then (1:ℂ) else mixed (w i) (F l) (realEmbed θ)) =
      (A.map Complex.ofRealHom).submatrix id σ := by
    ext i l
    by_cases hi : i=k <;> simp [A,hi,Matrix.submatrix_apply,he]
  intro hz
  apply hd
  have hmap : (A.map Complex.ofRealHom).det=Complex.ofRealHom A.det :=
    (Complex.ofRealHom.map_det A).symm
  rw [hM,Matrix.det_permute',hmap,show A.det=0 from hz,map_zero,mul_zero]

/-- The same physical words span the real projective energy space on every
Gaussian prefix of at least three spins. Sorting the energies only permutes
the columns of the minor. -/
theorem gaussian_sorted_full_projective_rank :
    ∃ (k₀ : (k : ℕ)→Fin (2^(k+3))) (v : (k : ℕ)→Fin (2^(k+3))→List (Fin (k+3))),
      (∀ k i, ∃ u, Suffix (k+2) u ∧ v k i=letters false u) ∧
      (∀ k i, (v k i).length≤2*(k+2)+1) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
        let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
        (of fun i j => if i=k₀ k then (1:ℝ)
          else realMixed ((v k i).map (fieldIndex (k+2))) (fun x => E x j) θ).det≠0 := by
  obtain ⟨k₀,v,hv,hl,hr⟩ := gaussian_full_projective_rank
  refine ⟨k₀,v,hv,hl,?_⟩
  filter_upwards [hr,gaussian_path_all_prefixes_maximally_projective] with ω hrank hgen
  intro k θ E
  let u := pathPauliDisorderShell ω (k+1)
  let q := qubitConfigFin (k+3)
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have hp : ∃ h : (reindex q q (pathHamiltonian u)).IsHermitian, MaximallyProjectiveEnergy h.eigenvalues :=
    ⟨hH.reindex q,Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv q hH (hgen k)⟩
  rw [reindex_pathHamiltonian] at hp
  obtain ⟨F,hf,hd⟩ := hrank k
  exact sorted_minor (chainPauliFin_isHermitian _) hp.choose_spec.injective (k₀ k)
    (fun i => (v k i).map (fieldIndex (k+2))) F hf hd

#print axioms gaussian_sorted_full_projective_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
