import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.GaussianAffinePauliProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance

/-! # Generic spectra of all finite prefixes of one Gaussian Pauli chain -/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def disorderIndex {n : ℕ} : PathLabel n → ℕ × PathPauliDirections
  | .inl (s,a) => (s.val,.inl a)
  | .inr (e,ab) => (e.val,.inr ab)

private theorem disorderIndex_injective (n : ℕ) : Function.Injective (disorderIndex (n := n)) := by
  intro l j h
  rcases l with ⟨a,b⟩ | ⟨a,b⟩ <;> rcases j with ⟨c,d⟩ | ⟨c,d⟩
  · have he := Prod.mk.inj h
    exact congrArg Sum.inl (Prod.ext (Fin.ext he.1) (Sum.inl.inj he.2))
  · exact nomatch congrArg Prod.snd h
  · exact nomatch congrArg Prod.snd h
  · have he := Prod.mk.inj h
    exact congrArg Sum.inr (Prod.ext (Fin.ext he.1) (Sum.inr.inj he.2))

private theorem disorder_prefix_law (n : ℕ) :
    MeasurePreserving (fun ω => fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i))
      pathPauliDisorderLaw (centredProductGaussian (Fin (Fintype.card (ChainLabel (n+2)))) 1) := by
  let f := (disorderIndex (n := n)) ∘ (pathCoeffEquiv n)
  have hf : Function.Injective f := (disorderIndex_injective n).comp (pathCoeffEquiv n).injective
  have hi := iIndepFun_infinitePi (P := fun _ : ℕ × PathPauliDirections => gaussianReal 0 1)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have heval : MeasurePreserving (fun ω : PathPauliDisorder => fun i => ω (f i)) pathPauliDisorderLaw
      (centredProductGaussian (Fin (Fintype.card (ChainLabel (n+2)))) 1) := by
    refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply _),?_⟩
    have h := (hi.precomp hf).map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)
    change Measure.map (fun ω : PathPauliDisorder => fun i => ω (f i)) _ =
      Measure.pi (fun _ => gaussianReal 0 1)
    convert h using 1
    congr 1
    funext i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ × PathPauliDirections => gaussianReal 0 1)
      (f i)).map_eq.symm
  convert heval using 1
  funext ω i
  change pathPauliDisorderShell ω n (pathCoeffEquiv n i) = ω (disorderIndex (pathCoeffEquiv n i))
  cases (pathCoeffEquiv n i) <;> rfl

private theorem chain_spectrum_ae_gaussian (k : ℕ) :
    ∀ᵐ θ ∂(centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1),
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k+3)) θ).eigenvalues := by
  obtain ⟨θ₀,hθ₀⟩ := exists_chainShell_maximallyProjective_witness k
  let P := chainPauliFin (k+3)
  have hP := chainPauliFin_isHermitian (k+3)
  have hnull := (polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (spectralGenericMatrix P) θ₀ (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues
    hθ₀ hθ₀.injective (by
      intro i
      rw [map_spectralGenericMatrix_eq θ₀]
      exact charpolyRelation_eigenvalues (isHermitian_spectralEnsembleMatrix hP θ₀) i)).2.2
  have hac : centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous
      (Fintype.card (ChainLabel (k+3))) one_ne_zero (fun _ => 0)
  have hg : ∀ᵐ θ ∂(centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1),
      θ ∈ polynomialMatrixProjectiveGenericSet (spectralGenericMatrix P) := ae_iff.mpr (hac hnull)
  filter_upwards [hg] with θ hθ
  exact (mem_genericSet_iff_maximallyProjective hP θ).mp hθ

/-- A single infinite iid Gaussian Pauli disorder almost surely gives
maximally projective spectra for every open prefix of at least three sites. -/
theorem gaussian_path_all_prefixes_maximally_projective :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      MaximallyProjectiveEnergy (isSelfAdjoint_pathHamiltonian
        (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues := by
  apply ae_all_iff.mpr
  intro k
  have hg := (disorder_prefix_law (k+1)).quasiMeasurePreserving.ae (chain_spectrum_ae_gaussian k)
  filter_upwards [hg] with ω hω
  let u := pathPauliDisorderShell ω (k+1)
  let θ := fun i => u (pathCoeffEquiv (k+1) i)
  let e := qubitConfigFin (k+3)
  let M := spectralEnsembleMatrix (chainPauliFin (k+3)) θ
  have hM : M.IsHermitian := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian _) θ
  have hm : ∃ hh : (Matrix.reindex e.symm e.symm M).IsHermitian,
      MaximallyProjectiveEnergy hh.eigenvalues :=
    ⟨hM.reindex e.symm,Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv e.symm hM hω⟩
  have he : Matrix.reindex e.symm e.symm M = pathHamiltonian u := by
    have hh : Matrix.reindex e e (pathHamiltonian u) = M := reindex_pathHamiltonian u
    rw [← hh]
    ext x y
    simp [Matrix.reindex_apply]
  rw [he] at hm
  exact hm.choose_spec

#print axioms gaussian_path_all_prefixes_maximally_projective
end
end GaloisForLFunctions.HTGeometry
