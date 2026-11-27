import GaloisForLFunctions.HTGeometry.PauliChainDephasing
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon

/-! # Gaussian avoidance of prescribed real spectral relations -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open private path_energy_permutation from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
noncomputable section

/-- A prescribed nonzero balanced real relation fails in every labeling
of the Gaussian spectrum. The product over permutations is a nonzero
polynomial in the physical Pauli coefficients. -/
theorem real_mode_avoidance (k : ℕ) (c : Fin (2^(k+3))→ℝ) (hc : ∑ i, c i=0) (hn : c≠0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let u := pathPauliDisorderShell ω (k+1)
      let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
      ∀ e : Fin (2^(k+3)) ≃ (Fin (k+3)→Bool), ∑ j, c j*E (e j) ≠ 0 := by
  classical
  let I := Fin (Fintype.card (ChainLabel (k+3)))
  let hP := chainPauliFin_isHermitian (k+3)
  let E (x : I→ℝ) := (isHermitian_spectralEnsembleMatrix hP x).eigenvalues
  obtain ⟨G,hG⟩ := exists_shellPoly_jointActionDefectProduct hP c 0
  have hprod (x : I→ℝ) : MvPolynomial.eval x G =
      ∏ π : Equiv.Perm (Fin (2^(k+3))), (∑ j, c j*E x (π j))^2 := by
    rw [hG,eval_jointActionDefectProduct]
    simp only [zero_pow (by decide : 2≠0),zero_mul,sub_zero,E]
  obtain ⟨v,hv⟩ := exists_shell_energy_witness_pauliChain k c hc hn 0
  have hnG : G≠0 := by
    intro he
    have hh := hprod v
    rw [he,map_zero] at hh
    apply Finset.prod_ne_zero_iff.mpr _ hh.symm
    intro π _
    simpa only [zero_mul] using hv π
  let μ := Measure.pi fun _ : I => gaussianReal 0 1
  have hac : μ ≪ volume := by
    rw [volume_pi]
    exact pi_absolutelyContinuous_pi _ _ _ fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hgood : ∀ᵐ x ∂μ, MvPolynomial.eval x G≠0 :=
    ae_iff.mpr (by simpa only [not_not] using hac (realMvPolynomial_zero_set_volume_fin _ G hnG))
  have hX := gaussian_pauli_prefix_coordinates_law (k+1)
  filter_upwards [hX.quasiMeasurePreserving.ae hgood,gaussian_path_all_prefixes_maximally_projective] with ω hw hi
  intro u Ep e
  let x := fun i => u (pathCoeffEquiv (k+1) i)
  change MvPolynomial.eval x G≠0 at hw
  rw [hprod] at hw
  obtain ⟨σ,hσ⟩ := path_energy_permutation k ω (hi k).injective
  change E x ∘ σ = Ep ∘ (qubitConfigFin (k+3)).symm at hσ
  let π := (e.trans (qubitConfigFin (k+3))).trans σ
  have he (j) : E x (π j)=Ep (e j) := by
    simpa only [π,Equiv.trans_apply,Function.comp_apply,Equiv.symm_apply_apply] using
      congrFun hσ (qubitConfigFin (k+3) (e j))
  intro hz
  exact Finset.prod_ne_zero_iff.mp hw π (Finset.mem_univ _) (by simp only [he,hz,zero_pow (by decide : 2≠0)])

#print axioms real_mode_avoidance
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
