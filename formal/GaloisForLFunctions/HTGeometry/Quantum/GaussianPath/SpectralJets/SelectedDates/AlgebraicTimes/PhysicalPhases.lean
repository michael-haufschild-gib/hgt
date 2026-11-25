import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.SpectralParameters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Relative phase rank at all dates algebraic over the frozen Gaussian couplings -/

open Set MeasureTheory Matrix Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
open ExactContacts
noncomputable section

private theorem sorted_prefix (k : ℕ) : ∀ᵐ ω ∂pathPauliDisorderLaw, let N := k+3
    let x := fun j => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) j)
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
    ∀ b : Fin (2^N), ∀ t : ℝ, t≠0 → IsAlgebraic (parameterField x) t →
      AlgebraicIndependent (complexParameterField x) (fun i : {j // j≠b} => energyPhase (E i.val-E b) t) := by
  let N := k+3
  let P := chainPauliFin_isHermitian N
  let m := Fintype.card (ChainLabel N)
  have hm : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix P x).eigenvalues :=
    ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
  have hc : centredProductGaussian (Fin m) 1 ≪ volume := productGaussian_absolutelyContinuous _ one_ne_zero _
  apply (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
  apply hc.ae_le
  filter_upwards [hm,ae_all_iff.mpr (ae_sorted_algebraic_time_phases N)] with x hmax hx
  exact fun b => hx b hmax.injective (hmax.comp_equiv (Tuple.sort _))

/-- Almost surely on every prefix, all relative eigenphases at every
nonzero date algebraic over the sampled coupling field are algebraically
independent over that same field in the complex numbers. -/
theorem gaussian_algebraic_time_phases : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
    let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
    let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
    ∀ (b : Fin N → Bool) (t : ℝ), t≠0 → IsAlgebraic (parameterField x) t →
      AlgebraicIndependent (complexParameterField x)
        (fun i : {j // j≠b} => anchorPhase E i.val t/anchorPhase E b t) := by
  filter_upwards [ae_all_iff.mpr sorted_prefix,gaussian_path_all_prefixes_maximally_projective] with ω hω hm k
  intro N x E b t ht hta
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hm k).injective
  let S := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
  change ∀ j, E j=S (e j) at he
  let f (i : {j // j≠b}) : {j // j≠e b} := ⟨e i.val,e.injective.ne i.property⟩
  have hf : Function.Injective f := fun i j h => Subtype.ext (e.injective (congrArg Subtype.val h))
  have h := (hω k (e b) t ht hta).comp f hf
  convert h using 1
  funext i
  change anchorPhase E i.val t/anchorPhase E b t=energyPhase (S (e i.val)-S (e b)) t
  rw [←he,←he,anchorPhase,anchorPhase,←Complex.exp_sub,energyPhase]
  congr 1
  push_cast
  ring

#print axioms gaussian_algebraic_time_phases
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
