import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.IndependentCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.FirstEntry

/-! # The independent spectral ratios at a prescribed first scalar return -/

open Set Filter MeasureTheory Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
open EntrySensitivity.PrescribedCharacters PrecisionReturns FirstGate
noncomputable section

private def angularScale (r : ℝ) (q : ℤ) : ℂ := -Complex.I*((2*π*((q:ℝ)+r):ℝ):ℂ)

private theorem sorted_ratios (K : Type) [Field K] [Countable K] [Algebra K ℂ] (r : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let x := fun i => u (pathCoeffEquiv (k+1) i)
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
      ∀ (i j : Fin (2^N)) (q : ℤ), i≠j → angularScale r q≠0 →
        AlgebraicIndependent K (fun l : Outside i j => Complex.exp
          (angularScale r q*(((E l.val-E j)/(E i-E j):ℝ):ℂ))) := by
  let N := k+3
  let hP := chainPauliFin_isHermitian N
  let m := Fintype.card (ChainLabel N)
  have H (i j : Fin (2^N)) (q : ℤ) : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), i≠j → angularScale r q≠0 →
      let E := sortedEnsembleSpectrum hP x
      AlgebraicIndependent K (fun l : Outside i j => Complex.exp
        (angularScale r q*(((E l.val-E j)/(E i-E j):ℝ):ℂ))) := by
    by_cases hij : i=j
    · exact .of_forall fun _ h => False.elim (h hij)
    by_cases hc : angularScale r q=0
    · exact .of_forall fun _ _ h => False.elim (h hc)
    have hs : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP x).eigenvalues :=
      ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
    filter_upwards [ae_independent_normalized_phases K hP (chainPauliFin_spectrumEscapesRealRelations k) i j hij hc,
      hs] with x hx hh
    exact fun _ _ => hx hh.injective
  have hg : centredProductGaussian (Fin m) 1 ≪ volume := productGaussian_absolutelyContinuous _ one_ne_zero _
  exact (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (hg.ae_le
    (ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr (H i j)))

/-- At the first scalar entry of any prescribed physical error, all
eigenphase ratios except for the two closing levels provide D−2
algebraically independent values. All positive outside origins are allowed. -/
theorem gaussian_first_scalar_independent_ratios (K : Type) [Field K] [Countable K] [Algebra K ℂ]
    (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      ∀ a > (0:ℝ), ε<orbitCircuitDistance H 0 a → let v := firstVisit H a 0 ε
        ∃ i j : Fin N → Bool, i≠j ∧
          (∃ q : ℤ, v*(E i-E j)=2*π*((q:ℝ)+SharpOccupation.physicalArc ε)) ∧ AlgebraicIndependent K
          (fun l : Outside i j => anchorPhase E l.val v/anchorPhase E j v) := by
  let r := SharpOccupation.physicalArc ε
  filter_upwards [ae_all_iff.mpr (sorted_ratios K r),gaussian_path_all_prefixes_maximally_projective,
    gaussian_first_entry_character ∅ countable_empty ε hε hs] with ω hω hmax hentry k
  intro N H E a ha hout v
  obtain ⟨i,j,hij,⟨q,hq⟩,_⟩ := hentry k a ha hout
  obtain ⟨p,hp⟩ := physical_sorted_order k ω (hmax k).injective
  let x := fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  let S := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) x
  change ∀ l, E l=S (p l) at hp
  have hg : E i-E j≠0 := sub_ne_zero.mpr ((hmax k).injective.ne hij)
  have hpv : 0<v := ha.trans (first_empty_entry_of_outside H hε hs hout).1
  have hval : v*(E i-E j)=2*π*((q:ℝ)+r) := hq
  have hc : angularScale r q≠0 := by
    unfold angularScale
    rw [←hval]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (mul_ne_zero hpv.ne' hg))
  let f (l : Outside i j) : Outside (p i) (p j) := ⟨p l.val,p.injective.ne l.property.1,p.injective.ne l.property.2⟩
  have hf : Function.Injective f := fun u v h => Subtype.ext (p.injective (congrArg Subtype.val h))
  have hi := (hω k (p i) (p j) q (p.injective.ne hij) hc).comp f hf
  refine ⟨i,j,hij,⟨q,hval⟩,?_⟩
  convert hi using 1
  funext l
  change anchorPhase E l.val v/anchorPhase E j v=Complex.exp (angularScale r q*(((S (p l.val)-S (p j))/(S (p i)-S (p j)):ℝ):ℂ))
  rw [←hp l.val,←hp i,←hp j,anchorPhase,anchorPhase,←Complex.exp_sub]
  congr 1
  dsimp only [angularScale]
  rw [←hval]
  push_cast
  have hgc : (E i:ℂ)-(E j:ℂ)≠0 := by exact_mod_cast hg
  field_simp [hgc]
  ring

#print axioms gaussian_first_scalar_independent_ratios
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
