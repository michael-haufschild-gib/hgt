import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.PhysicalPhases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.SpectralCoordinates.OrbitFunctions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FiniteTransitions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.PhysicalContacts
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-! # Arithmetic of genuine circuit-distance transitions on the frozen chain -/

open Matrix Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
open PhaseBoundary.FiniteCertificates PhaseBoundary.FiniteCertificates.SpectralCoordinates
open PrecisionReturns
noncomputable section

private theorem physical_field (k : ℕ) (ω : PathPauliDisorder) :
    let N := k+3
    let u := pathPauliDisorderShell ω (k+1)
    let H : selfAdjoint (Square (Bits N)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let F := complexParameterField (fun j => u (pathCoeffEquiv (k+1) j))
    let K := algebraicClosure F ℂ
    Complex.I∈K ∧ EntriesIn K H.val ∧ ∀ j, (H.2.isHermitian.eigenvalues j:ℂ)∈K := by
  intro N u H F K
  have hi : Complex.I∈K := mem_algebraicClosure_iff.mpr (GaloisForLFunctions.RHTower.isAlgebraic_I.tower_top F)
  have hx (a) : ((u (pathCoeffEquiv (k+1) a):ℝ):ℂ)∈K := K.algebraMap_mem
    ⟨_,IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self a)⟩
  have hM : EntriesIn K H.val := by
    intro i j
    let e := qubitConfigFin N
    have h := congrFun (congrFun (reindex_pathHamiltonian u) (e i)) (e j)
    have he : H.val i j=spectralEnsembleMatrix (chainPauliFin N) (fun a => u (pathCoeffEquiv (k+1) a)) (e i) (e j) := by
      simpa only [Matrix.reindex_apply,Matrix.submatrix_apply,e,Equiv.symm_apply_apply] using h
    rw [he]
    exact pauli_entries_mem K hi N _ hx _ _
  refine ⟨hi,hM,fun j => mem_algebraicClosure_iff.mpr ?_⟩
  exact algebraic_matrix_root H.val (fun i l => mem_algebraicClosure_iff.mp (hM i l))
    (hermitianEigenvalue_matrixCharpolyRelation _ H.2.isHermitian j)

/-- At a nonzero date algebraic over the frozen couplings, a positive
level algebraic over those couplings cannot be entered or exited.
The tolerance and the gate budget can both be chosen after the draw. -/
theorem gaussian_algebraic_time_avoids_frontier :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let x := fun j => u (pathCoeffEquiv (k+1) j)
      let H : selfAdjoint (Square (Bits N)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ (s : ℕ) (ε t : ℝ), 0<ε → IsAlgebraic (complexParameterField x) (ε:ℂ) →
        t≠0 → IsAlgebraic (parameterField x) t → t∉frontier {w | orbitCircuitDistance H s w=ε} := by
  filter_upwards [gaussian_algebraic_time_phases,gaussian_path_all_prefixes_maximally_projective] with ω hw hmax k
  intro N u x H s ε t hε he ht hta hf
  let K := algebraicClosure (complexParameterField x) ℂ
  let R := K.toSubfield.comap Complex.ofRealHom
  let r : R := ⟨ε,mem_algebraicClosure_iff.mpr he⟩
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]; dsimp only [d]; omega))
  obtain ⟨B,hB,hcover⟩ := orbit_level_tests R.subtype e H s r hε
  obtain ⟨p,hp,hzero⟩ := hcover t hf
  obtain ⟨hi,hM,hE⟩ := physical_field k ω
  exact contact_dependent R.subtype e H K (fun a => a.property) hi hM hE (hmax k).injective p t hzero
    (hB p hp) (hw k (e.symm 0) t ht hta).algebraicClosure

/-- Both the first robust crossing from the identity and every first
positive- or zero-budget dip through P are transcendental over the
sampled coupling field. The two dates refer to the same excursion. -/
theorem gaussian_first_contact_dates_transcendental :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let x := fun j => u (pathCoeffEquiv (k+1) j)
      let H : selfAdjoint (Square (Bits N)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        Transcendental (parameterField x) σ ∧ ∀ s≤P, Transcendental (parameterField x) (firstVisit H σ s (1/10)) := by
  filter_upwards [gaussian_first_contact_equations,gaussian_algebraic_time_phases,
    gaussian_path_all_prefixes_maximally_projective] with ω hσ hf hmax
  filter_upwards [hσ] with k hk
  intro N u x H P
  obtain ⟨σ,hpos,hc,hprior,hcert⟩ := hk
  let d := 2^N-1
  let e : Bits N ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    have hn := Nat.two_pow_pos N
    simp only [Bits,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]; dsimp only [d]; omega))
  let K := algebraicClosure (complexParameterField x) ℂ
  obtain ⟨hi,hM,hE⟩ := physical_field k ω
  have hκ (r : ℚ) : ((Rat.castHom ℝ r:ℝ):ℂ)∈K := by simpa using K.ratCast_mem r
  have tr (v : ℝ) (hv : 0<v) (h : ∃ p : EntryPolynomial N ℚ, entryEval (Rat.castHom ℝ) (relativeOrbit e H v) p=0 ∧
      ∃ u, entryEval (Rat.castHom ℝ) (relativeOrbit e H u) p≠0) : Transcendental (parameterField x) v := by
    obtain ⟨p,hp,hn⟩ := h
    intro ha
    exact contact_dependent _ e H K hκ hi hM hE (hmax k).injective p v hp hn
      (hf k (e.symm 0) v hv.ne' ha).algebraicClosure
  exact ⟨σ,hpos,hc,hprior,tr σ hpos (hcert e).1,fun s hs => tr _ (hpos.trans_le
    (firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)).1.1) ((hcert e).2 s hs)⟩

#print axioms gaussian_algebraic_time_avoids_frontier
#print axioms gaussian_first_contact_dates_transcendental
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes

