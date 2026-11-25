import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # The first empty-circuit visit from a specified spectral antipode -/

open Set Filter MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open EmptyVisitFlux SharpOccupation
noncomputable section

private theorem enclosing_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (p : J → UnitAddCircle) (r : ℝ) : (p ∘ e) ∈ enclosingUnitArc r ↔ p ∈ enclosingUnitArc r := by
  constructor
  · intro h
    obtain ⟨b,hb⟩ := mem_iUnion.mp h
    apply mem_iUnion.mpr
    refine ⟨e b,fun j hj => ?_⟩
    simpa only [Function.comp_apply,e.apply_symm_apply] using
      hb (e.symm j) (fun he => hj (by rw [←he,e.apply_symm_apply]))
  · intro h
    obtain ⟨b,hb⟩ := mem_iUnion.mp h
    apply mem_iUnion.mpr
    refine ⟨e.symm b,fun j hj => ?_⟩
    simpa only [Function.comp_apply,e.apply_symm_apply] using
      hb (e j) (fun he => hj (e.apply_eq_iff_eq_symm_apply.mp he))

/-- The first physical visit can be read in any ordering of the energies. -/
theorem first_visit_iff_spectral_least {N : ℕ} {J : Type*} [Fintype J]
    (H : selfAdjoint (Register N)) (e : (Fin N → Bool) ≃ J) (E : J → ℝ)
    (he : ∀ j, H.2.isHermitian.eigenvalues j = E (e j))
    (a t : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) :
    PrecisionReturns.firstVisit H a 0 ε = t ↔
      IsLeast {v : ℝ | a≤v ∧ flow (fun l => -E l/(2*π)) v ∈ enclosingUnitArc (physicalArc ε)} t := by
  have hset : PrecisionReturns.visitSet H a 0 ε =
      {v : ℝ | a≤v ∧ flow (fun l => -E l/(2*π)) v ∈ enclosingUnitArc (physicalArc ε)} := by
    ext v
    apply and_congr_right
    intro _
    change v∈SharpOccupation.visitSet H 0 ε ↔ _
    rw [←physical_visit H hε.1 hε.2 v]
    have hflow : flow (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) v =
        flow (fun l => -E l/(2*π)) v ∘ e := funext fun j => by simp only [flow,Function.comp_apply,he]
    rw [hflow,enclosing_reindex]
  rw [←hset]
  have hleast := PrecisionReturns.firstVisit_isLeast H a 0 hε.1
  exact ⟨fun h => h ▸ hleast,fun h => hleast.unique h⟩

/-- For every prefix and every chosen pair, the pair alone gives a
pathwise lower bound on the first physical wait from each antipode. -/
theorem gaussian_first_empty_wait_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ i j : Level k, j < i →
      ∀ ε ∈ Ioo (0:ℝ) (sqrt 2), ∀ n : ℕ,
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (fun l => u (pathCoeffEquiv (k+1) l))
      let a := pairDate (fun l => -E l) j i (1/2) n
      2*π*(1/2-physicalArc ε) ≤ (PrecisionReturns.firstVisit H a 0 ε-a)*(E i-E j) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k i j hij ε hε n u H E a
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hω k).injective
  have hsorted : Function.Injective E := by
    intro b c h
    apply e.symm.injective
    apply (hω k).injective
    rw [he,he,e.apply_symm_apply,e.apply_symm_apply]
    exact h
  have hE : E j<E i := lt_of_le_of_ne (monotone_sortedTuple _ hij.le) (hsorted.ne hij.ne)
  let r : Ioo (0:ℝ) (1/2) := ⟨physicalArc ε,(physicalArc_spec hε.1 hε.2).1⟩
  obtain ⟨ht,hfloor,_⟩ := antipodal_first_iff E i j hE r n
  have hv := ((first_visit_iff_spectral_least H e E he a _ hε).mp (Eq.refl (PrecisionReturns.firstVisit H a 0 ε))).1
  exact ht ▸ mul_le_mul_of_nonneg_right (sub_le_sub_right (hfloor hv) a) (sub_nonneg.mpr hE.le)

/-- Starting at the nth antipode of a specified ordered energy pair,
the probability that the first physical zero-gate visit attains the
earliest pair-allowed date tends to x^(2^N−2), x=2 arcsin(ε/2)/π.
The Hamiltonian is held fixed between these two random dates. -/
theorem gaussian_first_empty_visit_at_pair_minimum (k : ℕ) {i j : Level k} (hij : j < i)
    {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) :
    let r := physicalArc ε
    Tendsto (fun n : ℕ => pathPauliDisorderLaw {ω |
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (fun l => u (pathCoeffEquiv (k+1) l))
      let a := pairDate (fun l => -E l) j i (1/2) n
      PrecisionReturns.firstVisit H a 0 ε = pairDate (fun l => -E l) j i r n}) atTop
        (𝓝 (ENNReal.ofReal r^(2^(k+3)-2))) := by
  intro r
  let rr : Ioo (0:ℝ) (1/2) := ⟨r,(physicalArc_spec hε.1 hε.2).1⟩
  let X (ω : PathPauliDisorder) : Coupling k := fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  let G := centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1
  have hp : MeasurePreserving X pathPauliDisorderLaw G := gaussian_pauli_prefix_coordinates_law (k+1)
  have hs : ∀ᵐ x ∂G, Function.Injective (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) := by
    apply (productGaussian_absolutelyContinuous _ one_ne_zero _).ae_le
    exact (ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)).mono fun _ hx =>
      injective_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) hx.injective
  apply (gaussian_single_winding_entry k hij rr).congr
  intro n
  let T := 2*π*(1-r+(n:ℝ))
  let B := {x | finiteClockPhasePoint (gapFrequency k i j x) T ∈ closedBox (Outside i j) r}
  have hB : MeasurableSet B := (isClosed_set_pi (fun _ _ => isClosed_forwardUnitArc r)).measurableSet.preimage
    (measurable_gap_point k i j T)
  trans G B
  · apply measure_congr
    filter_upwards [hs] with x hx
    apply propext
    have hb := box_iff_face k hij r n x hx
    exact ⟨fun h => hb.mp h.2,fun h => ⟨(entry_iff_closed_face _ rr.2.1.le rr.2.2).mpr ⟨j,i,hb.mpr h⟩,hb.mpr h⟩⟩
  rw [←hp.measure_preimage hB.nullMeasurableSet]
  apply measure_congr
  filter_upwards [hp.quasiMeasurePreserving.ae hs,gaussian_path_all_prefixes_maximally_projective] with ω hx hω
  let H : selfAdjoint (Register (k+3)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (X ω)
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hω k).injective
  have hE : E j < E i := lt_of_le_of_ne (monotone_sortedTuple _ hij.le) (hx.ne hij.ne)
  apply propext
  have ha := (antipodal_first_iff E i j hE rr n).2.2
  have hb := box_iff_face k hij r n (X ω) hx
  refine Iff.trans ?_ (first_visit_iff_spectral_least H e E he _ _ hε).symm
  exact ⟨fun h => ha.mpr ⟨(entry_iff_closed_face _ rr.2.1.le rr.2.2).mpr ⟨j,i,hb.mpr h⟩,hb.mpr h⟩,
    fun h => hb.mp (ha.mp h).2⟩

#print axioms gaussian_first_empty_wait_floor
#print axioms gaussian_first_empty_visit_at_pair_minimum
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
