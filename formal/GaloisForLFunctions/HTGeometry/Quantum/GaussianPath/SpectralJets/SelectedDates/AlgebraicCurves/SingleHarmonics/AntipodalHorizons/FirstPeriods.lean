import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.PhysicalWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.WindowLaw

/-! # Finite-window bound for the first physical wait from an extremal antipode -/

open Set MeasureTheory Filter Real Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- Elapsed time to the first zero-gate visit from the specified antipode,
in periods of the physical spectral width. -/
def firstPeriods (k n : ℕ) (ε : ℝ) (ω : PathPauliDisorder) : ℝ :=
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (fun l => u (pathCoeffEquiv (k+1) l))
  let a := date E (topLevel k) 0 n 0
  (PrecisionReturns.firstVisit H a 0 ε-a)*((E (topLevel k)-E 0)/(2*π))

/-- A short actual first wait forces a scalar hit in the corresponding
continuous interval of the sorted spectrum, on the original Gaussian law. -/
theorem first_wait_measure_le (k n : ℕ) {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2)) (L : ℝ) :
    pathPauliDisorderLaw {ω | firstPeriods k n ε ω ≤ L} ≤
      (centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1)
        (windowHit k n L (physicalArc ε)) := by
  let X (ω : PathPauliDisorder) : Coupling k := fun l =>
    pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  apply le_trans _ ((gaussian_pauli_prefix_coordinates_law (k+1)).measure_preimage_le _)
  apply measure_mono_ae
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω hshort
  let H : selfAdjoint (Register (k+3)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (X ω)
  let i := topLevel k
  let j : Level k := 0
  let a := date E i j n 0
  let v := PrecisionReturns.firstVisit H a 0 ε
  let s := firstPeriods k n ε ω
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hω k).injective
  have hsorted : Function.Injective E := by
    intro b c h
    apply e.symm.injective
    apply (hω k).injective
    rw [he,he,e.apply_symm_apply,e.apply_symm_apply]
    exact h
  have hji : j < i := top_pos k
  have hg : 0 < E i-E j := sub_pos.mpr (lt_of_le_of_ne (monotone_sortedTuple _ hji.le) (hsorted.ne hji.ne))
  have hvisit := ((first_visit_iff_spectral_least H e E he a v hε).mp rfl).1
  have hpos : 0 ≤ s := mul_nonneg (sub_nonneg.mpr hvisit.1) (div_nonneg hg.le two_pi_pos.le)
  refine ⟨s,⟨hpos,hshort⟩,?_⟩
  have hdate : date E i j n s=v := by
    have hstep : date E i j n s=a+s*(2*π/(E i-E j)) := by
      dsimp only [a,date]
      ring
    have hcancel : ((E i-E j)/(2*π))*(2*π/(E i-E j))=1 := by
      field_simp [hg.ne',two_pi_pos.ne']
    rw [hstep]
    change a+((v-a)*((E i-E j)/(2*π)))*(2*π/(E i-E j))=v
    rw [mul_assoc,hcancel,mul_one]
    abel
  rw [hdate]
  exact hvisit.2

#print axioms first_wait_measure_le
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
