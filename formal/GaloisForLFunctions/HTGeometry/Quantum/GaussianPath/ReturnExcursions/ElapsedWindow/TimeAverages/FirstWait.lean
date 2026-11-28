import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.SelectedDates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.TimeAverages.CircuitPrice

/-! # The first wait bounded by explicit signed sums over replica pairs -/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes ShortWindows Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
noncomputable section

/-- For each candidate first-wait interval the base can select a Gaussian
observation window and spectral weights. All price terms are finite sums
of circuit diagonals, energies, local slopes and their Gaussian kernel. -/
theorem gaussian_first_wait_replica_bound {ι : Type*} [Fintype ι] (k P r : ℕ)
    (hr : r ≤ Fintype.card (Fin (k+3) → Bool)) {T L ρ W : ℝ}
    (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (hW : 0<W) (he : 17/80+ρ<3/4)
    (d : ℝ) (s : ι → ℕ) (A B p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    let n := k+1
    let R := firstRanks (Fin (k+3) → Bool) r hr
    let b := L/T
    let a := Real.sqrt (1-b^2)
    let τ := 1-(17/80+ρ+1/4)
    let dates (i : ι) := Icc (B i) (A i+2*d) ∩ Icc (-T) T
    let passes (g : Coeff n) := ∀ i, ∃ (m : ℝ) (V : ℝ≥0) (q : ℕ) (w : R → ℝ),
      (∀ j, w j ∈ Icc 0 W) ∧ ∑ j, w j=1 ∧
      averagedAffinePrice n (P+s i) g R w q a b m V <
        (gaussianReal m V).real (dates i)*(τ^(2*q)*p i)
    pathPauliDisorderLaw.real {ω | ∃ i, crossingWait n P (s i) (prefixPoint k ω) ∈ Icc (A i) (B i)} ≤
      pathPauliDisorderLaw.real {ω | crossingOrigin n P (9/80) (prefixPoint k ω) < d} +
      ((fieldLaw n).real {g | ¬ passes g} + (∑ i, p i) +
        4*Fintype.card (PathLabel n)*(r:ℝ)^2*W*L^2/(T*ρ)) := by
  classical
  intro n R b a τ dates passes
  have h := gaussian_selected_first_wait k P r hr hT hL hρ hW he d s A B p hp
  apply h.trans
  apply add_le_add le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro g hbad hpass
  apply hbad
  intro i
  obtain ⟨m,V,q,w,hw,hsum,hs⟩ := hpass i
  obtain ⟨t,hti,ht⟩ := date_of_averaged_price n (P+s i) g R w q a b m V
    (measurableSet_Icc.inter measurableSet_Icc) hs
  exact ⟨t,hti,q,w,hw,hsum,ht⟩

#print axioms gaussian_first_wait_replica_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
