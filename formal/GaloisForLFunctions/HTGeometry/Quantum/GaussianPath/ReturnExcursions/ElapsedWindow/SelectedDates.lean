import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.InitialAscent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.EventPrices
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Choosing a spectral test date inside the reflected first ascent -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes ShortWindows Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- A first wait in [A,B] forces a physical fit at every date in
[B,A+2d] when the ascent lasts at least d. Each base field chooses its
own test date in each such interval. Early ascent and spectral error
are charged once across all budgets and intervals. -/
theorem gaussian_selected_first_wait {ι : Type*} [Fintype ι] (k P r : ℕ)
    (hr : r ≤ Fintype.card (Fin (k+3) → Bool)) {T L ρ W : ℝ}
    (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (hW : 0<W) (he : 17/80+ρ<3/4)
    (d : ℝ) (s : ι → ℕ) (A B p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    let n := k+1
    let R := firstRanks (Fin (k+3) → Bool) r hr
    let b := L/T
    let a := Real.sqrt (1-b^2)
    let τ := 1-(17/80+ρ+1/4)
    let dates (i : ι) := Icc (B i) (A i+2*d) ∩ Icc (-T) T
    let passes (g : Coeff n) := ∀ i, ∃ t ∈ dates i, ∃ (q : ℕ) (w : R → ℝ),
      (∀ j, w j ∈ Icc 0 W) ∧ ∑ j, w j=1 ∧
      affineTracePrice n (P+s i) g R w q a b t ≤ τ^(2*q)*p i
    pathPauliDisorderLaw.real {ω | ∃ i, crossingWait n P (s i) (prefixPoint k ω) ∈ Icc (A i) (B i)} ≤
      pathPauliDisorderLaw.real {ω | crossingOrigin n P (9/80) (prefixPoint k ω) < d} +
      ((fieldLaw n).real {g | ¬ passes g} + (∑ i, p i) +
        4*Fintype.card (PathLabel n)*(r:ℝ)^2*W*L^2/(T*ρ)) := by
  classical
  intro n R b a τ dates passes
  let x (g : Coeff n) (j : PrefixIndex n) := g (pathCoeffEquiv n j)
  have mx : Measurable x := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  let E (i : ι) : Set (Coeff n) := {g | crossingWait n P (s i) (x g) ∈ Icc (A i) (B i) ∧
    d ≤ crossingOrigin n P (9/80) (x g)}
  have mE (i : ι) : MeasurableSet (E i) := (((measurable_crossingWait n P (s i)).comp mx)
    measurableSet_Icc).inter (measurableSet_le measurable_const ((measurable_crossingOrigin ..).comp mx))
  have hfit (i : ι) (t : ℝ) (ht : t ∈ dates i) :
      E i ⊆ BlockDilations.affordableDraw n (P+s i) (17/80) t := by
    intro g hg
    have hw := reflected_initial_segment n P (s i) (x g) t
      ⟨hg.1.2.trans ht.1.1,by linarith only [ht.1.2,hg.1.1,hg.2]⟩
    unfold pathGateDistance at hw
    rw [show numberedGenerator n (x g)=pathHamiltonian (WithLp.toLp 2 g) from
      numberedGenerator_shell (WithLp.toLp 2 g)] at hw
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hw
  have hprice := physical_event_twist_tail n r hr hT hL hρ hW (fun i => P+s i)
    (fun _ => 17/80) p E dates mE (fun _ _ ht => abs_le.mpr ht.2) hfit (fun _ => he) hp
  let Y (ω : PathPauliDisorder) (l : PathLabel n) := pathPauliDisorderShell ω n l
  have hsub : {ω | ∃ i, crossingWait n P (s i) (prefixPoint k ω) ∈ Icc (A i) (B i)} ⊆
      {ω | crossingOrigin n P (9/80) (prefixPoint k ω)<d} ∪ Y ⁻¹' (⋃ i, E i) := by
    rintro ω ⟨i,hi⟩
    by_cases hc : crossingOrigin n P (9/80) (prefixPoint k ω)<d
    · exact Or.inl hc
    · exact Or.inr (mem_iUnion.mpr ⟨i,hi,le_of_not_gt hc⟩)
  exact (measureReal_mono hsub).trans ((measureReal_union_le ..).trans (add_le_add le_rfl hprice))

#print axioms gaussian_selected_first_wait
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
