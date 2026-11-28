import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.EventPrices

/-! # A physical shortcut bound in terms of local-expectation collisions -/

open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section

/-- Each scheduled date uses its own circuit twists, replica order, and
distribution of weights on the top ranks. The spectral comparison error is
paid once. Capping each weight by W gives a cost proportional to W r². -/
theorem physical_schedule_twist_tail {ι : Type*} [Fintype ι] (n r : ℕ)
    (hr : r ≤ Fintype.card (Fin (n+2) → Bool)) {T L ρ W : ℝ}
    (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (hW : 0<W)
    (s : ι → ℕ) (ε t p : ι → ℝ) (ht : ∀ i, |t i| ≤ T)
    (hε : ∀ i, ε i+ρ<3/4) (hp : ∀ i, 0 ≤ p i) :
    let R := firstRanks (Fin (n+2) → Bool) r hr
    let b := L/T
    let a := Real.sqrt (1-b^2)
    let τ (i : ι) := 1-(ε i+ρ+1/4)
    let passes (h : Coeff n) := ∀ i, ∃ (q : ℕ) (w : R → ℝ),
      (∀ j, w j∈Icc 0 W) ∧ ∑ j, w j=1 ∧ affineTracePrice n (s i) h R w q a b (t i) ≤ τ i^(2*q)*p i
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      (⋃ i, BlockDilations.affordableDraw n (s i) (ε i) (t i))) ≤
      (fieldLaw n).real {h | ¬passes h} + (∑ i, p i) +
        4*Fintype.card (PathLabel n)*(r:ℝ)^2*W*L^2/(T*ρ) := by
  have h := physical_event_twist_tail n r hr hT hL hρ hW s ε p
    (fun i => BlockDilations.affordableDraw n (s i) (ε i) (t i)) (fun i => {t i})
    (fun i => BlockDilations.measurable_affordableDraw ..)
    (fun i v hv => by rw [Set.mem_singleton_iff.mp hv]; exact ht i)
    (fun i v hv => by rw [Set.mem_singleton_iff.mp hv]) hε hp
  simpa only [Set.mem_singleton_iff,exists_eq_left] using h

#print axioms physical_schedule_twist_tail
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
