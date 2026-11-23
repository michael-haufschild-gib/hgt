import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.Endpoints
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.FirstCell

/-! # First-return date from the integer tests on the normalized physical gaps -/
open Filter MeasureTheory Finset Set Real
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I]

/-- A cell can be tested beyond the observation origin by one comparison
of explicit finite extrema. -/
theorem qualifying_eq (θ : I→ℝ) (h : (rising θ).Nonempty) (cut : ℝ) {r : ℝ} (hr : 0≤r) :
    qualifying θ r cut={n : ℤ | max (lower θ h n r) (cut-n)≤upper θ h n r} := by
  ext n
  change (∃ z∈offsets θ n r, cut≤(n:ℝ)+z) ↔ _
  rw [offsets_eq_Icc θ h n hr]
  constructor
  · rintro ⟨z,hz,he⟩
    exact max_le (hz.1.trans hz.2) ((show cut-n≤z by linarith only [he]).trans hz.2)
  · intro hu
    exact ⟨_,⟨le_max_left ..,hu⟩,by linarith only [le_max_right (lower θ h n r) (cut-n)]⟩

/-- At fixed operator error, the first scalar return after the near-Hilbert
crossing is a finite-extremum formula at the least qualifying integer.
The arithmetic conditions involve only that same frozen spectrum. -/
theorem gaussian_first_return_formula :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ p q, w q < w p ∧ (∀ i, w q≤w i ∧ w i≤w p) ∧
          let W := w p-w q
          let θ := fun i => (w i-w q)/W
          ∃ h : (rising θ).Nonempty, ∀ ε∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ε
            let start (n : ℤ) := max (lower θ h n r) (σ*W-n)
            ∃ n : ℤ, IsLeast {m : ℤ | start m≤upper θ h m r} n ∧
              PrecisionReturns.firstVisit H σ 0 ε=((n:ℝ)+start n)/W := by
  filter_upwards [gaussian_first_return_cell] with ω hw
  filter_upwards [hw] with k hk
  intro N H P w
  obtain ⟨σ,hσ,hc,hb,p,q,he,hspan,hh⟩ := hk
  refine ⟨σ,hσ,hc,hb,p,q,he,hspan,?_⟩
  intro W θ
  have h : (rising θ).Nonempty := by
    refine ⟨(p,q),mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    change (w q-w q)/W < (w p-w q)/W
    rw [sub_self,zero_div,div_self (sub_pos.mpr he).ne']
    exact zero_lt_one
  refine ⟨h,?_⟩
  intro ε hε r start
  obtain ⟨n,hn,z,hz,hv⟩ := hh ε hε
  have hr := (physicalArc_spec hε.1 hε.2).1.1.le
  have hn' : IsLeast {m : ℤ | start m≤upper θ h m r} n := by
    rwa [←qualifying_eq θ h (σ*W) hr]
  have heq := offsets_eq_Icc θ h n hr
  have hstart : start n≤z := by
    have hm := hz.1.1
    rw [heq] at hm
    exact max_le hm.1 (by linarith only [hz.1.2])
  have hz' : z ≤ start n := hz.2 ⟨heq.symm ▸ (show start n∈Icc (lower θ h n r) (upper θ h n r) from
    ⟨le_max_left ..,hn'.1⟩),by linarith only [le_max_right (lower θ h n r) (σ*W-n)]⟩
  exact ⟨n,hn',le_antisymm hz' hstart ▸ hv⟩

#print axioms gaussian_first_return_formula
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
