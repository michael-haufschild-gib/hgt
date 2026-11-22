import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.EntryAngle
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.MicroscopicFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PolynomialFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # A growing empty interval precedes every true physical scalar entry -/
open Matrix Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open SharpOccupation
noncomputable section

/-- Almost surely on all large prefixes, from every previous scalar visit
to the entry of any later component the elapsed time exceeds N^(1/48)/4. -/
theorem gaussian_physical_entry_gap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ ε ∈ Ioc (0:ℝ) (1/10), let E := visitSet H 0 ε
      ∀ v ∈ E, ∀ w ∈ E, v<w → (∃ δ : ℝ, 0<δ ∧ ∀ t ∈ Ioo (w-δ) w, t ∉ E) →
        (N:ℝ)^((48:ℝ)⁻¹)/4 < w-v := by
  obtain ⟨A,c,hA,hc,hl⟩ := gaussian_pauli_polynomial_interval_cost_floor
  filter_upwards [hl,gaussian_microscopic_scalar_floor A hA] with ω hl hs
  filter_upwards [hl,hs] with n hl hs
  intro N H ε hε E v hv w hw hvw hgap
  have weaken (u : ℝ) (hu : u ∈ E) : HasProjectiveCircuitApproximation N (1/10) 0 (unitaryEvolution H.val u) := by
    obtain ⟨z,hz,D,hD,he⟩ := hu
    exact ⟨z,hz,D,hD,he.trans hε.2⟩
  by_contra! hshort
  by_cases ht : A/(N:ℝ) ≤ w-v
  · have h := (hl (w-v) ht hshort).2 v 0 0 (weaken v hv) (by rw [show v+(w-v)=w by ring]; exact weaken w hw)
    have hp : 0<c*sqrt (N:ℝ) := mul_pos hc (sqrt_pos.mpr (by dsimp only [N]; positivity))
    exact hp.not_ge (by simpa only [Nat.cast_zero,add_zero] using h)
  · have angle := entry_angle H hε hvw hv hw hgap
    have hh := hs (w-v) (sub_pos.mpr hvw) (le_of_not_ge ht) angle
    have hfit := affordable_add_time H (weaken w hw) ((weaken v hv).neg_time H)
    rw [show (1/10:ℝ)+1/10=1/5 by norm_num,←sub_eq_add_neg] at hfit
    exact hh.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hfit)

#print axioms gaussian_physical_entry_gap
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
