import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.MeasurableWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.FirstWindow

/-! # First affordable windows from the distinguished physical crossing -/

open Set Real MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals PrescribedTimes ShortWindows PrecisionReturns
noncomputable section

/-- The error can be chosen before the disorder. From the first near-Hilbert
crossing, the first actual visit at that error is followed, within D⁻ᵇ
in log waiting time, by the center of a same-error affordable interval.
Every budget is tested at its own first visit. -/
theorem gaussian_prescribed_first_window (b : ℕ) :
    ∀ᵐ e : ℝ ∂volume, 0 < e → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α ≤ 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        let σ := crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget N) (9/80) (prefixPoint k ω)
        ∀ s : ℕ, let v := firstVisit H σ s e
          ∃ w ≥ v, 1+(w-σ) ≤ (1+(v-σ))*exp (1/(2:ℝ)^(b*N)) ∧
            ∀ t : ℝ, |t-w| ≤ (2:ℝ)^(γ*(N:ℝ)) →
              HasProjectiveCircuitApproximation N e (s+⌊(2:ℝ)^(α*(N:ℝ))⌋₊) (unitaryEvolution H.val t) := by
  obtain ⟨C,hC⟩ := gaussian_first_return_window b
  let a (k : ℕ) (ω : PathPauliDisorder) :=
    crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (9/80) (prefixPoint k ω)
  have ha (k : ℕ) : Measurable (a k) :=
    (measurable_crossingOrigin ..).comp (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  have hh := prescribed_interval_clearance (fun k _ => a k) (fun k _ => ha k)
    (fun k => logMesh (k+3) b) (fun k => (C+b+2)*(k+3))
  filter_upwards [hh] with e hgood he
  filter_upwards [hC,hgood] with ω hchain hr
  exact (hchain (fun k => a k ω)).2 e he hr

#print axioms gaussian_prescribed_first_window
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
