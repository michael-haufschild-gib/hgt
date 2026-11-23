import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.FiniteSchedules.PhysicalTransport
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance

/-! # A tolerance chosen before the draw on an orbit-selected observation -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
open MaximumIntervals PrescribedTimes ShortWindows
noncomputable section

private theorem measurable_at_date (v : PathPauliDisorder → ℝ) (hv : Measurable v) (k s : ℕ) :
    Measurable fun ω => orbitCircuitDistance (chainGenerator ω k) s (v ω) := by
  let n := k+1
  have h := (continuous_distance n s).measurable.comp
    ((gaussian_pauli_prefix_coordinates_law n).measurable.prodMk hv)
  have he (ω : PathPauliDisorder) : orbitCircuitDistance (chainGenerator ω k) s (v ω) =
      pathGateDistance n s (prefixPoint k ω) (v ω) := by
    unfold pathGateDistance orbitCircuitDistance chainGenerator
    rw [show numberedGenerator n (prefixPoint k ω)=pathHamiltonian (pathPauliDisorderShell ω n)
      from numberedGenerator_shell _]
  simpa only [he] using h

/-- The observation can start at any prescribed sequence of measurable
stopping times, including the first robust crossings. At almost every
fixed accuracy, transporting a fit incurs only the stated additional
cost throughout an exponential window on almost every frozen chain. -/
theorem gaussian_prescribed_transport (a : ℕ → PathPauliDisorder → ℝ) (ha : ∀ k, Measurable (a k)) :
    ∀ᵐ e : ℝ ∂volume, 0 < e → ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ C : ℕ, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H := chainGenerator ω k
      let I := Icc (a k ω) (a k ω+(2:ℝ)^N)
      ∀ v ∈ I, ∀ w ∈ I, ∀ s : ℕ, HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val v) →
        ∃ j : ℕ, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val w) ∧
          (j:ℝ) ≤ (s:ℝ)+(N:ℝ)*(4+|w-v|)*2^(5*(C*N).sqrt+17) := by
  let g (ω : PathPauliDisorder) := scheduleHeight ω (fun k i => a k ω+(i:ℝ))
  have hg (k j) : Measurable (fun ω => g ω k j) := by
    by_cases hj : j=0
    · simpa only [g,scheduleHeight,if_pos hj] using (measurable_const : Measurable (fun _ : PathPauliDisorder => (0:ℝ)))
    · dsimp only [g,scheduleHeight]
      simp only [if_neg hj]
      exact measurable_at_date _ ((ha k).add_const _) _ _
  filter_upwards [gaussian_regular_for_measurable_heights g hg] with e he hpos
  filter_upwards [he,gaussian_same_error_transport] with ω hω htrans
  exact (htrans (fun k => a k ω)).2 e hpos hω

#print axioms gaussian_prescribed_transport
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.FiniteSchedules
