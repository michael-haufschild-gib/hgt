import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.UniformMarks

/-! # Every nonmerging call adds a gate to the physical spanning floor -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback SpanningDensity.FixedHorizon
noncomputable section

/-- On a bounded positive time interval, every fitting circuit needs
at least one full gate per nonmerging call in addition to its asymptotic
spanning cost, including calls revisiting previously marked endpoints. -/
theorem gaussian_uniform_repeat_floor {a T η ε : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
      ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤ε →
      (1-η)*(n+1:ℕ)+(redundant (circuitWord C):ℝ) < (C.gateCount:ℝ) := by
  filter_upwards [gaussian_uniform_cut_overlap (T:=T) ha hη (overlap_threshold_pos hε hε')] with ω hw
  filter_upwards [hw] with n hn
  intro t ht C z hz he
  obtain ⟨cut,hcut⟩ := component_cut C
  have hl : ((SpanningDensity.crossed cut).card:ℝ)<η*(n+1:ℕ) :=
    lt_of_not_ge fun h => hn t ht ⟨C,cut,h,overlap_of_fit _ _ (unitaryEvolution_mem_unitary
      (isSelfAdjoint_pathHamiltonian _) t) C.eval.property z hz he⟩
  have hc : ((parts (circuitWord C)).card:ℝ)≤((SpanningDensity.crossed cut).card:ℝ)+1 := by
    exact_mod_cast hcut
  have hm := repeat_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  have hh : ((n+2:ℕ):ℝ)+(redundant (circuitWord C):ℝ)≤
      (C.gateCount:ℝ)+((parts (circuitWord C)).card:ℝ) := by exact_mod_cast hm
  push_cast at hl hh ⊢
  linarith only [hl,hc,hh]

#print axioms gaussian_uniform_repeat_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
