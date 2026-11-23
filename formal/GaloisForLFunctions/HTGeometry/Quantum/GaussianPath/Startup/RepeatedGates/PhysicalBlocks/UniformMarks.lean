import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap

/-! # Gate charges for nonmerging endpoints throughout a physical interval -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal SpanningDensity.FixedHorizon
noncomputable section

/-- A gate acting inside one previously connected component marks its
endpoints. Every two marked wires add a gate to the spanning floor. -/
theorem gaussian_uniform_marked_floor {a T η ε : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
      ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤ε →
      (1-η)*(n+1:ℕ)+((marked (circuitWord C)).card:ℝ)/2 < (C.gateCount:ℝ) := by
  filter_upwards [gaussian_uniform_cut_overlap (T:=T) ha hη (overlap_threshold_pos hε hε')] with ω hw
  filter_upwards [hw] with n hn
  intro t ht C z hz he
  obtain ⟨cut,hcut⟩ := component_cut C
  have hl : ((SpanningDensity.crossed cut).card:ℝ) < η*(n+1:ℕ) := by
    apply lt_of_not_ge
    intro h
    exact hn t ht ⟨C,cut,h,overlap_of_fit _ _ (unitaryEvolution_mem_unitary
      (isSelfAdjoint_pathHamiltonian _) t) C.eval.property z hz he⟩
  have hc : ((parts (circuitWord C)).card:ℝ) ≤ ((SpanningDensity.crossed cut).card:ℝ)+1 := by
    exact_mod_cast hcut
  have hm := mark_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  have hh : ((marked (circuitWord C)).card:ℝ)+2*(n+2:ℕ) ≤
      2*((C.gateCount:ℝ)+((parts (circuitWord C)).card:ℝ)) := by exact_mod_cast hm
  push_cast at hl hh ⊢
  linarith only [hl,hc,hh]

#print axioms gaussian_uniform_marked_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
