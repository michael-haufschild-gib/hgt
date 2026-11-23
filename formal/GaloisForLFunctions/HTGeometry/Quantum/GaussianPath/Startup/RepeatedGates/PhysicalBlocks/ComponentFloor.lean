import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PhysicalFloor

/-! # Vanishing density of components for every circuit fitting the physical path -/
open MeasureTheory Set Filter GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Positive normalized overlap forces a sublinear number of connected
components in the circuit, even if any component uses arbitrarily many
gates and acts on spatially interleaved sites. -/
theorem gaussian_prescribed_components {a T η κ β : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | ∃ C : TwoQubitCircuit (n+2), 1+η*(n+1:ℕ) ≤ ((parts (circuitWord C)).card:ℝ) ∧
        κ ≤ ‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t))
          (choiVector C.eval.val)‖} ≤ β := by
  filter_upwards [gaussian_prescribed_cut_overlap (T:=T) ha hη hκ hβ] with n hn
  intro t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (hn t ht)
  rintro ω ⟨C,hparts,hfit⟩
  obtain ⟨cut,hcut⟩ := component_cut C
  have hc : ((parts (circuitWord C)).card:ℝ) ≤ ((SpanningDensity.crossed cut).card:ℝ)+1 := by exact_mod_cast hcut
  exact ⟨C,cut,by linarith only [hc,hparts],hfit⟩

#print axioms gaussian_prescribed_components

/-- In addition to the spanning cost, every two distinct wires touched
by nonmerging gates cost at least one more gate, up to an arbitrarily
small fraction of the path length. -/
theorem gaussian_prescribed_marked_floor {a T η ε β : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | ∃ C : TwoQubitCircuit (n+2), (C.gateCount:ℝ) ≤ (1-η)*(n+1:ℕ)+((marked (circuitWord C)).card:ℝ)/2 ∧
        ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤ε} ≤ β := by
  let κ := 1-ε^2/2
  have hκ : 0<κ := overlap_threshold_pos hε hε'
  filter_upwards [gaussian_prescribed_components (T:=T) ha hη hκ hβ] with n hn
  intro t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (hn t ht)
  rintro ω ⟨C,hcount,z,hz,he⟩
  have hm := mark_budget (circuitWord C)
  rw [Fintype.card_fin,circuitWord_length] at hm
  have hh : ((marked (circuitWord C)).card:ℝ)+2*(n+2:ℕ) ≤
      2*((C.gateCount:ℝ)+((parts (circuitWord C)).card:ℝ)) := by exact_mod_cast hm
  refine ⟨C,?_,overlap_of_fit _ _ (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) t)
    C.eval.property z hz he⟩
  push_cast at hh hcount ⊢
  linarith only [hh,hcount]

#print axioms gaussian_prescribed_marked_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
