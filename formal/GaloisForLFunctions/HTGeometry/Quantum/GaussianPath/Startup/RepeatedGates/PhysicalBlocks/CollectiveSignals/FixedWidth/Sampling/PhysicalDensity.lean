import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Families
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.ForestPacking.PhysicalDensity

/-! # Eighth-power density of repeated calls on one frozen Gaussian chain -/
open MeasureTheory Filter Set Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- A positive density of fixed-width triples forces order K t⁸
nonmerging gate calls at every time 0<t≤1. The same boxes witness
the entire interval on every sufficiently large prefix. -/
theorem gaussian_eighth_power_repeats :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Ioc (0:ℝ) 1,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4 →
        c*((n+1:ℕ):ℝ)*t^8≤(redundant (circuitWord C):ℝ)+1 := by
  obtain ⟨c,hc,hw⟩ := gaussian_fourth_power_repeats
  refine ⟨c,hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro t ht C z hz he
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.1.le ht.2 (by decide : 4≤8))
    (mul_nonneg hc.le (Nat.cast_nonneg _))).trans (hn t ht C z hz he)

#print axioms gaussian_eighth_power_repeats
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
