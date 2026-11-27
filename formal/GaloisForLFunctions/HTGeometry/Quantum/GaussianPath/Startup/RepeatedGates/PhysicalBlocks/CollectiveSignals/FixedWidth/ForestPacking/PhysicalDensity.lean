import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.ForestPacking.QuarticCost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.GuardedFamily

/-! # Fourth-power density of repeated calls on one frozen Gaussian chain -/
open MeasureTheory Filter Set Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- A positive density of fixed-width triples forces order K t⁴
nonmerging gate calls at every time 0<t≤1. The same boxes witness
the entire interval on every sufficiently large prefix. -/
theorem gaussian_fourth_power_repeats :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Ioc (0:ℝ) 1,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4 →
        c*((n+1:ℕ):ℝ)*t^4≤(redundant (circuitWord C):ℝ)+1 := by
  classical
  obtain ⟨c,hc,hw⟩ := gaussian_guarded_family
  refine ⟨c/(2^4*514),by positivity,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro t ht C z hz he
  obtain ⟨F,e,f,hcard,hadj,hdis,hcal⟩ := hn
  have h := fixed_triples_fourth_power e f hadj (pathPauliDisorderShell ω n) C ht z hz he hdis hcal
  rw [Fintype.card_coe] at h
  have hsin := pow_le_pow_left₀ (half_pos ht.1).le (short_sine ht) 4
  have hcost := mul_le_mul hcard hsin (pow_nonneg (half_pos ht.1).le 4) (Nat.cast_nonneg F.card)
  linarith only [h,hcost]

#print axioms gaussian_fourth_power_repeats
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
