import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.OrbitMaximum.Recovery
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactSynthesis.DimensionBounds.MaximumWindows
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Exact recovery of each frozen prefix's recurrent maximum from finite samples -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation DiagonalSynthesis.MultiplexedPhases
noncomputable section

/-- At every fixed positive tolerance, a deterministic sufficiently
large finite set of prime delays recovers the actual maximum on one
chain, eventually at every prefix. Both cutoffs precede the draw. -/
theorem frozen_prime_sample_maximum (r : ℕ→ℕ) (afterReturn : Bool) {ε : ℝ} (hε : 0<ε) :
    ∃ Q : ℕ→ℕ, ∀ S : ℕ→Finset Nat.Primes, (∀ k, Q k≤(S k).card) →
      ∃ T : ℕ→ℝ, ∀ t : ℕ→ℝ, (∀ᶠ k : ℕ in atTop, T k≤t k) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let n := k+1
        let u := pathPauliDisorderShell ω n
        let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
        let x := fun i => u (pathCoeffEquiv n i)
        let P := nearHilbertContinuousCircuitBudget (k+3)
        let σ := crossingOrigin n P (9/80) x
        let o := if afterReturn then σ+crossingWait n P (r k) x else σ
        ∃ m : ℕ, IsRecurrentOrbitCircuitMaximumAt H ε m ∧ ∀ j : ℕ,
          (∀ p : S k, pathGateDistance n j x (o+Real.log ((p.val:ℕ):ℝ)*t k)≤ε) ↔ m ≤ j := by
  classical
  let M (k : ℕ) := 35*(2^(k+3))^2
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  let o (k : ℕ) (x : PrefixIndex (k+1)→ℝ) :=
    let σ := crossingOrigin (k+1) (P k) (9/80) x
    if afterReturn then σ+crossingWait (k+1) (P k) (r k) x else σ
  let μ (k : ℕ) := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
  let B (k : ℕ) (S : Finset Nat.Primes) (t : ℝ) := {x | ∃ j ≤ M k, x∉orbitBudget (k+1) j ε ∧
    ∀ p : S, pathGateDistance (k+1) j x (o k x+Real.log ((p.val:ℕ):ℝ)*t)≤ε}
  let d (k : ℕ) := (1/2:ℝ)^k
  have cut (k : ℕ) : ∃ N, ∀ S : Finset Nat.Primes, N≤S.card →
      ∀ᶠ t : ℝ in atTop, (μ k).real (B k S t)<d k :=
    recover_budget_sublevels k (r k) (M k) ε afterReturn (pow_pos (by norm_num) k)
  choose Q hQ using cut
  refine ⟨Q,?_⟩
  intro S hS
  choose T hT using fun k => eventually_atTop.mp (hQ k (S k) (hS k))
  refine ⟨T,?_⟩
  intro t ht
  let X (k : ℕ) (ω : PathPauliDisorder) i := pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E (k : ℕ) := X k ⁻¹' B k (S k) (t k)
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hsum : Summable (fun k => pathPauliDisorderLaw.real (E k)) := by
    apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).of_norm_bounded_eventually_nat
    filter_upwards [ht] with k hk
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (ENNReal.toReal_mono (measure_ne_top (μ k) _)
      ((gaussian_pauli_prefix_coordinates_law (k+1)).measure_preimage_le (B k (S k) (t k)))).trans (hT k (t k) hk).le
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω∉E k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top pathPauliDisorderLaw _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [hgood] with ω hw
  filter_upwards [hw] with k hk
  intro n u H x _ σ _
  have hn : 2≤k+3 := by omega
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at hn H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  have hM : m ≤ M k := maximum_le_dimension_squared hn H hε.le hm
  refine ⟨m,hm,?_⟩
  intro j
  have he := orbitBudget_iff_maximum_le (s:=j) u ε hm
  constructor
  · intro fits
    by_contra! h
    exact hk ⟨j,h.le.trans hM,fun cap => (Nat.not_le.mpr h) (he.mp cap),fits⟩
  · intro hj p
    exact (he.mpr hj) _

#print axioms frozen_prime_sample_maximum
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
