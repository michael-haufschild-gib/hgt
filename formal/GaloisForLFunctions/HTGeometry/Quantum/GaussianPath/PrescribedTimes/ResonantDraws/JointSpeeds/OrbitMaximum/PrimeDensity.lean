import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.OrbitMaximum.PrimeWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.MaximumCDF
import GaloisForLFunctions.HTGeometry.OnsetRecurrenceIndependence

/-! # Positive prime density of the true maximum at a fixed physical time scale -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open SharpOccupation
noncomputable section

/-- On every Pauli chain, for every fixed dilation h>0, a positive
fraction of the primes give the actual same-error maximum at o+h log p.
The prime cutoff and density bound are uniform in the origin o. -/
theorem maximum_on_positive_prime_fraction (n : ℕ) (u : PathShell n) {ε : ℝ} (hε : 0<ε) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let x := fun i => u (pathCoeffEquiv n i)
    ∃ m : ℕ, IsRecurrentOrbitCircuitMaximumAt H ε m ∧ ∀ h > (0:ℝ),
      ∃ c > (0:ℝ), ∀ᶠ X : ℝ in atTop, ∀ o : ℝ, ∃ S : Finset ℕ,
        c*(Nat.primeCounting ⌊X⌋₊:ℝ)≤S.card ∧ ∀ p∈S, p.Prime ∧ (p:ℝ)≤X ∧
          ∀ j : ℕ, pathGateDistance n j x (o+h*log (p:ℝ))≤ε ↔ m ≤ j := by
  intro H x
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by omega : 2≤n+2) H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  refine ⟨m,hm,?_⟩
  intro h hh
  obtain ⟨G,w,hG,hw,hr⟩ := hm.2
  let A := {v : ℝ | ∀ j : ℕ, pathGateDistance n j x v≤ε ↔ m ≤ j}
  have hrec (a : ℝ) : ∃ v ∈ Icc a (a+G), Icc v (v+w)⊆A := by
    obtain ⟨v,hv,hmax⟩ := hr a
    refine ⟨v,hv,?_⟩
    intro t ht j
    constructor
    · intro fit
      have he : HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H.val t) := by
        apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        rw [pathGateDistance,show numberedGenerator n x=H.val from numberedGenerator_shell u] at fit
        exact fit
      obtain ⟨z,hz,C,hC,hfit⟩ := he
      exact (hmax t ht z hz C hfit).trans hC
    · intro hj
      exact ((orbitBudget_iff_maximum_le u ε hm).mpr hj) t
  obtain ⟨c,hc,hcount⟩ := prime_count_in_recurrent_intervals A hG hw hh hrec
  refine ⟨c/2,half_pos hc,?_⟩
  have hratio := _root_.RHTower.tendsto_primeCounting_ratio.eventually_lt_const (by norm_num : (1:ℝ)<2)
  filter_upwards [hcount,hratio,eventually_gt_atTop (1:ℝ)] with X hX hπ hlarge
  intro o
  obtain ⟨S,hmass,hS⟩ := hX o
  have hpos := div_pos (zero_lt_one.trans hlarge) (log_pos hlarge)
  have hπ' := (div_lt_iff₀ hpos).mp hπ
  refine ⟨S,le_trans ?_ hmass,hS⟩
  calc c/2*(Nat.primeCounting ⌊X⌋₊:ℝ) ≤ c/2*(2*(X/log X)) :=
         mul_le_mul_of_nonneg_left hπ'.le (half_pos hc).le
       _ = _ := by ring

#print axioms maximum_on_positive_prime_fraction
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
