import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.CapMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.OccupationBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.GaussianSector

/-! # Near-maximum occupation on the balanced Gaussian sector -/
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open PrescribedTimes SharpOccupation
noncomputable section

/-- An exp[-O(K log K)] Gaussian sector has same-error maximum between
the near-Hilbert cutoff and 213·2ᴷ. Long records lie above that maximum
divided by 13632(K+1) outside an exponentially small fraction in 2ᴷ. -/
theorem hierarchical_maximum_occupation :
    ∃ A> (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ b∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        A*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          ∃ m : ℕ, P < m ∧ m ≤ 213*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
            ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ s : ℕ, s*(64*(K+1))*213 ≤ m →
              visitFraction H s (1/10) a T < b^(2^K:ℕ) := by
  obtain ⟨a,ha,C,hC,hmass⟩ := hierarchical_cap_mass
  obtain ⟨b,hb,hcut⟩ := capped_path_occupation
  refine ⟨a*(1/10:ℝ)^9,mul_pos ha.1 (by norm_num),C,hC,b,hb,?_⟩
  filter_upwards [hcut,eventually_ge_atTop 1] with k hk hk₁
  intro n K P
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  let F := capEvent n (1/10)
  have hF := measurable_capEvent n (1/10)
  have hY := AccuracyScales.TenthPlateau.measurePreserving_pathDisorder_labels n
  have hm := hmass n (by dsimp only [n]; omega) (1/10) (by constructor <;> norm_num)
  refine ⟨Y ⁻¹' F,hF.preimage hY.measurable,hm.trans_eq
    (hY.measureReal_preimage hF.nullMeasurableSet).symm,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw
  intro he u H
  apply hk u (hw k) 213 (by decide)
  intro t
  have ht := (show (fun i => u (pathCoeffEquiv n i))∈JointSpeeds.orbitBudget n (213*2^K) (1/10) from he) t
  rw [pathGateDistance,numberedGenerator_shell] at ht
  rw [Nat.mul_comm 213 (2^K)] at ht
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr ht

#print axioms hierarchical_maximum_occupation
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
