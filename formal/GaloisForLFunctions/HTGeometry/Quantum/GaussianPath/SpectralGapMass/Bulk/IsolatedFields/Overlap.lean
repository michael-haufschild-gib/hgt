import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.TraceFactor

/-! # Trace overlap on almost isolated spins -/
open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- The field-replacement error scales with the square root of the
number of selected spins, while the reference overlap decays as a power. -/
theorem isolated_spin_overlap {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2)))
    (C : TwoQubitCircuit (n+2)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ i ∈ S, isolatedLongitudinalSite u 1 δ i)
    (hd : Disjoint S C.touchedSites) (t : ℝ) :
    ‖(C.eval.valᴴ*unitaryEvolution (pathHamiltonian u) t).trace‖/(2:ℝ)^(n+2) ≤
      |cos t|^S.card+|t|*δ*sqrt (21*S.card) := by
  let v := fieldReference u S
  let D := (2:ℝ)^(n+2)
  let tr (w : PathShell n) := (C.eval.valᴴ*unitaryEvolution (pathHamiltonian w) t).trace
  have he := sqrt_le_sqrt (fieldReference_energy u S hs)
  rw [sqrt_mul (show (0:ℝ) ≤ 21*S.card by positivity),sqrt_sq hδ] at he
  have h := (path_overlap_stability u v t C.eval).trans
    (mul_le_mul_of_nonneg_left he (show 0≤D*|t| by positivity))
  have hfactor := reference_overlap u C hd t
  change ‖tr v‖ ≤ D*|cos t|^S.card at hfactor
  change ‖tr u-tr v‖ ≤ D*|t|*(sqrt (21*S.card)*δ) at h
  rw [div_le_iff₀ (show 0 < D by positivity)]
  have ht := norm_sub_norm_le (tr u) (tr v)
  change ‖tr u‖ ≤ _
  nlinarith only [ht,h,hfactor]

#print axioms isolated_spin_overlap
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
