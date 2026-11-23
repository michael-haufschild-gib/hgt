import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ScalarDistance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity

/-! # Time density of replays of an entire frozen trajectory -/
open Filter Set MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator ENNReal
namespace GaloisForLFunctions.HTGeometry.TrajectoryProfiles
open SharpOccupation
noncomputable section

/-- Translating all scalar visits by a fixed date preserves their density
from every origin. -/
theorem translated_scalar_fraction {N : ℕ} (H : selfAdjoint (Register N))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {η : ℝ} (hη : 0 < η) (hsmall : η < sqrt 2)
    (v : ℝ) : let S := (fun z : ℝ => z-v) ⁻¹' visitSet H 0 η
      MeasurableSet S ∧ ∀ a : ℝ, Tendsto (fun T : ℝ => volume.real (S ∩ Icc a T)/(T-a))
        atTop (𝓝 (((2^N:ℕ):ℝ)*(physicalArc η)^(2^N-1:ℕ))) := by
  intro S
  let A := visitSet H 0 η
  have hm : MeasurableSet A := by
    have he : A=(orbitCircuitDistance H 0) ⁻¹' Iic η := by
      ext t; exact hasProjectiveCircuitApproximation_iff_infDist .. 
    rw [he]
    exact measurableSet_Iic.preimage (orbitCircuitDistance_lipschitz H 0).continuous.measurable
  refine ⟨hm.preimage (measurable_id.sub_const v),?_⟩
  intro a
  have hh := (ShortTimeProducts.scalar_fraction H hi hη hsmall (a-v)).comp
    (tendsto_atTop_add_const_right atTop (-v) tendsto_id)
  apply hh.congr
  intro T
  have he : S ∩ Icc a T = (fun u : ℝ => u+(-v)) ⁻¹' (A ∩ Icc (a-v) (T-v)) := by
    ext u
    change ((u-v∈A) ∧ a ≤ u ∧ u ≤ T) ↔ u+(-v)∈A ∧ a-v ≤ u+(-v) ∧ u+(-v) ≤ T-v
    simp only [←sub_eq_add_neg,sub_le_sub_iff_right]
  have hmass := (measurePreserving_add_right volume (-v)).measure_preimage (hm.inter measurableSet_Icc).nullMeasurableSet
  change volume.real (A ∩ Icc (a-v) (T+ -v))/(T+ -v-(a-v))=_
  rw [he,show T+ -v-(a-v)=T-a by ring]
  exact congrArg (fun x : ℝ≥0∞ => x.toReal/(T-a)) hmass.symm

/-- The set of dates whose full gate-distance trajectory follows the
trajectory at v to tolerance η has an exact physical-time density. -/
theorem gaussian_full_profile_density :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ η ∈ Ioo (0:ℝ) (sqrt 2), ∀ v : ℝ,
        let S := {z : ℝ | ∀ t : ℝ, ∀ s : ℕ,
          |orbitCircuitDistance H s (z+t)-orbitCircuitDistance H s (v+t)| ≤ η}
        MeasurableSet S ∧ ∀ a : ℝ, Tendsto (fun T : ℝ => volume.real (S ∩ Icc a T)/(T-a))
          atTop (𝓝 (((2^N:ℕ):ℝ)*(physicalArc η)^(2^N-1:ℕ))) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw k
  intro N H η hη v S
  have he : S = (fun z : ℝ => z-v) ⁻¹' visitSet H 0 η :=
    Set.ext fun z => profile_replay_iff_scalar H z v η
  rw [he]
  exact translated_scalar_fraction H (hw k) hη.1 hη.2 v

#print axioms gaussian_full_profile_density
end
end GaloisForLFunctions.HTGeometry.TrajectoryProfiles
