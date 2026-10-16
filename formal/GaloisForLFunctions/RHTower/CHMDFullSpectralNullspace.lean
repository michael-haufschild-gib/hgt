import GaloisForLFunctions.RHTower.CHMDTranslatedCardinalDetection
import GaloisForLFunctions.RHTower.CHMDPolarPlane

/-!
# Exact full spectral nullspace and signed radical

Every zero-silent graph source has a unique polar-plane component and a radical
remainder. The full radical is exactly the joint kernel of all Xi-zero samples
and both polar samples. These set identities have no parity, spectral expansion,
positivity, or graph-admission hypotheses.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph

def polarResidual (p : SourceGraph) : SourceGraph :=
  p - (2*polarCosine p) • constantLift 1 - (2*polarSine p) • oddPolarVector

theorem polarResidual_mem_signedRadical {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) :
    polarResidual p ∈ signedRadical := by
  intro q
  rw [polarResidual, sourcePair_sub_left, sourcePair_sub_left,
    sourcePair_smul_left, sourcePair_smul_left, full_nullspace_pair hp q,
    sourcePair_ground_eq_polarCosine, sourcePair_oddPolarVector]
  ring

theorem radical_polarCosine_zero {p : SourceGraph} (hp : p ∈ signedRadical) : polarCosine p = 0 := by
  have h := hp (constantLift 1)
  rw [sourcePair_symm, sourcePair_ground_eq_polarCosine, neg_eq_zero] at h
  exact h

theorem radical_polarSine_zero {p : SourceGraph} (hp : p ∈ signedRadical) : polarSine p = 0 := by
  have h := hp oddPolarVector
  rwa [sourcePair_symm, sourcePair_oddPolarVector] at h

theorem radical_graphFourierReadout_poles_zero {p : SourceGraph} (hp : p ∈ signedRadical) :
    graphFourierReadout p (I/2) = 0 ∧ graphFourierReadout p (-I/2) = 0 := by
  have hc := radical_polarCosine_zero hp
  have hs := radical_polarSine_zero hp
  rw [polarCosine_eq_half_fourier] at hc
  unfold polarSine at hs
  have hplus : (graphFourierReadout p (I/2)).re = 0 := by linarith
  have hminus : (graphFourierReadout p (-I/2)).re = 0 := by linarith
  constructor
  · apply Complex.ext
    · exact hplus
    · exact graphFourierReadout_real_of_re_zero p (by norm_num)
  · apply Complex.ext
    · exact hminus
    · exact graphFourierReadout_real_of_re_zero p (by norm_num)

theorem full_radical_iff_samples_zero (p : SourceGraph) :
    p ∈ signedRadical ↔ (∀ z : ℂ, XiC z = 0 → graphFourierReadout p z = 0) ∧
      graphFourierReadout p (I/2) = 0 ∧ graphFourierReadout p (-I/2) = 0 := by
  constructor
  · intro hp
    exact ⟨fun _ hz => radical_graphFourierReadout_zero hp hz, radical_graphFourierReadout_poles_zero hp⟩
  · rintro ⟨hz, hplus, hminus⟩ q
    rw [full_nullspace_pair_poles hz q, hplus, hminus]
    simp

theorem polar_coefficients_eq_of_residual_radical {p : SourceGraph} {c d : ℝ}
    (hr : p - c • constantLift 1 - d • oddPolarVector ∈ signedRadical) :
    c = 2*polarCosine p ∧ d = 2*polarSine p := by
  have hg := hr (constantLift 1)
  rw [sourcePair_sub_left, sourcePair_sub_left, sourcePair_smul_left, sourcePair_smul_left,
    sourcePair_symm p (constantLift 1), sourcePair_ground_eq_polarCosine,
    sourcePair_ground_eq_polarCosine, polarCosine_ground,
    sourcePair_oddPolarVector, polarSine_ground] at hg
  have hh := hr oddPolarVector
  rw [sourcePair_sub_left, sourcePair_sub_left, sourcePair_smul_left, sourcePair_smul_left,
    sourcePair_symm p oddPolarVector, sourcePair_oddPolarVector,
    sourcePair_ground_eq_polarCosine, polarCosine_oddPolarVector,
    sourcePair_oddPolarVector, polarSine_oddPolarVector] at hh
  constructor <;> linarith

theorem full_nullspace_unique_polar_coefficients {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) :
    ∃! cd : ℝ × ℝ, p - cd.1 • constantLift 1 - cd.2 • oddPolarVector ∈ signedRadical := by
  refine ⟨(2*polarCosine p, 2*polarSine p), polarResidual_mem_signedRadical hp, ?_⟩
  intro cd hcd
  obtain ⟨hc, hd⟩ := polar_coefficients_eq_of_residual_radical hcd
  exact Prod.ext hc hd

/-- Unconditional decomposition of the entire zero-sample kernel. -/
theorem fullSpectralNullspace_eq_polarPlane_add_radical :
    fullSpectralNullspace = {p | ∃ c d : ℝ, ∃ r : SourceGraph,
      r ∈ signedRadical ∧ p = c • constantLift 1 + d • oddPolarVector + r} := by
  ext p
  constructor
  · intro hp
    exact ⟨2*polarCosine p, 2*polarSine p, polarResidual p,
      polarResidual_mem_signedRadical hp, by unfold polarResidual; abel⟩
  · rintro ⟨c, d, r, hr, hp⟩ z hz
    have hstrip := (abs_im_lt_half_of_XiC_eq_zero hz).le
    rw [hp, graphFourierReadout_add _ _ hstrip, graphFourierReadout_add _ _ hstrip,
      graphFourierReadout_smul _ _ hstrip, graphFourierReadout_smul _ _ hstrip,
      ground_mem_fullSpectralNullspace z hz, oddPolarVector_mem_fullSpectralNullspace z hz,
      radical_graphFourierReadout_zero hr hz]
    simp

/-- No undetected parity sector remains in the radical characterization. -/
theorem signedRadical_eq_full_joint_kernel :
    (signedRadical : Set SourceGraph) = {p : SourceGraph | p ∈ fullSpectralNullspace ∧
      graphFourierReadout p (I/2) = 0 ∧ graphFourierReadout p (-I/2) = 0} := by
  ext p
  exact full_radical_iff_samples_zero p

end RHTower.CHMDDoobGraph
