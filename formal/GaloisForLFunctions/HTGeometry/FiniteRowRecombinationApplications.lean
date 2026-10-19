import GaloisForLFunctions.HTGeometry.FiniteRowRecombination
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss
import GaloisForLFunctions.HTGeometry.SourceResponseFormationEnergy

/-!
# Recombination of operator leakage and source-response energy

The finite mean-square recombination principle applies to the existing
Hilbert--Schmidt leakage and response-packet energies. Arbitrary signed
or complex coefficients are allowed; their total absolute mass records
the cost of synthesis. Row-dependent mixtures use their common envelope.
-/

noncomputable section
open scoped BigOperators NNReal
open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Hilbert--Schmidt synthesis with arbitrary complex coefficient mass. -/
theorem hsSqRe_sum_le_mass {ι d : Type*} [Fintype d]
    (s : Finset ι) (c : ι → ℂ) (W : ι → Matrix d d ℂ) :
    hsSqRe (∑ i ∈ s, c i • W i) ≤
      (∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * hsSqRe (W i) := by
  have h := sum_weight_norm_sum_smul_sq_le_mass s (fun _ : d × d => (1 : ℝ≥0)) c
    (fun i (r : d × d) => W i r.2 r.1)
  simpa only [hsSqRe_eq_sum, Matrix.sum_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, NNReal.coe_one, one_mul] using h

/-- A synthesized operator's leakage is controlled without unit-mass normalization. -/
theorem leak_sum_le_mass {ι d : Type*} [Fintype d] [DecidableEq d]
    (s : Finset ι) (PU PV : Matrix d d ℂ) (c : ι → ℂ) (W : ι → Matrix d d ℂ) :
    hsSqRe ((1 - PV) * (∑ i ∈ s, c i • W i) * PU) ≤
      (∑ i ∈ s, ‖c i‖) *
        ∑ i ∈ s, ‖c i‖ * hsSqRe ((1 - PV) * W i * PU) := by
  have heq : (1 - PV) * (∑ i ∈ s, c i • W i) * PU =
      ∑ i ∈ s, c i • ((1 - PV) * W i * PU) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [heq]
  exact hsSqRe_sum_le_mass s c _

/-- An arbitrary finite family of linear observations inherits the same synthesis budget. -/
theorem sum_weight_observation_energy_recombine_le
    {ι ρ 𝕜 V W : Type*} [Fintype ρ] [NormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (s : Finset ι) (w : ρ → ℝ≥0) (A : ρ → V →L[𝕜] W)
    (c : ι → ρ → 𝕜) (x : ι → ρ → V) :
    (∑ r, (w r : ℝ) * ‖A r (∑ i ∈ s, c i r • x i r)‖ ^ 2) ≤
      (∑ i ∈ s, ‖c i‖) *
        ∑ i ∈ s, ‖c i‖ * ∑ r, (w r : ℝ) * ‖A r (x i r)‖ ^ 2 := by
  simpa only [map_sum, map_smul] using
    sum_weight_norm_sum_smul_sq_le_row_envelope s w c (fun i r => A r (x i r))

namespace SourceResponse.ResponsePacket

variable {ι ρ I V W : Type*} [Fintype I]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Formation energy of a signed source mixture is bounded by constituent energies. -/
theorem energy_sum_le_mass (P : ResponsePacket I V W)
    (s : Finset ι) (c : ι → ℝ) (x : ι → V) :
    P.energy (∑ i ∈ s, c i • x i) ≤
      (∑ i ∈ s, ‖c i‖) * ∑ i ∈ s, ‖c i‖ * P.energy (x i) := by
  simpa only [energy, map_sum, map_smul] using
    norm_sum_smul_sq_le_mass s c (fun i => P.analysis (x i))

/-- Different response packets and mixtures may be used at every observation. -/
theorem sum_weight_energy_recombine_le [Fintype ρ]
    (P : ρ → ResponsePacket I V W) (s : Finset ι) (w : ρ → ℝ≥0)
    (c : ι → ρ → ℝ) (x : ι → ρ → V) :
    (∑ r, (w r : ℝ) * (P r).energy (∑ i ∈ s, c i r • x i r)) ≤
      (∑ i ∈ s, ‖c i‖) *
        ∑ i ∈ s, ‖c i‖ * ∑ r, (w r : ℝ) * (P r).energy (x i r) := by
  simpa only [energy] using
    sum_weight_observation_energy_recombine_le s w (fun r => (P r).analysis) c x

end SourceResponse.ResponsePacket

end GaloisForLFunctions.HTGeometry
