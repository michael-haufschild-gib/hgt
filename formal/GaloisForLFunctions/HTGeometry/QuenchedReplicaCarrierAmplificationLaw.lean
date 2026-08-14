import GaloisForLFunctions.HTGeometry.BetaThresholdIncidenceLaw

/-!
# Quenched replica carrier-amplification law

Shared-source power replicas amplify every positive-mass preparation carrier below the target
depth.  If a carrier of source mass `p` has preparation reporter at least `z ^ b`, then the usual
depth-`s` normalized moment certificate has the unavoidable floor

`p / z ^ (r * (s - b))`.

Thus once the one-replica certificate is vacuous, every larger replica order is vacuous.  This is
the exact obstruction behind codimension shortcut carriers in static local-Hamiltonian ensembles:
growing replicas select them rather than suppress them.  The result is unconditional for every
finite source measure and every measurable `[0,1]`-valued reporter.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Shared-source replica moment of a bounded preparation reporter. -/
def quenchedReplicaMass (μ : Measure Ω) (r : ℕ) (F : Ω → ℝ) : ℝ :=
  ∫ ω, F ω ^ r ∂μ

theorem integrable_pow_of_mem_unitInterval
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1) (r : ℕ) :
    Integrable (fun ω => F ω ^ r) μ := by
  refine ⟨(hFm.pow_const r).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hF0 ω) r)]
  exact pow_le_one₀ (hF0 ω) (hF1 ω)

/-- A positive-mass easy carrier supplies an unavoidable lower bound on every shared-source
replica moment. -/
theorem carrier_mass_mul_pow_le_quenchedReplicaMass
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} {S : Set Ω}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (hSm : MeasurableSet S) {z : ℝ} (hz0 : 0 ≤ z) {b r : ℕ}
    (hcarrier : ∀ ω ∈ S, z ^ b ≤ F ω) :
    μ.real S * z ^ (r * b) ≤ quenchedReplicaMass μ r F := by
  have hint := integrable_pow_of_mem_unitInterval μ hFm hF0 hF1 r
  have hconst : Integrable (fun _ω : Ω => z ^ (r * b)) μ := integrable_const _
  calc
    μ.real S * z ^ (r * b) = ∫ _ω in S, z ^ (r * b) ∂μ := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ ω in S, F ω ^ r ∂μ := by
      apply setIntegral_mono_on hconst.integrableOn hint.integrableOn hSm
      intro ω hω
      rw [mul_comm r b, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hz0 b) (hcarrier ω hω) r
    _ ≤ ∫ ω, F ω ^ r ∂μ := by
      exact setIntegral_le_integral hint
        (Filter.Eventually.of_forall fun ω => pow_nonneg (hF0 ω) r)
    _ = quenchedReplicaMass μ r F := rfl

/-- Markov normalization at a target depth amplifies a shallower carrier by the exact depth-gap
factor. -/
theorem carrier_amplification_le_replicaCertificate
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} {S : Set Ω}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (hSm : MeasurableSet S) {z : ℝ} (hz0 : 0 < z) {b s r : ℕ} (hbs : b ≤ s)
    (hcarrier : ∀ ω ∈ S, z ^ b ≤ F ω) :
    μ.real S / z ^ (r * (s - b)) ≤
      quenchedReplicaMass μ r F / z ^ (r * s) := by
  have hmass := carrier_mass_mul_pow_le_quenchedReplicaMass
    μ hFm hF0 hF1 hSm hz0.le (r := r) hcarrier
  have hzpow : 0 < z ^ (r * s) := pow_pos hz0 _
  rw [le_div_iff₀ hzpow]
  calc
    μ.real S / z ^ (r * (s - b)) * z ^ (r * s) =
        μ.real S * z ^ (r * b) := by
      field_simp
      have hexp : r * s = r * (s - b) + r * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hbs]
      rw [hexp, pow_add]
      ring
    _ ≤ quenchedReplicaMass μ r F := hmass

/-- If carrier mass already exceeds the depth-gap penalty, the replica certificate is at least
one and therefore gives no nontrivial probability upper bound. -/
theorem one_le_replicaCertificate_of_carrier
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} {S : Set Ω}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (hSm : MeasurableSet S) {z : ℝ} (hz0 : 0 < z) {b s r : ℕ} (hbs : b ≤ s)
    (hcarrier : ∀ ω ∈ S, z ^ b ≤ F ω)
    (hvacuous : z ^ (r * (s - b)) ≤ μ.real S) :
    1 ≤ quenchedReplicaMass μ r F / z ^ (r * s) := by
  have hcarrierBound := carrier_amplification_le_replicaCertificate
    μ hFm hF0 hF1 hSm hz0 (r := r) hbs hcarrier
  have hzpow : 0 < z ^ (r * (s - b)) := pow_pos hz0 _
  apply le_trans (b := μ.real S / z ^ (r * (s - b)))
  · rw [le_div_iff₀ hzpow]
    simpa using hvacuous
  · exact hcarrierBound

/-- Once the first shared-source moment is carrier-vacuous, every growing replica order is
carrier-vacuous.  Replication cannot repair a shallower positive-mass carrier. -/
theorem all_replicaCertificates_vacuous_of_one
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ} {S : Set Ω}
    (hFm : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (hSm : MeasurableSet S) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1)
    {b s r : ℕ} (hbs : b ≤ s) (hr : 1 ≤ r)
    (hcarrier : ∀ ω ∈ S, z ^ b ≤ F ω)
    (hvacuous : z ^ (s - b) ≤ μ.real S) :
    1 ≤ quenchedReplicaMass μ r F / z ^ (r * s) := by
  have hexp : s - b ≤ r * (s - b) := by
    simpa using Nat.mul_le_mul_right (s - b) hr
  have hpow : z ^ (r * (s - b)) ≤ z ^ (s - b) :=
    pow_le_pow_of_le_one hz0.le hz1 hexp
  exact one_le_replicaCertificate_of_carrier
    μ hFm hF0 hF1 hSm hz0 hbs hcarrier (hpow.trans hvacuous)

/-- Above a depth gap, increasing replica order can only worsen the unavoidable carrier
amplification floor. -/
theorem carrierAmplification_mono
    {p z : ℝ} (hp : 0 ≤ p) (hz0 : 0 < z) (hz1 : z ≤ 1)
    {b s r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    p / z ^ (r₁ * (s - b)) ≤ p / z ^ (r₂ * (s - b)) := by
  have hpow : z ^ (r₂ * (s - b)) ≤ z ^ (r₁ * (s - b)) := by
    exact pow_le_pow_of_le_one hz0.le hz1 (Nat.mul_le_mul_right (s - b) hr)
  exact div_le_div_of_nonneg_left hp (pow_pos hz0 _) hpow

end

end GaloisForLFunctions.HTGeometry
