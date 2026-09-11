import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAmplitudeMap
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
open Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section WeightedAmplitude
variable {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private def observedWeightMap (v : I → E) (J : E →L[ℂ] H) (i : I) : ℂ →L[ℂ] ℂ :=
  (‖J (v i)‖ : ℂ) • ContinuousLinearMap.id ℂ ℂ

private theorem observedWeightMap_bound (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (J : E →L[ℂ] H) (i : I) : ‖observedWeightMap v J i‖ ≤ ‖J‖ := by
  rw [observedWeightMap, norm_smul, ContinuousLinearMap.norm_id, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [hv, mul_one] using J.le_opNorm (v i)

private def weightedL2Amplitude (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (J : E →L[ℂ] H) :
    E →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  (lp.mapCLM 2 (observedWeightMap v J) (norm_nonneg J) (observedWeightMap_bound v hv J)).comp A

private theorem weightedL2Amplitude_apply (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (J : E →L[ℂ] H) (u : E) (i : I) :
    weightedL2Amplitude v hv A J u i = (‖J (v i)‖ : ℂ) * A u i := rfl

private theorem weightedL2Amplitude_norm_le (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (J : E →L[ℂ] H) :
    ‖weightedL2Amplitude v hv A J‖ ≤ ‖J‖ * ‖A‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul_of_nonneg_right
    (lp.norm_mapCLM_le 2 (observedWeightMap v J) (norm_nonneg J)
      (observedWeightMap_bound v hv J)) (norm_nonneg A)

private theorem weightedL2Amplitude_square_norm (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (J : E →L[ℂ] H) (u : E) :
    ‖weightedL2Amplitude v hv A J u‖ ^ 2 = ∑' i, ‖A u i‖ ^ 2 * ‖J (v i)‖ ^ 2 := by
  calc
    _ = ∑' i, ‖weightedL2Amplitude v hv A J u i‖ ^ 2 := by
      simpa using (lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
        (weightedL2Amplitude v hv A J u)).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [weightedL2Amplitude_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), mul_pow]
      ring

private theorem weightedL2Amplitude_mode [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hA : ∀ i, A (v i) = lp.single 2 i 1) (J : E →L[ℂ] H) (i : I) :
    weightedL2Amplitude v hv A J (v i) = lp.single 2 i (‖J (v i)‖ : ℂ) := by
  apply lp.ext
  funext j
  rw [weightedL2Amplitude_apply, hA]
  by_cases hji : j = i
  · subst j
    rw [lp.single_apply_self, lp.single_apply_self, mul_one]
  · rw [lp.single_apply_ne _ _ _ hji, lp.single_apply_ne _ _ _ hji, mul_zero]

private theorem weightedL2Amplitude_packet_square_norm [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hA : ∀ i, A (v i) = lp.single 2 i 1) (J : E →L[ℂ] H)
    (s : Finset I) (c : I → ℂ) :
    ‖weightedL2Amplitude v hv A J (∑ i ∈ s, c i • v i)‖ ^ 2 =
      ∑ i ∈ s, ‖c i‖ ^ 2 * ‖J (v i)‖ ^ 2 := by
  have he : weightedL2Amplitude v hv A J (∑ i ∈ s, c i • v i) =
      ∑ i ∈ s, lp.single 2 i (c i * (‖J (v i)‖ : ℂ)) := by
    simp only [map_sum, map_smul, weightedL2Amplitude_mode v hv A hA J]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [smul_eq_mul] using
      (lp.single_smul (E := fun _ : I => ℂ) 2 i (c i) (‖J (v i)‖ : ℂ)).symm
  rw [he]
  have hn := lp.norm_sum_single (E := fun _ : I => ℂ)
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (fun i => c i * (‖J (v i)‖ : ℂ)) s
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using hn

end WeightedAmplitude
/-- Canonical frequency amplitudes weighted by the norm of each observed mode.
This bounded map records the spectral energy visible to an arbitrary bounded
linear observation, without imposing summability hypotheses on the input. -/
def causalFrequencyObservedAmplitude
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    causalFrequencySpace b →L[ℂ] lp (fun _ : ℝ => ℂ) 2 :=
  weightedL2Amplitude (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (causalFrequencyAmplitudeMap b) J

/-- Each observed amplitude is the canonical coefficient times the single-mode
observation norm. -/
theorem causalFrequencyObservedAmplitude_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) (ω : ℝ) :
    causalFrequencyObservedAmplitude b J u ω =
      (‖J (causalFrequencyMode b ω)‖ : ℂ) * causalFrequencyCoefficient b ω u := rfl

/-- Observation bounds the weighted-amplitude operator by its own norm. -/
theorem causalFrequencyObservedAmplitude_norm_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    ‖causalFrequencyObservedAmplitude b J‖ ≤ ‖J‖ := by
  simpa only [causalFrequencyObservedAmplitude, norm_causalFrequencyAmplitudeMap, mul_one] using
    weightedL2Amplitude_norm_le (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
      (causalFrequencyAmplitudeMap b) J

/-- The observed amplitude norm is exactly the convergent weighted spectral
energy, including vectors outside the absolutely summable synthesis image. -/
theorem causalFrequencyObservedAmplitude_square_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    ‖causalFrequencyObservedAmplitude b J u‖ ^ 2 =
      ∑' ω : ℝ, ‖causalFrequencyCoefficient b ω u‖ ^ 2 *
        ‖J (causalFrequencyMode b ω)‖ ^ 2 :=
  weightedL2Amplitude_square_norm (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (causalFrequencyAmplitudeMap b) J u

/-- The weighted energy series is summable for every actual frequency vector. -/
theorem causalFrequencyObservedAmplitude_summable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Summable (fun ω : ℝ => ‖causalFrequencyCoefficient b ω u‖ ^ 2 *
      ‖J (causalFrequencyMode b ω)‖ ^ 2) := by
  have hs := (lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    (causalFrequencyObservedAmplitude b J u)).summable
  convert hs using 1
  funext ω
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, causalFrequencyObservedAmplitude_apply,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), mul_pow]
  ring

/-- A single mode has exactly one observed amplitude. -/
theorem causalFrequencyObservedAmplitude_mode
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b ω : ℝ) (J : causalFrequencySpace b →L[ℂ] H) :
    causalFrequencyObservedAmplitude b J (causalFrequencyMode b ω) =
      lp.single 2 ω (‖J (causalFrequencyMode b ω)‖ : ℂ) :=
  weightedL2Amplitude_mode (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (causalFrequencyAmplitudeMap b) (causalFrequencyAmplitudeMap_mode b) J ω

/-- Finite observed packets have exactly the diagonal weighted energy. -/
theorem causalFrequencyObservedAmplitude_packet_square_norm
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (s : Finset ℝ) (c : ℝ → ℂ) :
    ‖causalFrequencyObservedAmplitude b J (∑ ω ∈ s, c ω • causalFrequencyMode b ω)‖ ^ 2 =
      ∑ ω ∈ s, ‖c ω‖ ^ 2 * ‖J (causalFrequencyMode b ω)‖ ^ 2 :=
  weightedL2Amplitude_packet_square_norm (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (causalFrequencyAmplitudeMap b) (causalFrequencyAmplitudeMap_mode b) J s c

end RHTower.FokasLenells
