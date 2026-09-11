import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAmplitudeMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Constructions
open Complex Set Filter
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section AbsoluteSynthesis
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private def modeScalarMap (v : I → E) (i : I) : ℂ →L[ℂ] E :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (v i)

private theorem modeScalarMap_norm (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (i : I) :
    ‖modeScalarMap v i‖ ≤ 1 := by
  rw [modeScalarMap, ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id, hv]
  norm_num

private def absoluteSynthesis (v : I → E) (hv : ∀ i, ‖v i‖ = 1) :
    lp (fun _ : I => ℂ) 1 →L[ℂ] E :=
  (lp.tsumCLM ℂ I E).comp (lp.mapCLM 1 (modeScalarMap v) zero_le_one (modeScalarMap_norm v hv))

private theorem absoluteSynthesis_apply (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (c : lp (fun _ : I => ℂ) 1) :
    absoluteSynthesis v hv c = ∑' i, c i • v i := rfl

private theorem absolute_family_summable (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (c : lp (fun _ : I => ℂ) 1) : Summable (fun i => c i • v i) := by
  apply Summable.of_norm
  have hc : Summable (fun i => ‖c i‖) := by simpa using c.property.summable (by norm_num)
  simpa only [norm_smul, hv, mul_one] using hc

private theorem absoluteSynthesis_hasSum (v : I → E) (hv : ∀ i, ‖v i‖ = 1)
    (c : lp (fun _ : I => ℂ) 1) :
    HasSum (fun i => c i • v i) (absoluteSynthesis v hv c) :=
  (absolute_family_summable v hv c).hasSum

private theorem absoluteSynthesis_single [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (i : I) (c : ℂ) :
    absoluteSynthesis v hv (lp.single 1 i c) = c • v i := by
  rw [absoluteSynthesis_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hji
    rw [lp.single_apply_ne _ _ _ hji, zero_smul]

private theorem absoluteSynthesis_coefficient [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (c : lp (fun _ : I => ℂ) 1) (i : I) :
    a i (absoluteSynthesis v hv c) = c i := by
  rw [absoluteSynthesis_apply, (a i).map_tsum (absolute_family_summable v hv c),
    tsum_eq_single i]
  · simp [map_smul, hd]
  · intro j hji
    simp [map_smul, hd, Ne.symm hji]

private theorem absoluteSynthesis_norm [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (i₀ : I) :
    ‖absoluteSynthesis v hv‖ = 1 := by
  apply le_antisymm
  · calc
      ‖absoluteSynthesis v hv‖ ≤ ‖lp.tsumCLM ℂ I E‖ *
          ‖lp.mapCLM 1 (modeScalarMap v) zero_le_one (modeScalarMap_norm v hv)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul lp.norm_tsumCLM_le
        (lp.norm_mapCLM_le 1 (modeScalarMap v) zero_le_one (modeScalarMap_norm v hv))
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have h := (absoluteSynthesis v hv).le_opNorm (lp.single 1 i₀ (1 : ℂ))
    rw [absoluteSynthesis_single, one_smul, hv,
      lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_one, mul_one] at h
    exact h

private theorem absoluteSynthesis_injective [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0) :
    Function.Injective (absoluteSynthesis v hv) := by
  intro c d he
  apply lp.ext
  funext i
  have h := congrArg (a i) he
  simpa only [absoluteSynthesis_coefficient v hv a hd] using h

private theorem absoluteSynthesis_amplitude_map [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (hA : ∀ u i, A u i = a i u)
    (c : lp (fun _ : I => ℂ) 1) :
    A (absoluteSynthesis v hv c) = lp.linearMapOfLE ℂ (fun _ : I => ℂ) (by norm_num) c := by
  apply lp.ext
  funext i
  change A (absoluteSynthesis v hv c) i = c i
  rw [hA, absoluteSynthesis_coefficient v hv a hd]
end AbsoluteSynthesis

section SynthesisDensity
variable {B I : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
private theorem subtype_synthesis_dense [DecidableEq I]
    (D : Submodule ℂ B) (v : I → D)
    (hD : (Submodule.span ℂ (Set.range (fun i => (v i).val))).topologicalClosure = D)
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] D)
    (hS : ∀ i, S (lp.single 1 i 1) = v i) : DenseRange S := by
  let V : Submodule ℂ B := Submodule.span ℂ (Set.range (fun i => (v i).val))
  have hVD : V ≤ D := by
    rw [← hD]
    exact V.le_topologicalClosure
  let j : V → D := fun x => ⟨x.val, hVD x.property⟩
  have hj : DenseRange j := by
    change DenseRange (Set.inclusion (show (V : Set B) ⊆ D from hVD))
    apply (denseRange_inclusion_iff _).mpr
    change (D : Set B) ⊆ (V.topologicalClosure : Set B)
    rw [hD]
  refine Dense.mono ?_ hj
  rintro y ⟨x, rfl⟩
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp x.property
  change (∑ i ∈ c.support, c i • (v i).val) = x.val at hc
  refine ⟨∑ i ∈ c.support, c i • lp.single 1 i 1, ?_⟩
  apply Subtype.ext
  simp only [map_sum, map_smul, hS]
  change D.subtype (∑ i ∈ c.support, c i • v i) = x.val
  simp only [map_sum, map_smul]
  exact hc
end SynthesisDensity
/-- Absolute summation of actual unit frequency modes, as a bounded linear map
from real-indexed complex lp1 into the completed derivative-chain space. -/
def causalFrequencyAbsoluteSynthesis (b : ℝ) :
    lp (fun _ : ℝ => ℂ) 1 →L[ℂ] causalFrequencySpace b :=
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  absoluteSynthesis (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)

/-- Every absolutely summable amplitude family has its actual mode sum in the
chain norm, with no additional convergence premise. -/
theorem causalFrequencyAbsoluteSynthesis_hasSum (b : ℝ)
    (c : lp (fun _ : ℝ => ℂ) 1) :
    HasSum (fun ω => c ω • causalFrequencyMode b ω) (causalFrequencyAbsoluteSynthesis b c) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact absoluteSynthesis_hasSum (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b) c

/-- Synthesizing an lp1 family and extracting its lp2 amplitudes is exactly the
canonical inclusion of the same scalar family into lp2. -/
theorem causalFrequencyAmplitudeMap_absoluteSynthesis (b : ℝ)
    (c : lp (fun _ : ℝ => ℂ) 1) :
    causalFrequencyAmplitudeMap b (causalFrequencyAbsoluteSynthesis b c) =
      lp.linearMapOfLE ℂ (fun _ : ℝ => ℂ) (by norm_num : (1 : ENNReal) ≤ 2) c := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact absoluteSynthesis_amplitude_map (causalFrequencyMode b)
    (norm_causalBoundedUnitEigenchain b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyAmplitudeMap b) (fun _ _ => rfl) c

/-- The actual lp1 synthesis map has sharp operator norm one. -/
theorem norm_causalFrequencyAbsoluteSynthesis (b : ℝ) :
    ‖causalFrequencyAbsoluteSynthesis b‖ = 1 := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact absoluteSynthesis_norm (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b) 0

/-- Absolutely summable amplitude data are faithfully realized in actual chains. -/
theorem causalFrequencyAbsoluteSynthesis_injective (b : ℝ) :
    Function.Injective (causalFrequencyAbsoluteSynthesis b) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact absoluteSynthesis_injective (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (causalFrequencyCoefficient b) (causalFrequencyCoefficient_mode b)

/-- Absolutely summable mode sums are dense in the completed chain norm. -/
theorem causalFrequencyAbsoluteSynthesis_denseRange (b : ℝ) :
    DenseRange (causalFrequencyAbsoluteSynthesis b) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  apply subtype_synthesis_dense (causalFrequencySpace b) (causalFrequencyMode b) rfl
    (causalFrequencyAbsoluteSynthesis b)
  intro ω
  change absoluteSynthesis (causalFrequencyMode b) (norm_causalBoundedUnitEigenchain b)
    (lp.single 1 ω (1 : ℂ)) = causalFrequencyMode b ω
  simpa only [one_smul] using absoluteSynthesis_single (causalFrequencyMode b)
    (norm_causalBoundedUnitEigenchain b) ω (1 : ℂ)

end RHTower.FokasLenells
