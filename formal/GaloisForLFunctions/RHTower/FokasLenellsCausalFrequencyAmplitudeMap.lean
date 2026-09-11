import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyBessel
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyTotality
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
open Complex Set Filter
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section L2Model
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem coefficient_mem_l2 (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2)) (u : E) :
    Memℓp (fun i => a i u) 2 := by
  apply memℓp_gen
  simpa using hs u

private def coefficientL2Linear (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2)) :
    E →ₗ[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun u := ⟨fun i => a i u, coefficient_mem_l2 a hs u⟩
  map_add' u w := by
    apply lp.ext
    funext i
    exact map_add (a i) u w
  map_smul' c u := by
    apply lp.ext
    funext i
    exact map_smul (a i) c u

private theorem coefficientL2Linear_bound (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2) (u : E) :
    ‖coefficientL2Linear a hs u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg u)
  change (∑' i, ‖a i u‖ ^ (2 : ENNReal).toReal) ≤ ‖u‖ ^ (2 : ENNReal).toReal
  simpa using hb u

private def coefficientL2Map (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2) :
    E →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  (coefficientL2Linear a hs).mkContinuous 1 (fun u => by
    simpa only [one_mul] using coefficientL2Linear_bound a hs hb u)

private theorem coefficientL2Map_injective (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2)
    (hi : Function.Injective (fun u => fun i => a i u)) :
    Function.Injective (coefficientL2Map a hs hb) := by
  intro u w h
  apply hi
  funext i
  exact congrArg (fun x : lp (fun _ : I => ℂ) 2 => x i) h

private theorem coefficientL2Map_mode [DecidableEq I]
    (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2)
    (v : I → E) (hd : ∀ i j, a i (v j) = if i = j then 1 else 0) (i : I) :
    coefficientL2Map a hs hb (v i) = lp.single 2 i 1 := by
  apply lp.ext
  funext j
  change a j (v i) = (lp.single (E := fun _ : I => ℂ) 2 i (1 : ℂ)) j
  rw [hd]
  by_cases h : j = i
  · subst j
    simp
  · rw [if_neg h, lp.single_apply_ne _ _ _ h]

private theorem contraction_norm_one {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) (hA : ∀ u, ‖A u‖ ≤ ‖u‖)
    (v : E) (hv : ‖v‖ = 1) (hAv : ‖A v‖ = 1) : ‖A‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simpa only [one_mul] using hA u
  · have h := A.le_opNorm v
    simpa only [hAv, hv, mul_one] using h

private theorem l2_dense_range [DecidableEq I]
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2) (v : I → E)
    (hv : ∀ i, A (v i) = lp.single 2 i 1) : DenseRange A := by
  intro f
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) f)
  apply Filter.Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, f i • v i, ?_⟩
  simp only [map_sum, map_smul, hv]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : I => ℂ) 2 i (f i) (1 : ℂ)).symm
end L2Model
/-- The actual scalar amplitude family, bundled as a bounded linear map into
real-indexed complex square-summable sequences. -/
def causalFrequencyAmplitudeMap (b : ℝ) :
    causalFrequencySpace b →L[ℂ] lp (fun _ : ℝ => ℂ) 2 :=
  coefficientL2Map (causalFrequencyCoefficient b)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).1)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).2)

/-- Each actual unit mode becomes the corresponding unit coordinate vector. -/
theorem causalFrequencyAmplitudeMap_mode (b ω : ℝ) :
    causalFrequencyAmplitudeMap b (causalFrequencyMode b ω) = lp.single 2 ω 1 :=
  coefficientL2Map_mode (causalFrequencyCoefficient b)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).1)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).2)
    (causalFrequencyMode b) (causalFrequencyCoefficient_mode b) ω

/-- Square-summable amplitudes uniquely determine the actual frequency vector. -/
theorem causalFrequencyAmplitudeMap_injective (b : ℝ) :
    Function.Injective (causalFrequencyAmplitudeMap b) :=
  coefficientL2Map_injective (causalFrequencyCoefficient b)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).1)
    (fun u => (causalFrequencyCoefficient_summable_sq b u).2)
    (causalFrequencyCoefficient_injective b)

/-- The amplitude map has exact operator norm one. -/
theorem norm_causalFrequencyAmplitudeMap (b : ℝ) :
    ‖causalFrequencyAmplitudeMap b‖ = 1 := by
  apply contraction_norm_one (causalFrequencyAmplitudeMap b)
    (coefficientL2Linear_bound (causalFrequencyCoefficient b)
      (fun u => (causalFrequencyCoefficient_summable_sq b u).1)
      (fun u => (causalFrequencyCoefficient_summable_sq b u).2))
    (causalFrequencyMode b 0)
  · exact norm_causalBoundedUnitEigenchain b 0
  · rw [causalFrequencyAmplitudeMap_mode]
    simpa using (lp.norm_single (E := fun _ : ℝ => ℂ) (by norm_num : (0 : ENNReal) < 2)
      (0 : ℝ) (1 : ℂ))

/-- Finite actual mode sums provide a dense image in the amplitude Hilbert space.
This density does not assert that every square-summable family is realizable. -/
theorem causalFrequencyAmplitudeMap_denseRange (b : ℝ) :
    DenseRange (causalFrequencyAmplitudeMap b) :=
  l2_dense_range (causalFrequencyAmplitudeMap b) (causalFrequencyMode b)
    (causalFrequencyAmplitudeMap_mode b)

end RHTower.FokasLenells
