import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteInstability
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section Image
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem coefficient_from_inclusion (a : I → E →L[ℂ] ℂ)
    (A : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hA : ∀ u i, A u i = a i u)
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : ∀ c, A (S c) = lp.linearMapOfLE ℂ (fun _ : I => ℂ)
      (by norm_num : (1 : ENNReal) ≤ 2) c)
    (c : lp (fun _ : I => ℂ) 1) (i : I) : a i (S c) = c i := by
  have h := congrArg (fun x : lp (fun _ : I => ℂ) 2 => x i) (hS c)
  change A (S c) i = c i at h
  simpa only [hA] using h

private theorem synthesis_range_iff_absolute_coefficients
    (a : I → E →L[ℂ] ℂ)
    (hi : Function.Injective (fun u : E => fun i => a i u))
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : ∀ c i, a i (S c) = c i) (u : E) :
    u ∈ Set.range S ↔ Summable (fun i => ‖a i u‖) := by
  constructor
  · rintro ⟨c, rfl⟩
    simp only [hS]
    simpa using c.property.summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  · intro h
    have hm : Memℓp (fun i => a i u) 1 := by
      apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)).2
      simpa using h
    let c : lp (fun _ : I => ℂ) 1 := ⟨fun i => a i u, hm⟩
    refine ⟨c, hi ?_⟩
    funext i
    exact hS c i

private theorem nonsurjective_exists_nonabsolute_coefficients
    (a : I → E →L[ℂ] ℂ) (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hr : ∀ u, u ∈ Set.range S ↔ Summable (fun i => ‖a i u‖))
    (hS : ¬ Function.Surjective S) : ∃ u : E, ¬ Summable (fun i => ‖a i u‖) := by
  by_contra h
  push_neg at h
  apply hS
  intro u
  exact (hr u).2 (h u)
end Image

/-- Every canonical coefficient of an actual absolute mode sum is its input
amplitude, without an additional convergence or interchange hypothesis. -/
theorem causalFrequencyCoefficient_absoluteSynthesis (b : ℝ)
    (c : lp (fun _ : ℝ => ℂ) 1) (ω : ℝ) :
    causalFrequencyCoefficient b ω (causalFrequencyAbsoluteSynthesis b c) = c ω :=
  coefficient_from_inclusion (causalFrequencyCoefficient b)
    (causalFrequencyAmplitudeMap b) (fun _ _ => rfl)
    (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAmplitudeMap_absoluteSynthesis b) c ω

/-- The absolute-synthesis image is exactly the set of completed frequency
chains whose canonical amplitudes are absolutely summable. -/
theorem causalFrequencyAbsoluteSynthesis_range_iff (b : ℝ) (u : causalFrequencySpace b) :
    u ∈ Set.range (causalFrequencyAbsoluteSynthesis b) ↔
      Summable (fun ω => ‖causalFrequencyCoefficient b ω u‖) :=
  synthesis_range_iff_absolute_coefficients (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_injective b) (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyCoefficient_absoluteSynthesis b) u

/-- The actual completed space contains vectors with square-summable canonical
amplitudes that are not absolutely summable. -/
theorem causalFrequencyCoefficient_exists_not_summable (b : ℝ) :
    ∃ u : causalFrequencySpace b,
      ¬ Summable (fun ω => ‖causalFrequencyCoefficient b ω u‖) :=
  nonsurjective_exists_nonabsolute_coefficients (causalFrequencyCoefficient b)
    (causalFrequencyAbsoluteSynthesis b) (causalFrequencyAbsoluteSynthesis_range_iff b)
    (causalFrequencyAbsoluteSynthesis_not_surjective b)

end RHTower.FokasLenells
