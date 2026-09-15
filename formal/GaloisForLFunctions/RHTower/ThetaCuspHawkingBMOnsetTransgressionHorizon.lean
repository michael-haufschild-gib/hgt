import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceTimeTranslation

/-!
The compact translation defect of the literal fixed-onset source is one-sided at
the two horizon ends.  It has zero ingoing datum and retains exactly the
translated past datum.  This is boundary data for the backward causal
Goursat--Duhamel problem; no advanced wave or Peierls theorem is asserted.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMSourceTimeTranslation
open D4BMFullSourceAdvanced
noncomputable section
set_option autoImplicit false

/-- The literal fixed-onset translation defect carries no ingoing-horizon datum. -/
theorem defect_response_ingoing_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T v X k : ℝ) :
    Tendsto (fun x => ∫ p in Ioi 0 ×ˢ Iio 0,
      defectDensity q branch amp T (v-x) x X k p) atBot (𝓝 0) := by
  have h := (response_ingoing_horizon q branch amp (v+T) X k).sub
    ((response_ingoing_horizon q branch amp v X k).const_mul
      (sourceFactor q branch T))
  have he : (fun x =>
      response q branch amp (v+T-x) x X k-
        sourceFactor q branch T*response q branch amp (v-x) x X k) =ᶠ[atBot]
      (fun x => ∫ p in Ioi 0 ×ˢ Iio 0,
        defectDensity q branch amp T (v-x) x X k p) :=
    Eventually.of_forall (fun x => by
      change response q branch amp (v+T-x) x X k-
          sourceFactor q branch T*response q branch amp (v-x) x X k =
        ∫ p in Ioi 0 ×ˢ Iio 0, defectDensity q branch amp T (v-x) x X k p
      rw [show v+T-x=(v-x)+T by ring]
      exact response_translation q branch amp T (v-x) x X k)
  simpa using h.congr' he

/-- The onset defect is a one-sided horizon transgression: zero on the ingoing
side and the exact translated past datum on the outgoing side. -/
theorem defect_response_two_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T v X k : ℝ) :
    Tendsto (fun x => ∫ p in Ioi 0 ×ˢ Iio 0,
      defectDensity q branch amp T (v-x) x X k p) atBot (𝓝 0) ∧
    Tendsto (fun x => ∫ p in Ioi 0 ×ˢ Iio 0,
      defectDensity q branch amp T (v+x) x X k p) atBot
      (𝓝 (D4BMPastSourceResponse.pastResponse q branch amp (v+T) X k-
        sourceFactor q branch T * D4BMPastSourceResponse.pastResponse q branch amp v X k)) :=
  ⟨defect_response_ingoing_horizon q branch amp T v X k,
    defect_response_past_horizon q branch amp T v X k⟩

end
end RHTower.D4BMSourceTimeTranslation
