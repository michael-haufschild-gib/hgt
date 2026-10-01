import GaloisForLFunctions.RHTower.SteinhausFiniteLocalTarget


open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- Any finite set of distinct coordinates has exactly the original finite uniform phase law. -/
theorem map_steinhausMeasure_finiteCoordinates {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) :
    steinhausMeasure.map (fun (ω : Omega) (i : Fin n) => ω (p i)) =
      steinhausFinitePhaseMeasure n := by
  unfold steinhausMeasure steinhausFinitePhaseMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj hp, Measure.infinitePi_eq_pi]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The finite local-target lower bound holds under the original infinite Steinhaus law on any distinct coordinates. -/
theorem measureReal_originalSteinhausFiniteLocalTarget_ge {n : ℕ}
    (p : Fin n → ℕ) (hp : Function.Injective p) (a : Fin n → E)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hframe : ∀ w : E, c * ‖w‖ ^ 2 ≤ ∑ i, ‖inner ℂ (a i) w‖ ^ 2)
    (v : E) (hsmall : ∀ i, ‖a i‖ * ‖v‖ / c ≤ 1 / 2)
    (henergy : (∑ i, ‖a i‖ ^ 2) ≤ r ^ 2 / 2) :
    (1 / 4 : ℝ) * Real.exp (-2 * ‖v‖ ^ 2 / c) ≤
      steinhausMeasure.real {ω | ‖(∑ i, charFactor 1 (ω (p i)) • a i) - v‖ < r} := by
  have hcont : Continuous (fun x : Fin n → ℝ => ∑ i, charFactor 1 (x i) • a i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_charFactor 1).comp (continuous_apply i)).smul continuous_const)
  have hset : MeasurableSet {x : Fin n → ℝ | ‖(∑ i, charFactor 1 (x i) • a i) - v‖ < r} :=
    measurableSet_lt (hcont.sub continuous_const).norm.measurable measurable_const
  have hmap := map_steinhausMeasure_finiteCoordinates p hp
  have heq : steinhausMeasure.real {ω | ‖(∑ i, charFactor 1 (ω (p i)) • a i) - v‖ < r} =
      (steinhausFinitePhaseMeasure n).real {x | ‖(∑ i, charFactor 1 (x i) • a i) - v‖ < r} := by
    unfold Measure.real
    rw [← hmap, Measure.map_apply
      (measurable_pi_lambda _ (fun i => measurable_pi_apply (p i))) hset]
    rfl
  rw [heq]
  exact measureReal_steinhausFiniteLocalTarget_ge a hc hr hframe v hsmall henergy

end RHTower
