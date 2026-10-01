import GaloisForLFunctions.RHTower.SteinhausPrefixResampling
import GaloisForLFunctions.RHTower.SteinhausFrozenCarrierLocalTarget


open MeasureTheory
open scoped ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- Integrating a uniform conditional target bound preserves the retained event. -/
theorem measureReal_prefixEvent_inter_target_ge (S : Finset ℕ) {E A : Set Omega}
    (hE : MeasurableSet E) (hA : MeasurableSet A)
    (hretain : ∀ ω ξ : Omega, (∀ p ∈ S, ω p = ξ p) → (ω ∈ E ↔ ξ ∈ E))
    {q : ℝ} (hq : 0 ≤ q)
    (hconditional : ∀ ω ∈ E,
      q ≤ steinhausMeasure.real {η | freezeSteinhausPrefix S ω η ∈ A}) :
    q * steinhausMeasure.real E ≤ steinhausMeasure.real (E ∩ A) := by
  classical
  have hEA := hE.inter hA
  have hmap : steinhausMeasure (E ∩ A) =
      (steinhausMeasure.prod steinhausMeasure)
        ((fun z : Omega × Omega => freezeSteinhausPrefix S z.1 z.2) ⁻¹' (E ∩ A)) := by
    rw [← Measure.map_apply (measurable_freezeSteinhausPrefix_joint S) hEA,
      map_freezeSteinhausPrefix]
  have hlow : ENNReal.ofReal q * steinhausMeasure E ≤ steinhausMeasure (E ∩ A) := by
    rw [hmap, Measure.prod_apply (hEA.preimage (measurable_freezeSteinhausPrefix_joint S)),
      ← lintegral_indicator_const hE]
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have heq : Prod.mk ω ⁻¹'
          ((fun z : Omega × Omega => freezeSteinhausPrefix S z.1 z.2) ⁻¹' (E ∩ A)) =
          {η | freezeSteinhausPrefix S ω η ∈ A} := by
        ext η
        have hr : freezeSteinhausPrefix S ω η ∈ E :=
          (hretain ω _ (fun p hp => by simp [freezeSteinhausPrefix, hp])).mp hω
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, hr, true_and]
      dsimp only
      rw [heq]
      have h := ENNReal.ofReal_le_ofReal (hconditional ω hω)
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
    · simp only [Set.indicator_of_notMem hω]
      exact bot_le
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hlow
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq, Measure.real] using h

/-- Measurability of the literal finite-node carrier. -/
theorem measurable_steinhausHilbertCarrier {J : ℕ} (a : Fin J → ℕ → ℂ) (N : ℕ) :
    Measurable (steinhausHilbertCarrier a N) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin J => ℂ)).measurable.comp
  apply measurable_pi_lambda
  intro j
  exact Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))

end RHTower
