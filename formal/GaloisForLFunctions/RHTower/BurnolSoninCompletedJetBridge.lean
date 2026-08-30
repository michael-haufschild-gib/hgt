import GaloisForLFunctions.RHTower.SoninStripEvaluator
import GaloisForLFunctions.RHTower.SoninModelBridge
import GaloisForLFunctions.RHTower.BurnolSoninAllOrderTailJets

/-!
# Completed all-order Burnol jet evaluators on the literal source carrier

`SoninStripEvaluator` provides bounded all-order jets on its central-band
model.  The actual Burnol source carrier in this project is
`soninExtendedSpace a`, defined by the positive-head and cosine-head
conditions.  This file transports the generic result through the proved
model equivalence and identifies the resulting product with the literal
Gamma-completed Mellin evaluation.

Consequently every finite completed *continuation* jet is a bounded functional
on the literal source carrier throughout the open strip, and it agrees with
the raw completed integral in its absolute-convergence half-strip. This
settles the bounded-evaluator prerequisite for taking closures; it does not
prove the subsequent `L_a/K_a/P_a` complement or aperture-completeness
theorem.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The literal positive-head Sonine carrier embeds continuously into the
central-band model used by the existing all-order evaluator theorem. -/
def soninExtendedToSoninEvenExtended (a : ℝ) (ha : 0 < a) :
    soninExtendedSpace a →L[ℂ] soninEvenExtended a :=
  (evenSubspace.subtypeL.comp (soninExtendedSpace a).subtypeL).codRestrict
    (soninEvenExtended a) (fun f => by
      constructor
      · exact mem_centralSoninExtendedCarrier_of_mem_soninExtendedSpace ha f.property
      · exact ((f : soninExtendedSpace a) : evenSubspace).property)

/-- The embedding does not alter the underlying `L²` vector. -/
theorem soninExtendedToSoninEvenExtended_apply (a : ℝ) (ha : 0 < a)
    (f : soninExtendedSpace a) :
    ((soninExtendedToSoninEvenExtended a ha f : soninEvenExtended a) : SoninL2) =
      (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) := rfl

/-- The source-selected analytic continuation of the completed Mellin
transform.  On its absolute-convergence half-strip it is proved below to be
the literal completed integral; outside that half-strip it is the uniquely
specified central-band continuation, not a divergent raw integral. -/
def soninExtendedCompletedMellinContinuation (a : ℝ) (ha : 0 < a)
    (f : soninExtendedSpace a) (s : ℂ) : ℂ :=
  soninEval a ((soninExtendedToSoninEvenExtended a ha f : soninEvenExtended a) : SoninL2) s *
    mellinCompletionFactor s

/-- The Gamma completion factor is analytic on the open strip. -/
theorem analyticOnNhd_mellinCompletionFactor_openStrip :
    AnalyticOnNhd ℂ mellinCompletionFactor {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  exact analyticAt_mellinCompletionFactor_of_re_pos hz.1

/-- The completed literal Mellin transform agrees locally with the product
of the central-model evaluator and the Gamma completion factor. -/
theorem eventuallyEq_soninEval_mul_completion_soninMellinEvaluation
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (f : soninExtendedSpace a) :
    (fun s : ℂ => soninExtendedCompletedMellinContinuation a ha f s) =ᶠ[𝓝 w]
      fun s : ℂ => soninMellinEvaluation s
        ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2)) := by
  change (fun s : ℂ =>
    soninEval a ((soninExtendedToSoninEvenExtended a ha f : soninEvenExtended a) : SoninL2) s *
      mellinCompletionFactor s) =ᶠ[𝓝 w]
    fun s : ℂ => soninMellinEvaluation s
      ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2))
  have hstrip : ∀ᶠ s in 𝓝 w, 1 / 2 < s.re ∧ s.re < 1 := by
    have hopen : IsOpen {s : ℂ | 1 / 2 < s.re ∧ s.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    exact hopen.mem_nhds ⟨hlo, hhi⟩
  filter_upwards [hstrip] with s hs
  rw [soninEval_eq_soninMellinIntegral ha
    (soninExtendedToSoninEvenExtended a ha f).property.1
    (soninExtendedToSoninEvenExtended a ha f).property.2 hs.1 hs.2,
    soninMellinEvaluation, soninMellinIntegral,
    soninExtendedToSoninEvenExtended_apply]
  have hintegral :
      (∫ t in Ioi (0 : ℝ), soninMellinKernel s t *
          (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) t) =
        ∫ t in Ioi (0 : ℝ),
          (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) t * soninMellinKernel s t := by
    refine integral_congr_ae ?_
    filter_upwards with t
    ring
  simp only [soninMellinKernel] at hintegral ⊢
  rw [hintegral]
  ring

/-- **Completed continuation jet descent.** Every finite jet of the
source-selected, Gamma-completed analytic continuation is represented by a
bounded functional on the literal extended Sonine carrier throughout the
open strip. -/
theorem exists_soninExtendedCompletedMellinContinuationJetEvaluator
    {a : ℝ} (ha : 0 < a) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    ∃ Λ : soninExtendedSpace a →L[ℂ] ℂ,
      ∀ f : soninExtendedSpace a,
        Λ f = iteratedDeriv k
          (fun s : ℂ => soninExtendedCompletedMellinContinuation a ha f s) w := by
  let U : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUsub : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1} := fun _ hz => hz
  have hfactor : AnalyticOnNhd ℂ mellinCompletionFactor U := by
    simpa only [U] using analyticOnNhd_mellinCompletionFactor_openStrip
  obtain ⟨Λ, hΛ⟩ := exists_soninEvaluatorJetMul ha hUopen hUsub hfactor k ⟨hw0, hw1⟩
  refine ⟨Λ.comp (soninExtendedToSoninEvenExtended a ha), fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, hΛ]
  rfl

/-- **Completed all-order Burnol jet bridge.** Every finite literal
Gamma-completed Mellin jet is represented by a bounded functional on the
source-selected extended Sonine carrier on its physical
absolute-convergence half-strip. -/
theorem exists_soninExtendedCompletedMellinJetEvaluator
    {a : ℝ} (ha : 0 < a) (k : ℕ) {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re < 1) :
    ∃ Λ : soninExtendedSpace a →L[ℂ] ℂ,
      ∀ f : soninExtendedSpace a,
        Λ f = iteratedDeriv k
          (fun s : ℂ => soninMellinEvaluation s
            ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2))) w := by
  obtain ⟨Λ, hΛ⟩ := exists_soninExtendedCompletedMellinContinuationJetEvaluator
    ha k (by linarith) hhi
  refine ⟨Λ, fun f => ?_⟩
  calc
    Λ f = iteratedDeriv k
        (fun s : ℂ => soninExtendedCompletedMellinContinuation a ha f s) w := hΛ f
    _ = iteratedDeriv k
        (fun s : ℂ => soninMellinEvaluation s
          ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2))) w :=
      Filter.EventuallyEq.iteratedDeriv_eq k
        (eventuallyEq_soninEval_mul_completion_soninMellinEvaluation ha hlo hhi f)

end

end RHTower
