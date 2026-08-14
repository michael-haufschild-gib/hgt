import GaloisForLFunctions.HTGeometry.MultivariateEntirePolarizedJet
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Directional derivatives of multivariate entire sources

The Frechet derivative of an entire source is again analytic, so every directional derivative is
another entire source.  Reading an ordered mixed jet through that operation strips one slot from
the word, which is the composition law `∂^γ ∘ ∂^β = ∂^{β+γ}` for the continuous jet observations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Frechet derivative of an entire source is analytic. -/
theorem analyticOnNhd_fderiv_multivariateEntire {d : ℕ} (g : MultivariateEntire d) :
    AnalyticOnNhd ℂ (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ)) Set.univ :=
  (MultivariateEntire.analyticOnNhd g).fderiv

/-- Every directional derivative of an entire source is differentiable. -/
theorem differentiable_fderiv_apply {d : ℕ} (g : MultivariateEntire d) (v : Fin d → ℂ) :
    Differentiable ℂ (fun x => fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) x v) := by
  have hdiff : Differentiable ℂ (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ)) := fun x =>
    ((analyticOnNhd_fderiv_multivariateEntire g) x (Set.mem_univ x)).differentiableAt
  exact hdiff.clm_apply (differentiable_const v)

/-- The directional derivative of an entire source, as an entire source. -/
def partialDerivEntire {d : ℕ} (v : Fin d → ℂ) (g : MultivariateEntire d) :
    MultivariateEntire d :=
  ⟨⟨fun x => fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) x v,
      (differentiable_fderiv_apply g v).continuous⟩,
    lineEntire_of_differentiable _ (differentiable_fderiv_apply g v)⟩

@[simp] theorem partialDerivEntire_apply {d : ℕ} (v : Fin d → ℂ) (g : MultivariateEntire d)
    (x : Fin d → ℂ) :
    (partialDerivEntire v g).1 x = fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) x v := rfl

/-- Evaluating the last slot commutes with iterated differentiation. -/
theorem iteratedFDeriv_partialDerivEntire {d n : ℕ} (v : Fin d → ℂ) (g : MultivariateEntire d)
    (x : Fin d → ℂ) (u : Fin n → (Fin d → ℂ)) :
    iteratedFDeriv ℂ n (partialDerivEntire v g).1 x u =
      iteratedFDeriv ℂ n (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ)) x u v := by
  have hcd : ContDiff ℂ (⊤ : WithTop ℕ∞) (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ)) :=
    (analyticOnNhd_fderiv_multivariateEntire g).contDiff
  have hcomp := (ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left
    (f := fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ)) (x := x) (hcd.contDiffAt (x := x)) (i := n)
    (show (n : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) by simp)
  have happ := congrArg
    (fun B : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ (Fin d → ℂ)) ℂ ↦ B u) hcomp
  simpa [partialDerivEntire, Function.comp_def] using happ

/-- **Stripping the last jet slot.**  An ordered mixed jet of a source is the shorter ordered jet
of its directional derivative in the last slot. -/
theorem orderedPartialJetEvalCLM_succ_right {d n : ℕ} (x : Fin d → ℂ)
    (word : Fin (n + 1) → Fin d) (g : MultivariateEntire d) :
    orderedPartialJetEvalCLM x word g =
      orderedPartialJetEvalCLM x (Fin.init word)
        (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) g) := by
  rw [orderedPartialJetEvalCLM_eq_iteratedFDeriv, orderedPartialJetEvalCLM_eq_iteratedFDeriv,
    iteratedFDeriv_partialDerivEntire, iteratedFDeriv_succ_apply_right]
  rfl

end

end GaloisForLFunctions.HTGeometry
