import GaloisForLFunctions.HTGeometry.PositiveObserverCompactResolventLaw

/-!
# Universal periodic observer lifts with escaping hidden action

Every periodic history in an arbitrary topological observer space admits a canonical lift through
the positive compact-resolvent model.  Observation retains the original period, while the hidden
coordinates run through an orthonormal sequence: no subsequence converges and the positive action
tends to infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- Periodic observer history, with its positive period stored as intrinsic data. -/
structure PeriodicObserverHistory (O : Type*) where
  value : ℕ → O
  period : ℕ
  period_pos : 0 < period
  periodic : ∀ n, value (n + period) = value n

namespace PeriodicObserverHistory

variable {O : Type*}

/-- Canonical lift obtained by attaching the `n`-th compact-resolvent hidden eigenmode. -/
def escapingLift (o : PeriodicObserverHistory O) (n : ℕ) :
    O × PositiveObserverHiddenL2 :=
  (o.value n, positiveObserverHiddenMode n)

/-- Projection of the lifted history has exactly the supplied observer period. -/
theorem escapingLift_observer_periodic (o : PeriodicObserverHistory O) (n : ℕ) :
    (o.escapingLift (n + o.period)).1 = (o.escapingLift n).1 :=
  o.periodic n

variable [TopologicalSpace O]

/-- Full graph action `‖x‖² + ⟨Lx,x⟩` from equation (11) of the paper. -/
def compactGeneratorGraphAction
    (x : positiveObserverCompactGenerator.domain) : ℝ :=
  ‖(x : PositiveObserverHiddenL2)‖ ^ 2 +
    positiveObserverCompactGeneratorAction x

/-- Exact graph-action value `1 + λ_n` on the normalized eigenmode with `λ_n = n + 1`. -/
theorem compactGeneratorGraphAction_eigenvector (n : ℕ) :
    compactGeneratorGraphAction (positiveObserverCompactGeneratorEigenvector n) = n + 2 := by
  rw [compactGeneratorGraphAction,
    positiveObserverCompactGeneratorAction_eigenvector]
  change ‖positiveObserverHiddenMode n‖ ^ 2 + ((n : ℝ) + 1) = (n : ℝ) + 2
  rw [positiveObserverHiddenMode_norm]
  ring

/-- Full graph action is invariant under a global unit complex phase. -/
theorem compactGeneratorGraphAction_phase_invariant
    (x : positiveObserverCompactGenerator.domain) (z : ℂ) (hz : ‖z‖ = 1) :
    compactGeneratorGraphAction (z • x) = compactGeneratorGraphAction x := by
  rw [compactGeneratorGraphAction, compactGeneratorGraphAction,
    positiveObserverCompactGeneratorAction_phase_invariant x z hz]
  congr 1
  change ‖z • (x : PositiveObserverHiddenL2)‖ ^ 2 = ‖(x : PositiveObserverHiddenL2)‖ ^ 2
  rw [norm_smul, hz, one_mul]

/-- Graph action of the hidden eigenmodes escapes to infinity. -/
theorem compactGeneratorGraphAction_tendsto_atTop :
    Tendsto
      (fun n => compactGeneratorGraphAction
        (positiveObserverCompactGeneratorEigenvector n)) atTop atTop := by
  simp only [compactGeneratorGraphAction_eigenvector]
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

/-- No strictly increasing subsequence of the lifted history converges. -/
theorem escapingLift_no_convergent_subsequence
    (o : PeriodicObserverHistory O) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : O × PositiveObserverHiddenL2) :
    ¬ Tendsto (fun n => o.escapingLift (φ n)) atTop (nhds x) := by
  intro hconv
  apply positiveObserverHiddenMode_subsequence_not_cauchy φ hφ
  have hhidden : Tendsto (fun n => positiveObserverHiddenMode (φ n)) atTop (nhds x.2) := by
    simpa [Function.comp_def, escapingLift] using
      (continuous_snd.tendsto x |>.comp hconv)
  exact hhidden.cauchySeq

/-- Packaged universal lift law: periodic observation, total lack of convergent lifted
subsequences, and escape of the hidden compact-resolvent action. -/
theorem has_escaping_compactResolvent_lift (o : PeriodicObserverHistory O) :
    (∀ n, (o.escapingLift (n + o.period)).1 = (o.escapingLift n).1) ∧
      (∀ (φ : ℕ → ℕ), StrictMono φ → ∀ x : O × PositiveObserverHiddenL2,
        ¬ Tendsto (fun n => o.escapingLift (φ n)) atTop (nhds x)) ∧
      Tendsto
        (fun n => compactGeneratorGraphAction
          (positiveObserverCompactGeneratorEigenvector n)) atTop atTop := by
  exact ⟨o.escapingLift_observer_periodic,
    fun φ hφ x => o.escapingLift_no_convergent_subsequence φ hφ x,
    compactGeneratorGraphAction_tendsto_atTop⟩

end PeriodicObserverHistory

end

end GaloisForLFunctions.HTGeometry
