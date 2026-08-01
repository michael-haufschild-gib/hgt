import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw
import GaloisForLFunctions.HTGeometry.WeakInteractionRecurrenceSingularityLaw

/-!
# Countable recurrence singularity law

Arbitrarily small perturbations can be invisible to every bounded-time
operator-norm probe while changing exact infinite-time recurrence
statistics by a strict amount.  This file proves that tension for every
resonant finite window inside an arbitrary countable, possibly unbounded,
pure-point Hamiltonian.

The same perturbation is globally self-adjoint and Schatten-1, preserves
the maximal domain, saturates every finite projective relation, and drives
all replica orders of the chosen window to their permutation floors.
-/

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Countable recurrence singularity.**  Let a finite observed window of
an arbitrary countable pure-point Hamiltonian have any exact projective
resonance.  Within every positive operator-norm budget there is one
absolutely summable diagonal perturbation such that:

* the global interaction is bounded self-adjoint and Schatten-1;
* the perturbed unbounded Hamiltonian is self-adjoint on the unchanged
  maximal domain;
* every bounded-time observable on the window obeys the dimension-free
  Duhamel bound;
* every replica order reaches its permutation collision floor;
* at some finite order the completed collision statistic drops strictly.
-/
theorem exists_arbitrarilyWeak_countableRecurrenceSingularity
    {I J : Type*} [Countable I] [Fintype J] [DecidableEq J]
    (energy : I → ℝ) (e : J ↪ I)
    {weight : J → ℝ} (hweight : ∀ j, 0 < weight j)
    (hresonant : ¬ MaximallyProjectiveEnergy (energy ∘ e))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : I → ℝ), ∃ hw : Summable (fun i => |w i|),
      ‖realSummableDiagonalOperator w hw‖ < δ ∧
      IsSelfAdjoint (realSummableDiagonalOperator w hw) ∧
      RHTower.MemSchattenClass 1
        (realSummableDiagonalOperator w hw) ∧
      RHTower.maximalRealDiagonalDomain
          (fun i => energy i + w i) =
        RHTower.maximalRealDiagonalDomain energy ∧
      IsSelfAdjoint
        (RHTower.maximalRealDiagonal (fun i => energy i + w i)) ∧
      (∀ (O : RHTower.FiniteIndexClockSpace J →L[ℂ]
          RHTower.FiniteIndexClockSpace J) (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                ((fun i => energy i + w i) ∘ e))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  ((fun i => energy i + w i) ∘ e)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian (energy ∘ e))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (energy ∘ e))))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ n : ℕ,
        fidelityReplicaCollisionMass weight
            ((fun i => energy i + w i) ∘ e) n =
          fidelityReplicaPermutationFloor weight n) ∧
      ∃ n : ℕ,
        fidelityReplicaCollisionMass weight (energy ∘ e) n >
          fidelityReplicaCollisionMass weight
            ((fun i => energy i + w i) ∘ e) n := by
  obtain ⟨w, hw, hpoint, hnorm, hself, htrace, hdomain,
      hHamiltonian, hmax⟩ :=
    exists_arbitrarilyWeak_traceClassDiagonalHamiltonian_saturating
      energy δ hδ
  let before : J → ℝ := energy ∘ e
  let after : J → ℝ :=
    (fun i => energy i + w i) ∘ e
  have hwindowNorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian after -
          RHTower.finiteIndexDiagonalHamiltonian before‖ ≤ δ := by
    apply finiteIndexDiagonalHamiltonian_norm_sub_le
      after before δ hδ.le
    intro j
    simpa [after, before, Function.comp_apply] using
      (hpoint (e j)).le
  have hfinite : ∀
      (O : RHTower.FiniteIndexClockSpace J →L[ℂ]
        RHTower.FiniteIndexClockSpace J) (t : ℝ),
      ‖exp (t • ((-Complex.I) •
            RHTower.finiteIndexDiagonalHamiltonian after)) * O *
            star (exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian after))) -
          exp (t • ((-Complex.I) •
            RHTower.finiteIndexDiagonalHamiltonian before)) * O *
            star (exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian before)))‖
        ≤ 2 * |t| * δ * ‖O‖ := by
    intro O t
    calc
      _ ≤ 2 * |t| *
          ‖RHTower.finiteIndexDiagonalHamiltonian after -
            RHTower.finiteIndexDiagonalHamiltonian before‖ * ‖O‖ :=
        selfAdjoint_heisenbergEvolution_norm_sub_le
          (RHTower.finiteIndexDiagonalHamiltonian after)
          (RHTower.finiteIndexDiagonalHamiltonian before) O
          (finiteIndexDiagonalHamiltonian_isSelfAdjoint after)
          (finiteIndexDiagonalHamiltonian_isSelfAdjoint before) t
      _ ≤ 2 * |t| * δ * ‖O‖ := by gcongr
  have hafter : ∀ n : ℕ,
      fidelityReplicaCollisionMass weight after n =
        fidelityReplicaPermutationFloor weight n :=
    hmax.all_finiteWindow_collisionFloor e hweight
  obtain ⟨n, hbefore⟩ :=
    exists_replicaCollisionMass_strictlyAboveFloor_of_not_maximal
      hweight hresonant
  refine ⟨w, hw, hnorm, hself, htrace, hdomain, hHamiltonian,
    ?_, ?_, n, ?_⟩
  · simpa [after, before] using hfinite
  · simpa [after] using hafter
  · change fidelityReplicaCollisionMass weight before n >
      fidelityReplicaCollisionMass weight after n
    rw [hafter n]
    exact hbefore

end

end GaloisForLFunctions.HTGeometry
