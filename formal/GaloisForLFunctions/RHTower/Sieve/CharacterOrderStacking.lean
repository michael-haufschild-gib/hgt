import GaloisForLFunctions.RHTower.Sieve.LadderCharacterRecursion

/-!
# Stacking the orders

A ladder of fixed order `J` controls the first `J` levels of the remainder chain.  Since each stage
only writes phases above its own base, the stages are nested and define a single character, and for
every `j` the levels of order `j` are controlled from the `j`-th stage on.
-/

noncomputable section

open Filter GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

variable {α θ : ℝ} {dq : ℝ → ℂ} {Mglob : ℝ}

/-- The threshold beyond which the order-`J+1` ladder closes. -/
noncomputable def stageThreshold (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) : ℝ :=
  (exists_ladder_state_bound (J + 1) (Nat.succ_pos J) halpha hαθ hθ1 hdq hdqb).choose

theorem one_le_stageThreshold (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) : 1 ≤ stageThreshold halpha hαθ hθ1 hdq hdqb J :=
  (exists_ladder_state_bound (J + 1) (Nat.succ_pos J) halpha hαθ hθ1 hdq hdqb).choose_spec.1

theorem stageThreshold_spec (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) :
    ∀ x₀ : ℝ, stageThreshold halpha hαθ hθ1 hdq hdqb J ≤ x₀ → ∀ Mq : ℝ,
      (∀ t : ℝ, x₀ ≤ t → ‖dq t‖ ≤ Mq) → Mq ≤ datumSlack (J + 1) →
      ∀ u₀ : ℕ → ℂ, (∀ n, ‖u₀ n‖ = 1) →
      ∀ k : ℕ, ∀ j : ℕ, j < J + 1 →
        ‖arithJumpProfile dq (characterSource
            (ladderChar (J + 1) dq θ (Real.sqrt x₀) x₀ u₀ (k + 1))) j
            (ladderBase θ (Real.sqrt x₀) x₀ (k + 1))‖
          ≤ ((ladderLen θ (Real.sqrt x₀) x₀ k) ^ j / ((j.factorial : ℕ) : ℝ))
              * (((J + 1 : ℕ) : ℝ) * Real.log (ladderBase θ (Real.sqrt x₀) x₀ (k + 1))) :=
  (exists_ladder_state_bound (J + 1) (Nat.succ_pos J) halpha hαθ hθ1 hdq hdqb).choose_spec.2

/-- The base point of stage `J`. -/
noncomputable def stageBase (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    ℕ → ℝ
  | 0 => stageThreshold halpha hαθ hθ1 hdq hdqb 0
  | (J + 1) => max (stageThreshold halpha hαθ hθ1 hdq hdqb (J + 1)) (stageBase halpha hαθ hθ1 hdq hdqb J + 1)

theorem stageBase_zero (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    stageBase halpha hαθ hθ1 hdq hdqb 0 = stageThreshold halpha hαθ hθ1 hdq hdqb 0 := rfl

theorem stageBase_succ (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) :
    stageBase halpha hαθ hθ1 hdq hdqb (J + 1)
      = max (stageThreshold halpha hαθ hθ1 hdq hdqb (J + 1)) (stageBase halpha hαθ hθ1 hdq hdqb J + 1) := rfl

theorem one_le_stageBase (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) :
    1 ≤ stageBase halpha hαθ hθ1 hdq hdqb J := by
  induction J with
  | zero => exact one_le_stageThreshold halpha hαθ hθ1 hdq hdqb 0
  | succ J ih =>
      rw [stageBase_succ]
      exact le_trans ih (le_trans (by linarith) (le_max_right _ _))

theorem stageThreshold_le_stageBase (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) : stageThreshold halpha hαθ hθ1 hdq hdqb J ≤ stageBase halpha hαθ hθ1 hdq hdqb J := by
  cases J with
  | zero => exact le_of_eq (stageBase_zero halpha hαθ hθ1 hdq hdqb).symm
  | succ J =>
      rw [stageBase_succ]
      exact le_max_left _ _

theorem stageBase_lt_succ (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob)
    (J : ℕ) : stageBase halpha hαθ hθ1 hdq hdqb J < stageBase halpha hαθ hθ1 hdq hdqb (J + 1) := by
  rw [stageBase_succ]
  exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem stageBase_mono (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    Monotone (stageBase halpha hαθ hθ1 hdq hdqb) :=
  monotone_nat_of_le_succ fun J => le_of_lt (stageBase_lt_succ halpha hαθ hθ1 hdq hdqb J)

theorem index_le_stageBase (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob)
    (J : ℕ) : (J : ℝ) ≤ stageBase halpha hαθ hθ1 hdq hdqb J := by
  induction J with
  | zero =>
      simp only [Nat.cast_zero]
      linarith [one_le_stageBase halpha hαθ hθ1 hdq hdqb 0]
  | succ J ih =>
      have h := stageBase_succ halpha hαθ hθ1 hdq hdqb J
      have h2 : stageBase halpha hαθ hθ1 hdq hdqb J + 1
          ≤ stageBase halpha hαθ hθ1 hdq hdqb (J + 1) := by
        rw [h]
        exact le_max_right _ _
      push_cast
      linarith

/-- The phases after stage `J`; stage `J` runs the ladder of order `J+1`. -/
noncomputable def stagePhases (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    ℕ → (ℕ → ℂ)
  | 0 => ladderLimit 1 dq θ (Real.sqrt (stageBase halpha hαθ hθ1 hdq hdqb 0)) (stageBase halpha hαθ hθ1 hdq hdqb 0)
      (fun _ => 1)
  | (J + 1) => ladderLimit (J + 2) dq θ (Real.sqrt (stageBase halpha hαθ hθ1 hdq hdqb (J + 1)))
      (stageBase halpha hαθ hθ1 hdq hdqb (J + 1)) (stagePhases halpha hαθ hθ1 hdq hdqb J)

theorem stagePhases_zero (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    stagePhases halpha hαθ hθ1 hdq hdqb 0
      = ladderLimit 1 dq θ (Real.sqrt (stageBase halpha hαθ hθ1 hdq hdqb 0)) (stageBase halpha hαθ hθ1 hdq hdqb 0)
        (fun _ => 1) := rfl

theorem stagePhases_succ (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) :
    stagePhases halpha hαθ hθ1 hdq hdqb (J + 1)
      = ladderLimit (J + 2) dq θ (Real.sqrt (stageBase halpha hαθ hθ1 hdq hdqb (J + 1)))
        (stageBase halpha hαθ hθ1 hdq hdqb (J + 1)) (stagePhases halpha hαθ hθ1 hdq hdqb J) := rfl

theorem norm_stagePhases (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) (J : ℕ) :
    ∀ n : ℕ, ‖stagePhases halpha hαθ hθ1 hdq hdqb J n‖ = 1 := by
  induction J with
  | zero =>
      intro n
      rw [stagePhases_zero]
      exact norm_ladderLimit 1 dq _ _ _ (fun _ => by simp) n
  | succ J ih =>
      intro n
      rw [stagePhases_succ]
      exact norm_ladderLimit (J + 2) dq _ _ _ ih n

end RHTower.Sieve

end
