import GaloisForLFunctions.HTGeometry.ComplexTimeEulerShellGeneration

/-!
# Reflected Euler-shell cofinal selection

Every real character is admitted by some finite reflected shell fibre, while admission by every
fibre above the normalization wall forces the neutral character.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- Simultaneous admission of a real shell tilt and its reflected mate at every base point above
the normalization wall. -/
def GloballyReflectedShellAdmitted (m : ℕ) (t : ℝ) : Prop :=
  ∀ σ : ℝ, 1 < σ →
    Summable (fun n : ℕ => shellProbability m σ n *
      Real.exp (t * shellCenteredScore m σ n)) ∧
    Summable (fun n : ℕ => shellProbability m σ n *
      Real.exp ((-t) * shellCenteredScore m σ n))

/-- A shell tilt is summable everywhere inside its exact shifted half-plane. -/
theorem summable_shellRealPartition_terms {m : ℕ} (hm : m ≠ 0)
    {σ t : ℝ} (hσ : 1 < σ) (hst : 1 < σ + t) :
    Summable (fun n : ℕ => shellProbability m σ n *
      Real.exp (t * shellCenteredScore m σ n)) := by
  let c : ℝ := Real.exp (t * shellScoreMean m σ) / shellMellin m σ
  have hs : Summable (fun n : ℕ => c * shellMass m (σ + t) n) :=
    (summable_shellMass m hst).mul_left c
  refine hs.congr fun n => ?_
  exact (shellRealPartition_term_eq_shiftedMass hm hσ t n).symm

/-- Every fixed real character is admitted at some finite reflected shell fibre. -/
theorem exists_finite_reflectedShellAdmission {m : ℕ} (hm : m ≠ 0) (t : ℝ) :
    ∃ σ : ℝ, 1 < σ ∧
      Summable (fun n : ℕ => shellProbability m σ n *
        Real.exp (t * shellCenteredScore m σ n)) ∧
      Summable (fun n : ℕ => shellProbability m σ n *
        Real.exp ((-t) * shellCenteredScore m σ n)) := by
  let σ : ℝ := 2 + |t|
  have hσ : 1 < σ := by
    dsimp [σ]
    linarith [abs_nonneg t]
  have hplus : 1 < σ + t := by
    dsimp [σ]
    linarith [neg_le_abs t]
  have hminus : 1 < σ + (-t) := by
    dsimp [σ]
    linarith [le_abs_self t]
  exact ⟨σ, hσ, summable_shellRealPartition_terms hm hσ hplus,
    summable_shellRealPartition_terms hm hσ hminus⟩

/-- Reflected global shell admission is invariant under the functional-equation sign action. -/
theorem globallyReflectedShellAdmitted_neg (m : ℕ) (t : ℝ) :
    GloballyReflectedShellAdmitted m (-t) ↔ GloballyReflectedShellAdmitted m t := by
  constructor <;> intro h σ hσ
  · simpa only [neg_neg] using (h σ hσ).symm
  · simpa only [neg_neg] using (h σ hσ).symm

/-- **Literal cofinal formation/properness selector.**  A real character and its reflected mate
are admitted by every marked Euler-shell fibre above the normalization wall exactly when the
character is neutral. -/
theorem globallyReflectedShellAdmitted_iff {m : ℕ} (hm : 12 ≤ m) (t : ℝ) :
    GloballyReflectedShellAdmitted m t ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    let σ : ℝ := 1 + |t|
    have hσ : 1 < σ := by
      dsimp [σ]
      linarith [abs_pos.mpr ht]
    obtain ⟨hplus, hminus⟩ := h σ hσ
    by_cases htp : 0 < t
    · have htime : -t = -shellNegativeLifetime σ := by
        simp [σ, shellNegativeLifetime, abs_of_pos htp]
      apply not_summable_shellRealPartition_at_wall hm hσ
      simpa only [htime] using hminus
    · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htp) ht
      have htime : t = -shellNegativeLifetime σ := by
        simp [σ, shellNegativeLifetime, abs_of_neg htneg]
      apply not_summable_shellRealPartition_at_wall hm hσ
      simpa only [htime] using hplus
  · rintro rfl
    intro σ hσ
    have hs := (hasSum_shellProbability (by omega : m ≠ 0) hσ).summable
    constructor <;> simpa using hs

/-- Capstone: finite-stage survival, reflected symmetry, and cofinal selection hold on the same
literal arithmetic shell family. -/
theorem reflectedShellCofinalSelection_capstone {m : ℕ} (hm : 12 ≤ m) (t : ℝ) :
    (∃ σ : ℝ, 1 < σ ∧
      Summable (fun n : ℕ => shellProbability m σ n *
        Real.exp (t * shellCenteredScore m σ n)) ∧
      Summable (fun n : ℕ => shellProbability m σ n *
        Real.exp ((-t) * shellCenteredScore m σ n))) ∧
    (GloballyReflectedShellAdmitted m (-t) ↔
      GloballyReflectedShellAdmitted m t) ∧
    (GloballyReflectedShellAdmitted m t ↔ t = 0) := by
  exact ⟨exists_finite_reflectedShellAdmission (by omega) t,
    globallyReflectedShellAdmitted_neg m t,
    globallyReflectedShellAdmitted_iff hm t⟩

end GaloisForLFunctions.HTGeometry
