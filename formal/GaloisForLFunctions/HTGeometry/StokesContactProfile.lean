import Mathlib

/-!
# Complementary contact profiles for ramified Stokes data

A finite ramification profile is evaluated by successive positive affine contractions.  Its
complementary contact is the top pole height minus the reciprocal-ramification path integral.
This file proves that identity recursively and proves the strict comparison principle responsible
for diagonal and nested separation.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- A finite contact branch.  A step at height `level` has relative ramification `factor`; the
terminal leaf stores the final contact height. -/
inductive ContactTower where
  | leaf (height : ℚ)
  | step (level : ℚ) (factor : ℕ) (tail : ContactTower)

namespace ContactTower

/-- Top height of a contact tower. -/
def top : ContactTower → ℚ
  | .leaf height => height
  | .step level _ _ => level

/-- Complementary contact obtained by recursive reciprocal-ramification averaging. -/
def contact : ContactTower → ℚ
  | .leaf height => height
  | .step level factor tail =>
      level * (1 - 1 / (factor : ℚ)) + contact tail / (factor : ℚ)

/-- Reciprocal-ramification path integral from terminal height to top height. -/
def loss : ContactTower → ℚ
  | .leaf _ => 0
  | .step level factor tail =>
      (level - top tail) / (factor : ℚ) + loss tail / (factor : ℚ)

/-- Admissibility: nonnegative terminal height, strictly descending levels, and genuine
ramification at every step. -/
def Valid : ContactTower → Prop
  | .leaf height => 0 ≤ height
  | .step level factor tail => 1 < factor ∧ top tail < level ∧ Valid tail

/-- Universal complementary-contact law: contact plus reciprocal-ramification loss equals top
height. -/
theorem contact_eq_top_sub_loss (t : ContactTower) : t.contact = t.top - t.loss := by
  induction t with
  | leaf height => simp [contact, top, loss]
  | step level factor tail ih =>
      change level * (1 - 1 / (factor : ℚ)) + tail.contact / (factor : ℚ) =
        level - ((level - tail.top) / (factor : ℚ) + tail.loss / (factor : ℚ))
      rw [ih]
      ring

/-- Reciprocal-ramification loss is nonnegative on every admissible branch. -/
theorem loss_nonneg {t : ContactTower} (h : t.Valid) : 0 ≤ t.loss := by
  induction t with
  | leaf height => simp [loss]
  | step level factor tail ih =>
      simp only [Valid] at h
      simp only [loss]
      have hfactorNat : 0 < factor := Nat.zero_lt_of_lt h.1
      have hfactor : 0 < (factor : ℚ) := by exact_mod_cast hfactorNat
      exact add_nonneg (div_nonneg (sub_nonneg.mpr h.2.1.le) hfactor.le)
        (div_nonneg (ih h.2.2) hfactor.le)

/-- A nontrivial admissible branch has strictly positive reciprocal-ramification loss. -/
theorem loss_step_pos {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (h : (ContactTower.step level factor tail).Valid) :
    0 < (ContactTower.step level factor tail).loss := by
  simp only [Valid] at h
  simp only [loss]
  have hfactorNat : 0 < factor := Nat.zero_lt_of_lt h.1
  have hfactor : 0 < (factor : ℚ) := by exact_mod_cast hfactorNat
  exact add_pos_of_pos_of_nonneg (div_pos (sub_pos.mpr h.2.1) hfactor)
    (div_nonneg (loss_nonneg h.2.2) hfactor.le)

/-- Strict form of the complementary-contact law below the top vertex. -/
theorem contact_lt_top_step {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (h : (ContactTower.step level factor tail).Valid) :
    (ContactTower.step level factor tail).contact <
      (ContactTower.step level factor tail).top := by
  rw [contact_eq_top_sub_loss]
  exact sub_lt_self _ (loss_step_pos h)

end ContactTower

/-- Apply a common sequence of fission levels and relative ramification factors to a terminal
contact. -/
def applyContactPrefix : List (ℚ × ℕ) → ℚ → ℚ
  | [], terminal => terminal
  | (level, factor) :: steps, terminal =>
      level * (1 - 1 / (factor : ℚ)) +
        applyContactPrefix steps terminal / (factor : ℚ)

/-- Every relative ramification factor in a contact prefix is positive. -/
def PositiveContactPrefix (steps : List (ℚ × ℕ)) : Prop :=
  ∀ step ∈ steps, 0 < step.2

/-- A common positive-ramification prefix is a strictly increasing function of its terminal
contact. -/
theorem applyContactPrefix_strictMono {steps : List (ℚ × ℕ)}
    (hsteps : PositiveContactPrefix steps) :
    StrictMono (applyContactPrefix steps) := by
  induction steps with
  | nil =>
      intro a b hab
      simpa [applyContactPrefix] using hab
  | cons step steps ih =>
      intro a b hab
      simp only [applyContactPrefix]
      have hstep : 0 < (step.2 : ℚ) := by
        exact_mod_cast hsteps step (by simp)
      have htail : PositiveContactPrefix steps := by
        intro x hx
        exact hsteps x (by simp [hx])
      simpa [add_comm] using
        add_lt_add_left (div_lt_div_of_pos_right (ih htail hab) hstep)
          (step.1 * (1 - 1 / (step.2 : ℚ)))

/-- Strict diagonal separation after cancelling the common contact prefix. -/
theorem strict_diagonal_from_positive_continuation {steps : List (ℚ × ℕ)}
    (hsteps : PositiveContactPrefix steps) {self terminal : ℚ} (h : self < terminal) :
    applyContactPrefix steps self < applyContactPrefix steps terminal :=
  applyContactPrefix_strictMono hsteps h

/-- Strict nested separation after cancelling the common contact prefix. -/
theorem strict_nested_from_positive_prefix {steps : List (ℚ × ℕ)}
    (hsteps : PositiveContactPrefix steps) {lower higher : ℚ} (h : lower < higher) :
    applyContactPrefix steps lower < applyContactPrefix steps higher :=
  applyContactPrefix_strictMono hsteps h

end IrregularStokes
end GaloisForLFunctions
