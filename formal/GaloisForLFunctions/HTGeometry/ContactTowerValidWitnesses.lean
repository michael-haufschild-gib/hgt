import GaloisForLFunctions.HTGeometry.StokesContactProfile

/-!
# Valid contact towers exist at every depth

Admissibility of a contact tower is nonnegative terminal height, strictly descending levels and
genuine ramification at every step.  Nothing exhibited one.  The unit-height leaf is valid, and
stacking a doubling step at each successive integer level produces a valid tower of every depth,
so the complementary-contact and loss laws are not statements about an empty class.

The positive-ramification prefix condition is realized by the empty prefix and by every list of
genuine steps.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- The nonnegative leaf is valid. -/
theorem ContactTower.valid_leaf {h : ℚ} (hh : 0 ≤ h) : (ContactTower.leaf h).Valid := hh

/-- A genuine step over a valid tower of lower top height is valid. -/
theorem ContactTower.valid_step {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (hfactor : 1 < factor) (hlevel : tail.top < level) (htail : tail.Valid) :
    (ContactTower.step level factor tail).Valid :=
  ⟨hfactor, hlevel, htail⟩

/-- The canonical doubling tower of a given depth: a ramification-two step at every integer
level. -/
def ContactTower.stack : ℕ → ContactTower
  | 0 => ContactTower.leaf 0
  | n + 1 => ContactTower.step ((n : ℚ) + 1) 2 (ContactTower.stack n)

theorem ContactTower.top_stack_le (n : ℕ) : (ContactTower.stack n).top ≤ (n : ℚ) := by
  cases n with
  | zero => simp [ContactTower.stack, ContactTower.top]
  | succ k =>
      simp only [ContactTower.stack, ContactTower.top]
      push_cast
      linarith

/-- **The doubling tower is valid at every depth.** -/
theorem ContactTower.valid_stack (n : ℕ) : (ContactTower.stack n).Valid := by
  induction n with
  | zero => exact ContactTower.valid_leaf le_rfl
  | succ k ih =>
      refine ContactTower.valid_step (by norm_num) ?_ ih
      have := ContactTower.top_stack_le k
      linarith

/-- Valid towers exist at every depth. -/
theorem exists_valid_contactTower (n : ℕ) : ∃ t : ContactTower, t.Valid :=
  ⟨ContactTower.stack n, ContactTower.valid_stack n⟩

/-- The empty prefix has positive ramification. -/
theorem positiveContactPrefix_nil : PositiveContactPrefix [] := by
  intro step hstep
  exact absurd hstep (List.not_mem_nil)

/-- A prefix of genuine steps has positive ramification. -/
theorem positiveContactPrefix_of_forall {steps : List (ℚ × ℕ)}
    (h : ∀ s ∈ steps, 0 < s.2) : PositiveContactPrefix steps := h

/-- A doubling prefix of any length has positive ramification. -/
theorem positiveContactPrefix_replicate (n : ℕ) (level : ℚ) :
    PositiveContactPrefix (List.replicate n (level, 2)) := by
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  norm_num

end IrregularStokes
end GaloisForLFunctions
