import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.Sieve.MultiBlockFrame

/-!
# Supercritical sharpness mechanisms for sieve window length

The square-root-log sieve window has a natural-valued ceiling profile.  Monotonicity lets the
paper's sequential-touch dichotomy identify either full unit growth or a concrete adjacent scale
where the discrete window does not change.
-/

noncomputable section

namespace RHTower.Sieve

/-- Integer ceiling of the square-root-log short-interval length at natural scale `n + 1`. -/
def cardLengthHalfCeil (n : ℕ) : ℕ :=
  ⌈cardLength (1 / 2 : ℝ) ((n : ℝ) + 1)⌉₊

/-- The square-root-log window ceiling is monotone in natural scale. -/
theorem cardLengthHalfCeil_monotone : Monotone cardLengthHalfCeil := by
  intro i j hij
  apply Nat.ceil_mono
  refine cardLength_mono (β := (1 / 2 : ℝ)) (y := (i : ℝ) + 1)
    (z := (j : ℝ) + 1) (by norm_num) ?_ ?_
  · have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · exact_mod_cast Nat.add_le_add_right hij 1

/-- Across any `t` adjacent natural scales, the discrete square-root-log window either gains at
least `t` cells or exposes a scale at which its ceiling stalls. -/
theorem cardLengthHalfCeil_grows_or_exists_stall (N t : ℕ) :
    cardLengthHalfCeil N + t ≤ cardLengthHalfCeil (N + t) ∨
      ∃ i < t, cardLengthHalfCeil (N + (i + 1)) = cardLengthHalfCeil (N + i) := by
  have hmono : Monotone (fun i ↦ cardLengthHalfCeil (N + i)) := by
    intro i j hij
    exact cardLengthHalfCeil_monotone (Nat.add_le_add_left hij N)
  simpa [Nat.add_assoc] using
    (GaloisForLFunctions.HTGeometry.accumulates_touches_or_exists_stall
      (fun i ↦ cardLengthHalfCeil (N + i)) t hmono)

end RHTower.Sieve
