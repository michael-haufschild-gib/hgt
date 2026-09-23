import GaloisForLFunctions.RHTower.Sieve.LargeSieveFinset

/-!
# The sharp large sieve from a circle-separation hypothesis

Arithmetic families are separated in `ℝ/ℤ`, not in `ℝ`; `fareySet_sep`, for instance, produces a
lower bound for `toIntDist`.  The circle distance never exceeds the ordinary one — it is the
distance to the *nearest* integer, and `0` is one of them — so a circle-separation hypothesis is
stronger, and the sharp bound of `LargeSieveFinset.lean` applies unchanged.
-/

namespace RHTower.Sieve

open Finset

/-- The circle distance never exceeds the ordinary distance to the origin. -/
theorem toIntDist_le_abs (x : ℝ) : toIntDist x ≤ |x| := by
  rcases lt_or_ge (1 / 2 : ℝ) |x| with h | h
  · exact le_trans (toIntDist_le_half x) (le_of_lt h)
  · rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq]
      exact toIntDist_le_half x
    · rw [toIntDist_eq_abs_of_abs_lt_half hlt]

/-- **The sharp large sieve under a circle-separation hypothesis.** -/
theorem largeSieve_gallagher_circle (N : ℕ) (hN : 0 < N) (c : Fin N → ℂ) (s : Finset ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hne : s.Nonempty)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ toIntDist (x - y))
    (hmem : ∀ x ∈ s, δ / 2 ≤ x ∧ x + δ / 2 ≤ 1) :
    ∑ x ∈ s, ‖expSum N c x‖ ^ (2 : ℕ)
      ≤ (1 / δ + 4 * Real.pi * (N : ℝ)) * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  refine largeSieve_gallagher_finset N hN c s hδ hne (fun x hx y hy hxy => ?_) hmem
  exact le_trans (hsep x hx y hy hxy) (toIntDist_le_abs (x - y))

end RHTower.Sieve
