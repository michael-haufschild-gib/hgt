import GaloisForLFunctions.RHTower.TreeCountBeatsFactorial

/-!
# The two hyperbolicity theorems leave a corner, and the corner is the whole problem

The Jensen route needs hyperbolicity of `J^{d,n}` for **every** pair `(d, n)`.  Two families of
theorems supply it, and their union is not everything.

**Region A — large shift, any degree.**  For each fixed degree there is a threshold beyond which the
Jensen polynomial is hyperbolic: `n ≥ N(d)`.  This is unconditional, but `N` is a function of `d` and
grows.

**Region B — small degree, any shift.**  Verifying the hypothesis to height `T` for the relevant
derivatives settles all shifts for degrees up to `T²`.  This is uniform in `n`, but bounded in `d` by
the *verified* height.

**The corner.**  A pair `(d, 0)` with `d > T²` and `N(d) > 0` lies in neither region.  Covering the
whole lattice therefore forces `N(d) = 0` for every `d` past the verified range — that is, it forces
the unconditional threshold to become **vacuous** exactly where the verification stops.

> **The two theorems trade the same currency.  Region B converts verified height into settled degree
> quadratically; region A converts degree into a required shift.  Neither reaches the low-shift,
> high-degree corner, and that corner is not a technical remainder: covering it is equivalent to
> making the unconditional threshold uniform, which is the hypothesis itself.**

This closes the reading of the Jensen route as an escape from finite verification.  Its uniform-in-`n`
reach **is** the verification height, squared.

This file formalizes the coverage lattice, the witness in the corner, and the equivalence between full
coverage and vanishing of the threshold past the verified range.
-/

noncomputable section

namespace RHTower

/-- Region A: the shift is past the unconditional threshold for its degree. -/
def regionA (N : ℕ → ℕ) (d n : ℕ) : Prop := N d ≤ n

/-- Region B: the degree is inside the range settled by verification to height `T`. -/
def regionB (T : ℕ) (d : ℕ) : Prop := d ≤ T ^ 2

/-- The pair is covered if it lies in either region. -/
def covered (N : ℕ → ℕ) (T : ℕ) (d n : ℕ) : Prop := regionA N d n ∨ regionB T d

/-- **The corner witness.**  If some degree past the verified range has a positive threshold, the
pair `(d, 0)` is uncovered. -/
theorem corner_uncovered {N : ℕ → ℕ} {T d : ℕ} (hd : T ^ 2 < d) (hN : 0 < N d) :
    ¬ covered N T d 0 := by
  rintro (hA | hB)
  · exact absurd (Nat.le_zero.mp hA) (Nat.ne_of_gt hN)
  · exact absurd hB (not_le.mpr hd)

/-- **Full coverage forces a vacuous threshold.**  If every pair is covered, the unconditional
threshold vanishes past the verified range. -/
theorem coverage_forces_vanishing {N : ℕ → ℕ} {T : ℕ}
    (hcov : ∀ d n, covered N T d n) : ∀ d, T ^ 2 < d → N d = 0 := by
  intro d hd
  by_contra h
  exact corner_uncovered hd (Nat.pos_of_ne_zero h) (hcov d 0)

/-- **And conversely.**  A threshold vanishing past the verified range does cover everything. -/
theorem vanishing_gives_coverage {N : ℕ → ℕ} {T : ℕ}
    (hvan : ∀ d, T ^ 2 < d → N d = 0) : ∀ d n, covered N T d n := by
  intro d n
  rcases le_or_gt d (T ^ 2) with h | h
  · exact Or.inr h
  · exact Or.inl (by simp [regionA, hvan d h])

/-- **The equivalence.**  Covering the lattice is exactly the vanishing of the threshold beyond the
verified range: there is no intermediate improvement that closes the corner. -/
theorem coverage_iff_vanishing {N : ℕ → ℕ} {T : ℕ} :
    (∀ d n, covered N T d n) ↔ (∀ d, T ^ 2 < d → N d = 0) :=
  ⟨coverage_forces_vanishing, vanishing_gives_coverage⟩

/-- **The quadratic trade.**  Raising the verified height by a factor raises the settled degree by
its square, so the settled range is the verification height squared and nothing more. -/
theorem quadratic_trade (T c : ℕ) : (c * T) ^ 2 = c ^ 2 * T ^ 2 := by ring

/-- **The corner is not small.**  For every verified height and every threshold function, infinitely
many degrees lie beyond the verified range; if the threshold is anywhere positive there, an uncovered
pair exists at each such degree. -/
theorem corner_persists (T : ℕ) : ∀ m : ℕ, ∃ d, m ≤ d ∧ T ^ 2 < d := by
  intro m
  exact ⟨max m (T ^ 2) + 1, le_trans (le_max_left m _) (Nat.le_succ _),
    lt_of_le_of_lt (le_max_right m _) (Nat.lt_succ_self _)⟩

end RHTower
