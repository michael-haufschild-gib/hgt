import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ambidextrous Kummer selection

Restriction along Kummer depth is compatible with every integer charge.  Covariant inclusion is
more rigid: its doubling defect is the negative charge in `ZMod (2 * n)`.  A nonzero charge is
therefore detected at every depth larger than its absolute value, and cofinal ambidextrous
flatness is equivalent to charge zero.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Defect between a charge at depth `2 * n` and twice its restricted representative at depth
`n`. -/
def ambidextrousDoublingDefect (n : ℕ) (q : ℤ) : ZMod (2 * n) :=
  (q : ZMod (2 * n)) - 2 * (q : ZMod (2 * n))

/-- The Kummer doubling defect is exactly the negative charge modulo `2 * n`. -/
@[simp] theorem ambidextrousDoublingDefect_eq (n : ℕ) (q : ℤ) :
    ambidextrousDoublingDefect n q = (-q : ZMod (2 * n)) := by
  unfold ambidextrousDoublingDefect
  ring

/-- Every nonzero integer charge is detected at every Kummer depth larger than its absolute
value. -/
theorem ambidextrousDoublingDefect_ne_zero
    {n : ℕ} {q : ℤ} (hq : q ≠ 0) (hqn : q.natAbs < n) :
    ambidextrousDoublingDefect n q ≠ 0 := by
  rw [ambidextrousDoublingDefect_eq]
  intro hzero
  have hzero' : ((-q : ℤ) : ZMod (2 * n)) = 0 := by simpa using hzero
  have hdvd : ((2 * n : ℕ) : ℤ) ∣ -q :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (-q) (2 * n)).mp hzero'
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd (neg_ne_zero.mpr hq)
  simp only [Int.natAbs_natCast, Int.natAbs_neg] at hle
  omega

/-- Cofinal ambidextrous Kummer flatness selects the zero charge, and zero charge is flat at every
depth. -/
theorem ambidextrousDoublingDefect_flat_iff (q : ℤ) :
    (∀ n : ℕ, q.natAbs < n → ambidextrousDoublingDefect n q = 0) ↔ q = 0 := by
  constructor
  · intro hflat
    by_contra hq
    exact ambidextrousDoublingDefect_ne_zero hq (Nat.lt_add_one q.natAbs)
      (hflat (q.natAbs + 1) (Nat.lt_add_one q.natAbs))
  · rintro rfl
    simp [ambidextrousDoublingDefect]

/-- Doubling defects preserve addition of integer charges. -/
theorem ambidextrousDoublingDefect_add (n : ℕ) (q r : ℤ) :
    ambidextrousDoublingDefect n (q + r) =
      ambidextrousDoublingDefect n q + ambidextrousDoublingDefect n r := by
  rw [ambidextrousDoublingDefect_eq, ambidextrousDoublingDefect_eq,
    ambidextrousDoublingDefect_eq]
  push_cast
  ring

/-- Doubling defects preserve negation of integer charges. -/
theorem ambidextrousDoublingDefect_neg (n : ℕ) (q : ℤ) :
    ambidextrousDoublingDefect n (-q) = -ambidextrousDoublingDefect n q := by
  rw [ambidextrousDoublingDefect_eq, ambidextrousDoublingDefect_eq]
  push_cast
  ring

/-- Lean-certified finite selector: cofinal vanishing of the restriction/inclusion defect is
equivalent to vanishing of the discrete charge. -/
theorem ambidextrousKummerSelection_capstone (q : ℤ) :
    q = 0 ↔ ∀ n : ℕ, q.natAbs < n → ambidextrousDoublingDefect n q = 0 := by
  simpa [eq_comm] using (ambidextrousDoublingDefect_flat_iff q).symm

end GaloisForLFunctions.HTGeometry
