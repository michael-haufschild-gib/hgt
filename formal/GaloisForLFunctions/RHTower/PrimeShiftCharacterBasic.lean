import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces

/-!
# Basic normalized prime-shift coefficient fields

Small foundational definitions shared by prime-shift summability, tail, and
Marcinkiewicz arguments.  Keeping them independent of the residue-domain
construction permits finite coefficient estimates to compile without pulling
in that analytic closure machinery.
-/

noncomputable section

namespace RHTower

/-- The normalized prime shift character of a complex point, as a prime
coefficient field. -/
noncomputable def primeShiftCharacter (z : ℂ) : ℕ → ℂ :=
  fun n => if n.Prime then (n : ℂ) ^ ((1 : ℂ) / 2 - z) else 0

/-- The absolute-value field of a complex coefficient field. -/
noncomputable def absField (b : ℕ → ℂ) : ℕ → ℝ := fun n => ‖b n‖

theorem absField_nonneg (b : ℕ → ℂ) (n : ℕ) : 0 ≤ absField b n := norm_nonneg _

end RHTower

end
