import Mathlib.Data.Rat.Lemmas

/-!
# The standard multiplicative height on the rational numbers

The maximum of the absolute reduced numerator and positive denominator
controls both archimedean size and the size of denominator-cleared differences.
-/

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction

/-- Standard multiplicative Weil height `max(|num q|, den q)` on `ℚ`. -/
def weilHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

theorem weilHeight_pos (q : ℚ) : 0 < weilHeight q :=
  q.den_pos.trans_le (le_max_right _ _)

theorem num_natAbs_le_weilHeight (q : ℚ) : q.num.natAbs ≤ weilHeight q := le_max_left _ _

theorem den_le_weilHeight (q : ℚ) : q.den ≤ weilHeight q := le_max_right _ _

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction
