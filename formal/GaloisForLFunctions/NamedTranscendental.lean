import Mathlib

/-!
# A concrete named transcendental real number, transcendental over ℚ

This mathlib toolchain provides Liouville's construction (`liouvilleNumber`,
`liouville_liouvilleNumber`, `Liouville.transcendental`) but only concludes transcendence over `ℤ`,
and provides no positivity.  This file supplies both:

* `transcendental_int_to_rat` — transcendence over `ℤ` upgrades to transcendence over `ℚ`
  (`ℚ = Frac ℤ`, via `IsFractionRing.isAlgebraic_iff`);
* `liouvilleConst` — the Liouville constant `∑ 1/10^{n!}`, a concrete positive real, proved
  `Transcendental ℚ` and `> 0`.

It is the concrete transcendental shift needed to make the shifted-value independence results
unconditional at a named number.
-/

open scoped Nat

namespace GaloisForLFunctions

/-- Transcendence over `ℤ` upgrades to transcendence over `ℚ`, the fraction field of `ℤ`. -/
theorem transcendental_int_to_rat {x : ℝ} (h : Transcendental ℤ x) : Transcendental ℚ x :=
  fun hAlg => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hAlg)

/-- The Liouville constant `∑ₙ 10^{−n!}` — a concrete transcendental real. -/
noncomputable def liouvilleConst : ℝ := liouvilleNumber 10

/-- The Liouville constant is transcendental over `ℚ`. -/
theorem liouvilleConst_transcendental : Transcendental ℚ liouvilleConst :=
  transcendental_int_to_rat (liouville_liouvilleNumber (by norm_num)).transcendental

/-- The Liouville constant is strictly positive. -/
theorem liouvilleConst_pos : 0 < liouvilleConst := by
  unfold liouvilleConst liouvilleNumber
  exact Summable.tsum_pos (LiouvilleNumber.summable (by norm_num)) (fun i => by positivity) 0
    (by norm_num [Nat.factorial])

end GaloisForLFunctions
