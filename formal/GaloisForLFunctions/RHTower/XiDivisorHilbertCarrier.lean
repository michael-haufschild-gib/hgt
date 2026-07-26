import GaloisForLFunctions.RHTower.XiCanonicalProduct
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Minimal Hilbert carrier of the multiplicity-exact Xi divisor

This module isolates the square-summable carrier used by Deninger's closed divisor generator from
the substantially heavier Cauchy-kernel and Weil-positivity theory.
-/

namespace RHTower

/-- Hilbert space of square-summable functions on multiplicity copies of the Xi divisor. -/
abbrev XiDivisorL2 : Type := lp (fun _ : XiZeroCopy => ℂ) 2

end RHTower
