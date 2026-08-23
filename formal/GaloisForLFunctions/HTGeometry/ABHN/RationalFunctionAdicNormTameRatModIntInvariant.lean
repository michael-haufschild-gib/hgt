/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionAdicNormTameCharacter
import GaloisForLFunctions.HTGeometry.FiniteMilnorKOneRatModIntInvariant

/-!
# A `ℚ/ℤ`-valued norm-tame invariant at completed finite places of `F(t)`

Composing the completed local norm-tame Milnor invariant with the faithful finite-field embedding
`K₁ᴹ(F) ↪ ℚ/ℤ` produces an additive local invariant with the same target as ABHN.  Its standard
circle character is exactly the norm-normalized local phase already used in completed tame
reciprocity.

This is an ABHN-shaped tame invariant, not a Brauer invariant: a norm-residue comparison theorem is
still required to transfer it to central simple algebras.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt

universe u

noncomputable section

/-- The completed finite-place norm-tame Milnor invariant valued in `ℚ/ℤ`. -/
noncomputable def rationalFunctionFiniteAdicNormTameRatModIntInvariant
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2 →+ RatModInt :=
  (finiteMilnorKOneStdRatModIntInvariant F).comp
    (rationalFunctionFiniteAdicNormTameMilnorInvariant F q)

/-- Evaluation formula for the completed `ℚ/ℤ`-valued norm-tame invariant. -/
theorem rationalFunctionFiniteAdicNormTameRatModIntInvariant_apply
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameRatModIntInvariant F q x =
      finiteMilnorKOneStdRatModIntInvariant F
        (rationalFunctionFiniteAdicNormTameMilnorInvariant F q x) :=
  rfl

/-- The `ℚ/ℤ` invariant vanishes exactly on the norm-tame kernel. -/
theorem rationalFunctionFiniteAdicNormTameRatModIntInvariant_eq_zero_iff_mem_ker
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F)
    (x : MilnorKDeg ((polyPlace q.2.1).adicCompletion (RatFunc F)) 2) :
    rationalFunctionFiniteAdicNormTameRatModIntInvariant F q x = 0 ↔
      x ∈ (rationalFunctionFiniteAdicNormTameMilnorInvariant F q).ker := by
  rw [rationalFunctionFiniteAdicNormTameRatModIntInvariant_apply,
    finiteMilnorKOneStdRatModIntInvariant_eq_zero_iff]
  rfl

/-- The completed norm-tame phase is the standard circle character of the additive invariant. -/
theorem rationalFunctionFiniteAdicNormTameStdAddChar_eq_ratModInt_comp
    (F : Type u) [Field F] [Finite F] (q : MonicIrred F) :
    rationalFunctionFiniteAdicNormTameStdAddChar F q =
      ratModIntStdAddChar.compAddMonoidHom
        (rationalFunctionFiniteAdicNormTameRatModIntInvariant F q) :=
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
