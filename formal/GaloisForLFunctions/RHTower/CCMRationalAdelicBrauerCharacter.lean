/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.RHTower.CCMRationalAdelicAzumayaResidue
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter

/-!
# Canonical local Brauer characters for the rational adelic route

The Connes--Tate local source cannot factor through an additive complex-valued Brauer observable:
such an observable is forced to vanish.  If the expected local Brauer invariant is supplied,
however, composing it with the canonical circle character of `ℚ/ℤ` gives a faithful nonlinear
local phase.  This is the available ABHN-side carrier for a future comparison with a Tate local
factor.

No equality with the Connes--Tate local zeta integral is claimed here.
-/

namespace GaloisForLFunctions.RHTower

open IsDedekindDomain Rat.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The faithful complex phase obtained by composing a supplied local Brauer invariant with the
canonical circle character of `ℚ/ℤ`. -/
noncomputable def ccmRationalLocalBrauerStdAddChar
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt) :
    AddChar (BrauerGroup (CCMRationalLocalField v)) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom
    (ccmRationalLocalInvariantAddEquivOfPadic v invariant).toAddMonoidHom

/-- A supplied local invariant makes the canonical local Brauer phase faithful. -/
theorem ccmRationalLocalBrauerStdAddChar_injective
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt) :
    Function.Injective (ccmRationalLocalBrauerStdAddChar v invariant) := by
  exact ratModIntStdAddChar_injective.comp
    (ccmRationalLocalInvariantAddEquivOfPadic v invariant).injective

/-- The canonical local Brauer phase is one exactly for the split Brauer class. -/
theorem ccmRationalLocalBrauerStdAddChar_eq_one_iff_eq_zero
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt)
    (x : BrauerGroup (CCMRationalLocalField v)) :
    ccmRationalLocalBrauerStdAddChar v invariant x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply ccmRationalLocalBrauerStdAddChar_injective v invariant
    rw [hx]
    exact (ccmRationalLocalBrauerStdAddChar v invariant).map_zero_eq_one.symm
  · intro hx
    rw [hx]
    exact (ccmRationalLocalBrauerStdAddChar v invariant).map_zero_eq_one

/-- A nonsplit local Brauer class has a nontrivial canonical phase. -/
theorem ccmRationalLocalBrauerStdAddChar_ne_one_of_ne_zero
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt)
    (x : BrauerGroup (CCMRationalLocalField v)) (hx : x ≠ 0) :
    ccmRationalLocalBrauerStdAddChar v invariant x ≠ 1 := by
  intro hchar
  exact hx (ccmRationalLocalBrauerStdAddChar_eq_one_iff_eq_zero v invariant x |>.mp hchar)

end

end GaloisForLFunctions.RHTower
