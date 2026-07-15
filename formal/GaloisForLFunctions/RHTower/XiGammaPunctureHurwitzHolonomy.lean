import GaloisForLFunctions.HTGeometry.GammaPunctureLaurentCover
import GaloisForLFunctions.RHTower.XiHurwitzConstraintOrientation

/-!
# The Xi-Hurwitz character is the inverse-Gamma puncture holonomy

The monodromy scalar already controlling the Xi-indexed Hurwitz differential matroid is exactly
the holonomy of the generic fractional section on the source-derived inverse-Gamma puncture.  This
is an unconditional value identification for every exponent.  It connects the HT source puncture
to the RH orientation character but supplies no positivity or critical-line assertion.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry HurwitzOrbit

/-- Exact cross-lane value relation between inverse-Gamma puncture holonomy and Hurwitz monodromy. -/
theorem gammaPunctureFractionalHolonomy_eq_monoScalar (s : ℂ) :
    gammaPunctureFractionalHolonomy s = monoScalar s := by
  rfl

/-- At an actual Xi-divisor point, the same source holonomy is the canonical orientation
character used by the Xi-Hurwitz criterion. -/
theorem gammaPunctureFractionalHolonomy_eq_xiHurwitzMonodromyCharacter
    (ρ : XiDivisorSupport) :
    gammaPunctureFractionalHolonomy (ρ : ℂ) =
      xiHurwitzMonodromyCharacter ρ := by
  rfl

/-- The inverse-Gamma fractional section therefore acquires the exact Xi-Hurwitz character under
one puncture loop. -/
theorem gammaPunctureFractionalMode_shift_xiHurwitz
    (ρ : XiDivisorSupport) (z : ℂ) :
    gammaPunctureFractionalMode (ρ : ℂ)
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      xiHurwitzMonodromyCharacter ρ *
        gammaPunctureFractionalMode (ρ : ℂ) z := by
  rw [gammaPunctureFractionalMode_shift,
    gammaPunctureFractionalHolonomy_eq_xiHurwitzMonodromyCharacter]

end

end RHTower
