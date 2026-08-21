import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.AbelianChernSimons
import GaloisForLFunctions.HTGeometry.KnotTheory.RMatrix

/-!
# `Z₂` Chern--Simons phase and double braiding

The toric-code Chern--Simons layer supplies a mod-two linking exponent.  The phase braiding from
`HTGeometry.KnotTheory.RMatrix` has double braiding `-1`; this file records their exact agreement
on the fundamental horizontal/vertical Wilson pair.  It is an abelian mutual-braiding bridge, not
a non-abelian Chern--Simons or Jones-polynomial construction.
-/

namespace Quantum.Stabilizer.Lattice

open GaloisForLFunctions.HTGeometry.KnotTheory

noncomputable section

/-- The `Z₂` Wilson-link phase associated to a mod-two linking exponent. -/
def z2ChernSimonsLinkPhase (linking : ZMod 2) : ℂ :=
  if linking = 0 then 1 else -1

/-- Fundamental horizontal and vertical Wilson loops have the nontrivial `Z₂` link phase. -/
theorem z2ChernSimonsLinkPhase_fundamental :
    z2ChernSimonsLinkPhase
      (toricChernSimonsLinking toricHorizontalWilsonLoop toricVerticalWilsonLoop) = -1 := by
  rw [toricChernSimonsLinking_fundamental]
  simp [z2ChernSimonsLinkPhase]

/-- The double braid phase of `i · SWAP` matches the fundamental toric `Z₂` Wilson-link phase. -/
theorem rAction_double_braid_matches_toric_link
    (f : PairState) :
    rAction (rAction f) =
      z2ChernSimonsLinkPhase
        (toricChernSimonsLinking toricHorizontalWilsonLoop toricVerticalWilsonLoop) • f := by
  rw [z2ChernSimonsLinkPhase_fundamental]
  simpa using rAction_square f

end

end Quantum.Stabilizer.Lattice
