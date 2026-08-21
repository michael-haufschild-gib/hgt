import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.AbelianChernSimons

/-!
# Finite toric Abelian gauge shadow of the Seiberg--Witten invariant

This product construction places the finite spinor-curvature invariant beside the existing mod-two
toric Chern--Simons linking charge.  It records exactly what survives mechanically in the corpus:
phase-gauge invariance of the spinor coordinate and bilinearity of the topological coordinate.

This is not a Seiberg--Witten invariant of a four-manifold.  In particular, the toric factor is a
`ZMod 2` lattice-gauge charge, not a `Spinᶜ` structure or a continuum `U(1)` connection.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Quantum.Stabilizer.Lattice

/-- Joint finite Abelian spinor-curvature and toric linking record. -/
def seibergWittenToricGaugeShadow (ψ : SeibergWittenSpinor)
    (a b : toricH1 (L := 2)) : SeibergWittenCurvature × ZMod 2 :=
  (seibergWittenInvariant ψ, toricChernSimonsLinking a b)

/-- The spinor coordinate of the toric gauge shadow is invariant under common phase gauge. -/
theorem seibergWittenToricGaugeShadow_gaugeInvariant
    (u : Circle) (ψ : SeibergWittenSpinor) (a b : toricH1 (L := 2)) :
    seibergWittenToricGaugeShadow (u • ψ) a b =
      seibergWittenToricGaugeShadow ψ a b := by
  unfold seibergWittenToricGaugeShadow
  rw [seibergWittenInvariant_gaugeInvariant]

/-- The toric linking coordinate is additive in its first gauge charge. -/
theorem seibergWittenToricGaugeShadow_add_left
    (ψ : SeibergWittenSpinor) (a b c : toricH1 (L := 2)) :
    seibergWittenToricGaugeShadow ψ (a + b) c =
      (seibergWittenInvariant ψ,
        toricChernSimonsLinking a c + toricChernSimonsLinking b c) := by
  unfold seibergWittenToricGaugeShadow
  rw [toricChernSimonsLinking_add_left]

/-- The toric linking coordinate is additive in its second gauge charge. -/
theorem seibergWittenToricGaugeShadow_add_right
    (ψ : SeibergWittenSpinor) (a b c : toricH1 (L := 2)) :
    seibergWittenToricGaugeShadow ψ a (b + c) =
      (seibergWittenInvariant ψ,
        toricChernSimonsLinking a b + toricChernSimonsLinking a c) := by
  unfold seibergWittenToricGaugeShadow
  rw [toricChernSimonsLinking_add_right]

/-- Alternation forces the toric self-linking coordinate of every joint shadow to vanish. -/
theorem seibergWittenToricGaugeShadow_self
    (ψ : SeibergWittenSpinor) (a : toricH1 (L := 2)) :
    seibergWittenToricGaugeShadow ψ a a = (seibergWittenInvariant ψ, 0) := by
  unfold seibergWittenToricGaugeShadow
  rw [toricChernSimonsLinking_self]

/-- The fundamental horizontal--vertical toric pair has unit linking coordinate. -/
theorem seibergWittenToricGaugeShadow_fundamental (ψ : SeibergWittenSpinor) :
    seibergWittenToricGaugeShadow ψ toricHorizontalWilsonLoop toricVerticalWilsonLoop =
      (seibergWittenInvariant ψ, 1) := by
  unfold seibergWittenToricGaugeShadow
  rw [toricChernSimonsLinking_fundamental]

end GaloisForLFunctions.HTGeometry
