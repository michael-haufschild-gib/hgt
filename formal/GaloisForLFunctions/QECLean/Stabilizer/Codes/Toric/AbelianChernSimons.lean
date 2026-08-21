import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.WrappingInvariants

/-!
# Abelian Chern--Simons linking on toric-code homology

The toric-code corpus already identifies first homology of the smallest nondegenerate torus with
`(Z/2Z)²`.  Its alternating intersection form is the linking exponent of the abelian `Z₂`
Chern--Simons/BF Wilson observable.  This is an abelian linking invariant, not a Jones polynomial:
the development contains no non-symmetric braid `R`-matrix or Markov trace.
-/

namespace Quantum.Stabilizer.Lattice

noncomputable section

local instance : Fact (0 < 2) := ⟨by omega⟩

/-- The two wrapping charges of the smallest nondegenerate toric code. -/
def toricWilsonCharge (a : toricH1 (L := 2)) : ZMod 2 × ZMod 2 :=
  phiLinearMap (L := 2) a

/-- Mod-two intersection form on toric first homology.

This is the linking exponent of the abelian `Z₂` Chern--Simons/BF Wilson observable. -/
def toricChernSimonsLinking (a b : toricH1 (L := 2)) : ZMod 2 :=
  (toricWilsonCharge a).1 * (toricWilsonCharge b).2 +
    (toricWilsonCharge a).2 * (toricWilsonCharge b).1

theorem toricWilsonCharge_add (a b : toricH1 (L := 2)) :
    toricWilsonCharge (a + b) = toricWilsonCharge a + toricWilsonCharge b := by
  exact (phiLinearMap (L := 2)).map_add a b

theorem toricChernSimonsLinking_add_left (a b c : toricH1 (L := 2)) :
    toricChernSimonsLinking (a + b) c =
      toricChernSimonsLinking a c + toricChernSimonsLinking b c := by
  simp only [toricChernSimonsLinking, toricWilsonCharge_add, Prod.fst_add, Prod.snd_add]
  ring

theorem toricChernSimonsLinking_add_right (a b c : toricH1 (L := 2)) :
    toricChernSimonsLinking a (b + c) =
      toricChernSimonsLinking a b + toricChernSimonsLinking a c := by
  simp only [toricChernSimonsLinking, toricWilsonCharge_add, Prod.fst_add, Prod.snd_add]
  ring

theorem toricChernSimonsLinking_self (a : toricH1 (L := 2)) :
    toricChernSimonsLinking a a = 0 := by
  rw [toricChernSimonsLinking, mul_comm (toricWilsonCharge a).2]
  rw [← two_mul]
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- Homology class of a horizontal fundamental Wilson loop. -/
noncomputable def toricHorizontalWilsonLoop : toricH1 (L := 2) :=
  (phi_surjective (L := 2) (1, 0)).choose

/-- Homology class of a vertical fundamental Wilson loop. -/
noncomputable def toricVerticalWilsonLoop : toricH1 (L := 2) :=
  (phi_surjective (L := 2) (0, 1)).choose

theorem toricWilsonCharge_horizontal :
    toricWilsonCharge toricHorizontalWilsonLoop = (1, 0) := by
  rw [toricWilsonCharge, ← phi_eq_phiLinearMap]
  exact (phi_surjective (L := 2) (1, 0)).choose_spec

theorem toricWilsonCharge_vertical :
    toricWilsonCharge toricVerticalWilsonLoop = (0, 1) := by
  rw [toricWilsonCharge, ← phi_eq_phiLinearMap]
  exact (phi_surjective (L := 2) (0, 1)).choose_spec

theorem toricChernSimonsLinking_fundamental :
    toricChernSimonsLinking toricHorizontalWilsonLoop toricVerticalWilsonLoop = 1 := by
  simp [toricChernSimonsLinking, toricWilsonCharge_horizontal, toricWilsonCharge_vertical]

end

end Quantum.Stabilizer.Lattice
