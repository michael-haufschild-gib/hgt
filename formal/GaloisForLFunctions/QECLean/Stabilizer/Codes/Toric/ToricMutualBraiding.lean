import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.KnotChernSimonsBridge

/-!
# Chern--Simons mutual braiding on toric homology

The mod-two toric Chern--Simons linking pairing controls whether the concrete phase `R`-matrix
acts by identity or by double braiding.  This realizes the abelian mutual-braiding action on every
pair of toric `H₁` charges.  It is not a Jones or colored-Jones construction.
-/

namespace Quantum.Stabilizer.Lattice

open GaloisForLFunctions.HTGeometry.KnotTheory

noncomputable section

/-- Mutual braiding of two toric charges: trivial linking acts identically; nontrivial linking
acts by the double braid of `i · SWAP`. -/
def toricMutualBraidingAction (a b : toricH1 (L := 2)) (f : PairState) : PairState :=
  if toricChernSimonsLinking a b = 0 then f else rAction (rAction f)

/-- The toric mutual-braiding action is exactly scalar multiplication by its Chern--Simons link
phase. -/
theorem toricMutualBraidingAction_eq_phase (a b : toricH1 (L := 2)) (f : PairState) :
    toricMutualBraidingAction a b f =
      z2ChernSimonsLinkPhase (toricChernSimonsLinking a b) • f := by
  unfold toricMutualBraidingAction
  split_ifs with h
  · simp [z2ChernSimonsLinkPhase, h]
  · simp only [z2ChernSimonsLinkPhase, if_neg h]
    simpa using rAction_square f

/-- The fundamental horizontal/vertical toric Wilson pair realizes the R-matrix double braid. -/
theorem toricMutualBraidingAction_fundamental (f : PairState) :
    toricMutualBraidingAction toricHorizontalWilsonLoop toricVerticalWilsonLoop f =
      rAction (rAction f) := by
  simp [toricMutualBraidingAction, toricChernSimonsLinking_fundamental]

/-- Alternating toric self-linking produces no mutual-braiding phase. -/
theorem toricMutualBraidingAction_self (a : toricH1 (L := 2)) (f : PairState) :
    toricMutualBraidingAction a a f = f := by
  rw [toricMutualBraidingAction_eq_phase, toricChernSimonsLinking_self]
  simp [z2ChernSimonsLinkPhase]

end

end Quantum.Stabilizer.Lattice
