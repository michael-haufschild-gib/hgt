/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalInvariants

/-!
# Brauer classes split over an algebraic closure

Every central simple algebra becomes a matrix algebra after scalar extension to an algebraically
closed field.  At the quotient level this says that the algebraic-closure scalar-extension map on
Brauer groups is zero.  It is the splitting input for the absolute-Galois-cohomology comparison;
the descent from this fact to continuous degree-two cohomology is separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- Every Brauer class becomes split after scalar extension to an algebraic closure. -/
theorem scalarExtensionBrauerMap_algebraicClosure_eq_split
    (K : Type*) [Field K] (x : BrauerGroup K) :
    scalarExtensionBrauerMap K (AlgebraicClosure K) x = brauerSplitClass (AlgebraicClosure K) :=
  brauerGroup_eq_split_of_isAlgClosed (AlgebraicClosure K)
    (scalarExtensionBrauerMap K (AlgebraicClosure K) x)

/-- Scalar extension from a field to its algebraic closure is the zero homomorphism on Brauer
groups. -/
theorem scalarExtensionBrauerAddHom_algebraicClosure_eq_zero
    (K : Type*) [Field K] :
    scalarExtensionBrauerAddHom K (AlgebraicClosure K) = 0 := by
  ext x
  change scalarExtensionBrauerMap K (AlgebraicClosure K) x = brauerSplitClass (AlgebraicClosure K)
  exact scalarExtensionBrauerMap_algebraicClosure_eq_split K x

end GaloisForLFunctions.HTGeometry.ABHN
