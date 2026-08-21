/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebra

/-!
# The split cyclic algebra representation

For the parameter `1`, a cyclic Galois algebra acts on the coefficient field viewed as a
`K`-vector space.  Coefficients act by left multiplication and the cyclic variable acts by the
chosen Galois generator.  This gives a concrete representation of the raw quotient in
`End_K(L)`, proves that its coefficient copy is faithful, and proves the quotient is nontrivial.

Surjectivity or injectivity of the entire representation is the remaining normal-form/descent
step needed to identify this split cyclic algebra with `End_K(L)`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- The coefficient field acts on itself by left multiplication. -/
noncomputable abbrev cyclicGaloisAlgebraSplitCoefficientAction : L →+* Module.End K L :=
  (Algebra.lmul K L).toRingHom

/-- The chosen cyclic Galois generator acts as a `K`-linear endomorphism of its coefficient
field. -/
noncomputable abbrev cyclicGaloisAlgebraSplitGeneratorAction : Module.End K L :=
  (cyclicGaloisGenerator K L).toLinearMap

/-- Taking powers commutes with passage from the Galois automorphism to its linear action. -/
omit [FiniteDimensional K L] [IsGalois K L] in
theorem cyclicGaloisGenerator_toLinearMap_pow (q : ℕ) :
    (cyclicGaloisGenerator K L).toLinearMap ^ q =
      ((cyclicGaloisGenerator K L) ^ q).toLinearMap := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [pow_succ, pow_succ, ih]
    rfl

/-- The generator action has order equal to the degree of the cyclic Galois extension. -/
theorem cyclicGaloisAlgebraSplitGeneratorAction_pow_finrank :
    cyclicGaloisAlgebraSplitGeneratorAction K L ^ Module.finrank K L = 1 := by
  rw [← cyclicGaloisGenerator_orderOf K L]
  rw [cyclicGaloisGenerator_toLinearMap_pow]
  ext x
  simp only [Module.End.one_apply]
  change ((cyclicGaloisGenerator K L) ^ orderOf (cyclicGaloisGenerator K L)) x = x
  rw [pow_orderOf_eq_one]
  simp

/-- The coefficient and generator actions satisfy every skew commutation relation required by
the universal cyclic-algebra lift. -/
theorem cyclicGaloisAlgebraSplit_actions_commute (m : Multiplicative ℕ) (x : L) :
    cyclicGaloisAlgebraSplitCoefficientAction K L
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) x) *
      cyclicPowerMonoidHom (cyclicGaloisAlgebraSplitGeneratorAction K L) m =
    cyclicPowerMonoidHom (cyclicGaloisAlgebraSplitGeneratorAction K L) m *
      cyclicGaloisAlgebraSplitCoefficientAction K L x := by
  ext z
  unfold cyclicGaloisAlgebraSplitCoefficientAction cyclicGaloisAlgebraSplitGeneratorAction
    cyclicPowerRingAut cyclicPowerMonoidHom
  change (Algebra.lmul K L
      (((cyclicGaloisGenerator K L).toRingEquiv ^ (toAdd m)) x) *
        ((cyclicGaloisGenerator K L).toLinearMap ^ (toAdd m))) z =
    (((cyclicGaloisGenerator K L).toLinearMap ^ (toAdd m)) * Algebra.lmul K L x) z
  rw [cyclicGaloisGenerator_toLinearMap_pow]
  simp [Module.End.mul_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul]

/-- The split raw cyclic Galois algebra acts on `L` through left multiplication by coefficients
and the Galois generator. -/
noncomputable def cyclicGaloisAlgebraSplitRepresentation :
    cyclicGaloisAlgebra K L 1 →+* Module.End K L :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L)
    (cyclicGaloisAlgebraSplit_actions_commute K L) (by
      change cyclicGaloisAlgebraSplitGeneratorAction K L ^ Module.finrank K L =
        cyclicGaloisAlgebraSplitCoefficientAction K L (algebraMap K L (1 : K))
      simp only [map_one]
      exact cyclicGaloisAlgebraSplitGeneratorAction_pow_finrank K L)

/-- The split representation sends a coefficient to its left-multiplication endomorphism. -/
theorem cyclicGaloisAlgebraSplitRepresentation_C (b : L) :
    cyclicGaloisAlgebraSplitRepresentation K L (cyclicGaloisAlgebraC K L 1 b) =
      Algebra.lmul K L b := by
  unfold cyclicGaloisAlgebraSplitRepresentation
  exact cyclicAlgebraLift_C (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L) _ _ b

/-- The split representation sends the cyclic generator to the chosen Galois action. -/
theorem cyclicGaloisAlgebraSplitRepresentation_X :
    cyclicGaloisAlgebraSplitRepresentation K L (cyclicGaloisAlgebraX K L 1) =
      cyclicGaloisAlgebraSplitGeneratorAction K L := by
  unfold cyclicGaloisAlgebraSplitRepresentation
  exact cyclicAlgebraLift_X (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L (1 : K)) (cyclicGaloisAlgebraSplitCoefficientAction K L)
    (cyclicGaloisAlgebraSplitGeneratorAction K L) _ _

/-- The coefficient field embeds faithfully into the split raw cyclic algebra. -/
theorem cyclicGaloisAlgebraSplit_C_injective :
    Function.Injective (cyclicGaloisAlgebraC K L 1) := by
  intro x y hxy
  have hrepresentation := congrArg (cyclicGaloisAlgebraSplitRepresentation K L) hxy
  rw [cyclicGaloisAlgebraSplitRepresentation_C,
    cyclicGaloisAlgebraSplitRepresentation_C] at hrepresentation
  have hone := LinearMap.congr_fun hrepresentation 1
  change x * 1 = y * 1 at hone
  simpa using hone

/-- The split raw cyclic Galois algebra is not the zero ring. -/
theorem cyclicGaloisAlgebraSplit_one_ne_zero : (1 : cyclicGaloisAlgebra K L 1) ≠ 0 := by
  intro hzero
  have hrepresentation := congrArg (cyclicGaloisAlgebraSplitRepresentation K L) hzero
  rw [map_one, map_zero] at hrepresentation
  exact one_ne_zero hrepresentation

end GaloisForLFunctions.HTGeometry.ABHN
