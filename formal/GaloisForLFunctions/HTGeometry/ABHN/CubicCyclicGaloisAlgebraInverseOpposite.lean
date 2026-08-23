import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraInverseOpposite

/-!
# Cubic cyclic parameter inversion on Brauer classes

The all-degree inverse-parameter opposite equivalence specializes to the cubic `H²` parameter
model.  Negation of a cubic unit parameter therefore agrees exactly with Brauer inversion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
  [FiniteDimensional K L] [IsGalois K L]

/-- The cubic and all-degree central-simple-algebra packages represent the same Brauer class. -/
theorem brauerClass_cubicCyclicGaloisAlgebraCSA_eq_generic
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha) =
      brauerClass (cyclicGaloisAlgebraCSA K L a ha) := by
  exact brauerClass_eq_of_algEquiv _ _ AlgEquiv.refl

/-- Parameter inversion is Brauer inversion for a nonzero cubic cyclic Galois algebra. -/
theorem cubicCyclicGaloisAlgebra_brauerTensorNeg
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    brauerTensorNeg K (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) =
      brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a⁻¹ (inv_ne_zero ha)) := by
  calc
    brauerTensorNeg K (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) =
      brauerTensorNeg K (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) := by
        rw [brauerClass_cubicCyclicGaloisAlgebraCSA_eq_generic K L hdeg a ha]
    _ = brauerClass (cyclicGaloisAlgebraCSA K L a⁻¹ (inv_ne_zero ha)) :=
      cyclicGaloisAlgebra_brauerTensorNeg K L a ha
    _ = brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a⁻¹ (inv_ne_zero ha)) := by
      rw [brauerClass_cubicCyclicGaloisAlgebraCSA_eq_generic K L hdeg a⁻¹]

/-- Negation of a cubic cyclic `H²` unit parameter agrees with Brauer inversion. -/
theorem cubicCyclicGaloisH2Parameter_brauerTensorNeg
    (hdeg : Module.finrank K L = 3) (a : Additive Kˣ) :
    brauerTensorNeg K (brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg a)) =
      brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg (-a)) := by
  change brauerTensorNeg K
    (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg (a.toMul : K) a.toMul.ne_zero)) =
      brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg ((-a).toMul : K) (-a).toMul.ne_zero)
  simpa only [toMul_neg, Units.val_inv_eq_inv_val] using
    cubicCyclicGaloisAlgebra_brauerTensorNeg K L hdeg (a.toMul : K) a.toMul.ne_zero

end GaloisForLFunctions.HTGeometry.ABHN
