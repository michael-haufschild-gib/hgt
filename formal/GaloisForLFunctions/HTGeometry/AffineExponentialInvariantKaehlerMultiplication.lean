import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehler

/-!
# Multiplication pullback of mixed invariant Kähler forms

The mixed logarithmic/additive form on `Gₐⁿ × Gₘⁿ` is invariant: pullback along group
multiplication is the sum of pullbacks from the two factors.  This file proves the identity on the
actual Hopf coordinate algebra.  The torus calculation is the universal `dlog(uv) = dlog u +
dlog v` law; the additive calculation is primitivity of the additive coordinates.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialInvariantKaehler

open AffineExponentialGroup

noncomputable section

variable (k : Type*) [Field k]

/-- The displayed invariant form is a base-field linear combination of normalized logarithmic and
additive coordinate differentials. -/
theorem mixedInvariantKaehlerVector_normalized {n : ℕ} (tor add : Fin n → k) :
    mixedInvariantKaehlerVector k tor add =
      (∑ i, tor i • ((torusCharacter k (-(Finsupp.single i 1))) •
        KaehlerDifferential.D k (CoordinateAlgebra k n)
          (torusCharacter k (Finsupp.single i 1)))) +
      ∑ i, add i • KaehlerDifferential.D k (CoordinateAlgebra k n)
        (additiveCoordinate k i) := by
  classical
  unfold mixedInvariantKaehlerVector
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    conv_rhs =>
      rw [← IsScalarTower.algebraMap_smul (CoordinateAlgebra k n) (tor i)]
      rw [smul_smul]
  · apply Finset.sum_congr rfl
    intro i _
    conv_rhs =>
      rw [← IsScalarTower.algebraMap_smul (CoordinateAlgebra k n) (add i)]

set_option maxHeartbeats 800000 in
/-- Pullback of a normalized torus logarithmic differential along multiplication is the sum of its
two factor pullbacks. -/
theorem algHomKaehlerMap_dlog_comul {n : ℕ} (m : Fin n →₀ ℤ) :
    letI : CommRing
        (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
    algHomKaehlerMap
        (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))
        ((torusCharacter k (-m)) •
          KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m)) =
      algHomKaehlerMap
          (Algebra.TensorProduct.includeLeft :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          ((torusCharacter k (-m)) •
            KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m)) +
        algHomKaehlerMap
          (Algebra.TensorProduct.includeRight :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          ((torusCharacter k (-m)) •
            KaehlerDifferential.D k (CoordinateAlgebra k n) (torusCharacter k m)) := by
  letI : CommRing
      (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
  rw [algHomKaehlerMap_smul, algHomKaehlerMap_D,
    algHomKaehlerMap_smul, algHomKaehlerMap_D,
    algHomKaehlerMap_smul, algHomKaehlerMap_D]
  change
    (Coalgebra.comul (R := k) (torusCharacter k (-m))) •
        KaehlerDifferential.D k
          (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (Coalgebra.comul (R := k) (torusCharacter k m)) = _
  rw [comul_torusCharacter, comul_torusCharacter]
  rw [show torusCharacter k m ⊗ₜ[k] torusCharacter k m =
      (torusCharacter k m ⊗ₜ[k] 1) * (1 ⊗ₜ[k] torusCharacter k m) by simp]
  rw [Derivation.leibniz]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  have hcancel : torusCharacter k (-m) * torusCharacter k m = 1 := by
    rw [← torusCharacter_add]
    simp
  rw [smul_add, smul_smul, smul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hcancel]
  simp [add_comm]

/-- Pullback of an additive coordinate differential along multiplication is the sum of its two
factor pullbacks. -/
theorem algHomKaehlerMap_additiveCoordinate_comul {n : ℕ} (i : Fin n) :
    letI : CommRing
        (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
    algHomKaehlerMap
        (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))
        (KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i)) =
      algHomKaehlerMap
          (Algebra.TensorProduct.includeLeft :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i)) +
        algHomKaehlerMap
          (Algebra.TensorProduct.includeRight :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i)) := by
  letI : CommRing
      (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
  rw [algHomKaehlerMap_D, algHomKaehlerMap_D, algHomKaehlerMap_D]
  change KaehlerDifferential.D k
      (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
      (Coalgebra.comul (R := k) (additiveCoordinate k i)) = _
  rw [comul_additiveCoordinate, map_add]
  rfl

set_option maxHeartbeats 800000 in
/-- **Invariant multiplication law.** Pullback of the actual mixed invariant Kähler form along
the Hopf multiplication morphism is the sum of its two factor pullbacks. -/
theorem algHomKaehlerMap_mixedInvariantKaehlerVector_comul {n : ℕ}
    (tor add : Fin n → k) :
    letI : CommRing
        (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
    algHomKaehlerMap
        (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))
        (mixedInvariantKaehlerVector k tor add) =
      algHomKaehlerMap
          (Algebra.TensorProduct.includeLeft :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (mixedInvariantKaehlerVector k tor add) +
        algHomKaehlerMap
          (Algebra.TensorProduct.includeRight :
            CoordinateAlgebra k n →ₐ[k]
              CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n)
          (mixedInvariantKaehlerVector k tor add) := by
  letI : CommRing
      (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) := inferInstance
  classical
  rw [mixedInvariantKaehlerVector_normalized, map_add, map_add, map_add]
  simp only [map_sum, map_smul]
  simp_rw [algHomKaehlerMap_dlog_comul, algHomKaehlerMap_additiveCoordinate_comul]
  simp only [smul_add, Finset.sum_add_distrib]
  abel

end

end AffineExponentialInvariantKaehler
end GaloisForLFunctions.HTGeometry
