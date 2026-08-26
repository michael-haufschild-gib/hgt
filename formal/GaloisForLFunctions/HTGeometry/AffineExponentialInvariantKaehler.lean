import GaloisForLFunctions.HTGeometry.CoLieKaehler
import GaloisForLFunctions.HTGeometry.AffineExponentialCoLieClassification
import GaloisForLFunctions.HTGeometry.AffineExponentialPointEvaluation
import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing

/-!
# Invariant Kähler differentials on the mixed affine-exponential group

This file defines the invariant one-form with prescribed torus-logarithmic and additive
coefficients on `Gₘⁿ × Gₐⁿ`.  It proves two exact comparison formulas: pulling the form back to a
point gives the expected logarithmic/additive Kähler differential, and pulling it back to the
identity gives the already-classified mixed co-Lie vector.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialInvariantKaehler

open AffineExponentialGroup AffineGroupScheme
open AffineExponentialCoLieClassification
open AffineExponentialPointEvaluation

noncomputable section

variable (k : Type*) [Field k]

/-- Algebra structure on a target field induced by evaluation at a mixed point. -/
@[reducible] noncomputable def pointAlgebra {L : Type*} [Field L] [Algebra k L]
    {n : ℕ} (p : Point L n) : Algebra (CoordinateAlgebra k n) L :=
  algHomTargetAlgebra (eval (k := k) p)

/-- Pullback of Kähler differentials along evaluation at a mixed point, restricted to a
base-field-linear map so its type does not depend on a local algebra instance. -/
noncomputable def pointKaehlerMap {L : Type*} [Field L] [Algebra k L]
    {n : ℕ} (p : Point L n) :
    Ω[CoordinateAlgebra k n⁄k] →ₗ[k] Ω[L⁄k] :=
  algHomKaehlerMap (eval (k := k) p)

theorem pointKaehlerMap_D {L : Type*} [Field L] [Algebra k L]
    {n : ℕ} (p : Point L n) (f : CoordinateAlgebra k n) :
    pointKaehlerMap k p (KaehlerDifferential.D k (CoordinateAlgebra k n) f) =
      KaehlerDifferential.D k L (eval (k := k) p f) := by
  exact algHomKaehlerMap_D (eval (k := k) p) f

/-- Invariant mixed one-form with torus-logarithmic coefficients `tor` and additive coefficients
`add`. -/
def mixedInvariantKaehlerVector {n : ℕ} (tor add : Fin n → k) :
    Ω[CoordinateAlgebra k n⁄k] :=
  (∑ i, (algebraMap k (CoordinateAlgebra k n) (tor i) *
      torusCharacter k (-(Finsupp.single i 1))) •
        KaehlerDifferential.D k (CoordinateAlgebra k n)
          (torusCharacter k (Finsupp.single i 1))) +
    ∑ i, algebraMap k (CoordinateAlgebra k n) (add i) •
      KaehlerDifferential.D k (CoordinateAlgebra k n) (additiveCoordinate k i)

/-- Identity pullback of the invariant Kähler form is the corresponding mixed co-Lie vector. -/
theorem kaehlerToCoLie_mixedInvariantKaehlerVector {n : ℕ}
    (tor add : Fin n → k) :
    kaehlerToCoLie (mixedInvariantKaehlerVector k tor add) =
      mixedCoLieVector k tor add := by
  classical
  simp only [mixedInvariantKaehlerVector, map_add, map_sum, map_smul,
    kaehlerToCoLie_D, mixedCoLieVector]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [smul_coLie]
    simp [counit_torusCharacter]
  · apply Finset.sum_congr rfl
    intro i _
    rw [smul_coLie]
    simp

/-- Point pullback of the invariant Kähler form is the concrete finite sum of logarithmic torus
differentials and additive-coordinate differentials. -/
theorem pointKaehlerMap_mixedInvariantKaehlerVector
    {L : Type*} [Field L] [Algebra k L]
    {n : ℕ} (p : Point L n) (tor add : Fin n → k) :
    pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) =
      (∑ i, (algebraMap k L (tor i) *
          (AlgebraicTorusCharacter.character (torusPart p)
            (-(Finsupp.single i 1)) : L)) •
        KaehlerDifferential.D k L
          (AlgebraicTorusCharacter.character (torusPart p)
            (Finsupp.single i 1) : L)) +
      ∑ i, algebraMap k L (add i) •
        KaehlerDifferential.D k L (additivePart p i) := by
  classical
  letI : Algebra (CoordinateAlgebra k n) L := pointAlgebra k p
  letI : IsScalarTower k (CoordinateAlgebra k n) L :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k L c = eval (k := k) p (algebraMap k (CoordinateAlgebra k n) c)
      simp
  unfold pointKaehlerMap mixedInvariantKaehlerVector
  change (KaehlerDifferential.map k k (CoordinateAlgebra k n) L) _ = _
  simp only [map_add, map_sum, map_smul, KaehlerDifferential.map_D]
  have hbase (c : k) :
      algebraMap (CoordinateAlgebra k n) L
          (algebraMap k (CoordinateAlgebra k n) c) = algebraMap k L c := by
    exact (IsScalarTower.algebraMap_apply k (CoordinateAlgebra k n) L c).symm
  have htorus (m : Fin n →₀ ℤ) :
      algebraMap (CoordinateAlgebra k n) L (torusCharacter k m) =
        (AlgebraicTorusCharacter.character (torusPart p) m : L) := by
    change eval (k := k) p (torusCharacter k m) = _
    exact eval_torusCharacter p m
  have hadd (i : Fin n) :
      algebraMap (CoordinateAlgebra k n) L (additiveCoordinate k i) =
        additivePart p i := by
    change eval (k := k) p (additiveCoordinate k i) = _
    exact eval_additiveCoordinate p i
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [← IsScalarTower.algebraMap_smul L]
    rw [map_mul, hbase, htorus, htorus]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← IsScalarTower.algebraMap_smul L]
    rw [hbase, hadd]

end

end AffineExponentialInvariantKaehler
end GaloisForLFunctions.HTGeometry
