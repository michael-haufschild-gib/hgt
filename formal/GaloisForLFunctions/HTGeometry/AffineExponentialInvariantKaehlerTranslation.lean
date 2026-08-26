import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehlerMultiplication
import GaloisForLFunctions.HTGeometry.AffineExponentialPointClosure

/-!
# Translation invariance of mixed invariant Kähler forms

Right translation scales each torus character by its value at the translating point and shifts
each additive coordinate by its value there.  Since these values lie in the base field, their
universal differentials vanish.  Consequently the actual mixed logarithmic/additive one-form is
unchanged by every right translation.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialInvariantKaehler

open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialPointClosure

noncomputable section

/-- Right translation scales a torus character by its value at the translating point. -/
theorem rightTranslate_torusCharacter
    (k : Type*) [Field k] {n : ℕ} (q : Point k n) (m : Fin n →₀ ℤ) :
    rightTranslate q (torusCharacter k m) =
      algebraMap k (CoordinateAlgebra k n)
          (AlgebraicTorusCharacter.character (torusPart q) m : k) *
        torusCharacter k m := by
  rw [rightTranslate, AlgHom.comp_apply]
  change AffineExponentialPointClosure.rightSlice q
      (Coalgebra.comul (R := k) (torusCharacter k m)) = _
  rw [comul_torusCharacter]
  simp [AffineExponentialPointClosure.rightSlice, eval_torusCharacter, mul_comm]

/-- Right translation shifts an additive coordinate by its value at the translating point. -/
theorem rightTranslate_additiveCoordinate
    (k : Type*) [Field k] {n : ℕ} (q : Point k n) (i : Fin n) :
    rightTranslate q (additiveCoordinate k i) =
      additiveCoordinate k i +
        algebraMap k (CoordinateAlgebra k n) (additivePart q i) := by
  rw [rightTranslate, AlgHom.comp_apply]
  change AffineExponentialPointClosure.rightSlice q
      (Coalgebra.comul (R := k) (additiveCoordinate k i)) = _
  rw [comul_additiveCoordinate]
  simp only [map_add, AffineExponentialPointClosure.rightSlice,
    Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, map_one,
    mul_one, one_mul]
  rw [AlgHom.comp_apply, eval_additiveCoordinate]
  rfl

set_option maxHeartbeats 800000 in
/-- **Translation invariance.** Pullback of the actual mixed invariant Kähler form along right
translation by any base-field point is the same form. -/
theorem algHomKaehlerMap_rightTranslate_mixedInvariantKaehlerVector
    (k : Type*) [Field k] {n : ℕ} (q : Point k n)
    (tor add : Fin n → k) :
    algHomKaehlerMap (rightTranslate q)
        (mixedInvariantKaehlerVector k tor add) =
      mixedInvariantKaehlerVector k tor add := by
  classical
  have hconst (c : k) :
      KaehlerDifferential.D k (CoordinateAlgebra k n)
          (algebraMap k (CoordinateAlgebra k n) c) = 0 := by
    rw [← mul_one (algebraMap k (CoordinateAlgebra k n) c),
      ← Algebra.smul_def]
    simp
  rw [mixedInvariantKaehlerVector_normalized]
  simp only [map_add, map_sum, map_smul]
  apply congrArg₂ (fun x y => x + y)
  · apply Finset.sum_congr rfl
    intro i _
    rw [algHomKaehlerMap_smul, algHomKaehlerMap_D,
      rightTranslate_torusCharacter, rightTranslate_torusCharacter]
    rw [Derivation.leibniz]
    rw [hconst]
    simp only [smul_zero, add_zero]
    apply congrArg (fun z => tor i • z)
    rw [smul_smul]
    have hcancel :
        (AlgebraicTorusCharacter.character (torusPart q)
            (-(Finsupp.single i 1)) : k) *
          (AlgebraicTorusCharacter.character (torusPart q)
            (Finsupp.single i 1) : k) = 1 := by
      have h := congrArg (fun z : kˣ => (z : k))
        (AlgebraicTorusCharacter.character_add (torusPart q)
          (-(Finsupp.single i 1)) (Finsupp.single i 1))
      simpa using h.symm
    have hcoeff :
        ((algebraMap k (CoordinateAlgebra k n)
              (AlgebraicTorusCharacter.character (torusPart q)
                (-(Finsupp.single i 1)) : k)) *
            torusCharacter k (-(Finsupp.single i 1))) *
          algebraMap k (CoordinateAlgebra k n)
            (AlgebraicTorusCharacter.character (torusPart q)
              (Finsupp.single i 1) : k) =
        torusCharacter k (-(Finsupp.single i 1)) := by
      calc
        _ = (algebraMap k (CoordinateAlgebra k n)
                (AlgebraicTorusCharacter.character (torusPart q)
                  (-(Finsupp.single i 1)) : k) *
              algebraMap k (CoordinateAlgebra k n)
                (AlgebraicTorusCharacter.character (torusPart q)
                  (Finsupp.single i 1) : k)) *
            torusCharacter k (-(Finsupp.single i 1)) := by ac_rfl
        _ = algebraMap k (CoordinateAlgebra k n)
              ((AlgebraicTorusCharacter.character (torusPart q)
                  (-(Finsupp.single i 1)) : k) *
                (AlgebraicTorusCharacter.character (torusPart q)
                  (Finsupp.single i 1) : k)) *
            torusCharacter k (-(Finsupp.single i 1)) := by rw [map_mul]
        _ = _ := by rw [hcancel, map_one, one_mul]
    rw [hcoeff]
  · apply Finset.sum_congr rfl
    intro i _
    rw [algHomKaehlerMap_D, rightTranslate_additiveCoordinate, map_add]
    rw [hconst]
    simp

end

end AffineExponentialInvariantKaehler
end GaloisForLFunctions.HTGeometry
