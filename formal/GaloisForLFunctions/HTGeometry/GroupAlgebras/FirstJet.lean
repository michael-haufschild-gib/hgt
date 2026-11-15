import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# First-order quotients of abelian group algebras

For an abelian group `G`, the augmentation-square quotient of `R[G]` is
`R` extended by the square-zero module `R ⊗[ℤ] Additive G`. The map sends
`[g]` to `(1, 1 ⊗ g)`. Its inverse sends `1 ⊗ g` to `[g] - 1` modulo
the augmentation square; multiplication of two such differences proves additivity.

This retains torsion with integral coefficients and makes its behavior under
scalar extension explicit.
-/

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet
variable (R G : Type*) [CommRing R] [CommGroup G]

/-- Group-valued moments after extension of scalars. -/
abbrev MomentSpace := R ⊗[ℤ] Additive G

/-- Sum of group-algebra coefficients. -/
def augmentation : MonoidAlgebra R G →ₐ[R] R :=
  MonoidAlgebra.lift R R G 1

/-- The kernel of coefficient summation. -/
def augmentationIdeal : Ideal (MonoidAlgebra R G) := RingHom.ker (augmentation R G).toRingHom

/-- A group label as a unit in the square-zero extension. -/
def label : G →* TrivSqZeroExt R (MomentSpace R G) where
  toFun g := (1, 1 ⊗ₜ[ℤ] Additive.ofMul g)
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · change (1 : R) ⊗ₜ[ℤ] (Additive.ofMul a + Additive.ofMul b) = _
      simp [TensorProduct.tmul_add, add_comm]

/-- Augmentation together with the universal first moment. -/
def jet : MonoidAlgebra R G →ₐ[R] TrivSqZeroExt R (MomentSpace R G) :=
  MonoidAlgebra.lift R _ G (label R G)

@[simp] theorem augmentation_of (g : G) : augmentation R G (MonoidAlgebra.of R G g) = 1 := by
  simp [augmentation]

@[simp] theorem jet_of (g : G) :
    jet R G (MonoidAlgebra.of R G g) = (1, (1 : R) ⊗ₜ[ℤ] Additive.ofMul g) := by
  simp [jet, label]

theorem jet_fst (v : MonoidAlgebra R G) : (jet R G v).fst = augmentation R G v := by
  have h : (TrivSqZeroExt.fstHom R R (MomentSpace R G)).toLinearMap.comp
      (jet R G).toLinearMap = (augmentation R G).toLinearMap := by
    apply (MonoidAlgebra.basis G R).ext
    intro g
    change (jet R G (MonoidAlgebra.of R G g)).fst = augmentation R G (MonoidAlgebra.of R G g)
    rw [jet_of R G g, augmentation_of R G g]
    rfl
  exact LinearMap.congr_fun h v

@[simp] theorem augmentation_one : augmentation R G 1 = 1 := map_one _

theorem root_mem (g : G) : MonoidAlgebra.of R G g - 1 ∈ augmentationIdeal R G := by
  change augmentation R G (MonoidAlgebra.of R G g - 1) = 0
  rw [map_sub, augmentation_of R G g, map_one, sub_self]

theorem square_le_jet_ker : (augmentationIdeal R G)^2 ≤ RingHom.ker (jet R G).toRingHom := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change jet R G (a * b) = 0
  have ha0 : (jet R G a).fst = 0 := (jet_fst R G a).trans ha
  have hb0 : (jet R G b).fst = 0 := (jet_fst R G b).trans hb
  rw [map_mul]
  apply TrivSqZeroExt.ext
  · simp [ha0, hb0]
  · simp [TrivSqZeroExt.snd_mul, ha0, hb0]

abbrev SquareQuotient := MonoidAlgebra R G ⧸ (augmentationIdeal R G)^2

def quotientMap : MonoidAlgebra R G →ₐ[R] SquareQuotient R G :=
  Ideal.Quotient.mkₐ R ((augmentationIdeal R G)^2)

/-- Multiplicative labels become additive after killing products of roots. -/
def quotientRoot : Additive G →+ SquareQuotient R G where
  toFun g := quotientMap R G (MonoidAlgebra.of R G g.toMul) - 1
  map_zero' := by
    change quotientMap R G (MonoidAlgebra.of R G 1) - 1 = 0
    rw [map_one, map_one, sub_self]
  map_add' a b := by
    have hm : (MonoidAlgebra.of R G a.toMul - 1) *
        (MonoidAlgebra.of R G b.toMul - 1) ∈ (augmentationIdeal R G)^2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (root_mem R G a.toMul) (root_mem R G b.toMul)
    have hz : quotientMap R G ((MonoidAlgebra.of R G a.toMul - 1) *
        (MonoidAlgebra.of R G b.toMul - 1)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_mul, map_sub, map_sub, map_one] at hz
    change quotientMap R G (MonoidAlgebra.of R G (a.toMul * b.toMul)) - 1 = _
    rw [map_mul, map_mul]
    linear_combination hz

/-- Scalar extension of the additive root map. -/
def quotientMoment : MomentSpace R G →ₗ[R] SquareQuotient R G :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton R _ (quotientRoot R G).toIntLinearMap)

@[simp] theorem quotientMoment_tmul (r : R) (g : Additive G) :
    quotientMoment R G (r ⊗ₜ[ℤ] g) = r • (quotientRoot R G g) := rfl

/-- Reconstruction of a quotient class from its augmentation and first moment. -/
def linearInverse : TrivSqZeroExt R (MomentSpace R G) →ₗ[R] SquareQuotient R G :=
  (Algebra.ofId R (SquareQuotient R G)).toLinearMap.comp
    (TrivSqZeroExt.fstHom R R (MomentSpace R G)).toLinearMap +
    (quotientMoment R G).comp (TrivSqZeroExt.sndHom R (MomentSpace R G))

theorem linearInverse_jet (v : MonoidAlgebra R G) :
    linearInverse R G (jet R G v) = quotientMap R G v := by
  have h : (linearInverse R G).comp (jet R G).toLinearMap = (quotientMap R G).toLinearMap := by
    apply (MonoidAlgebra.basis G R).ext
    intro g
    change linearInverse R G (jet R G (MonoidAlgebra.of R G g)) =
      quotientMap R G (MonoidAlgebra.of R G g)
    rw [jet_of]
    simp [linearInverse, quotientRoot]
  exact LinearMap.congr_fun h v

/-- Augmentation and first moment are the complete obstruction to membership in `I²`. -/
theorem jet_ker_eq_square : RingHom.ker (jet R G).toRingHom = (augmentationIdeal R G)^2 := by
  apply le_antisymm
  · intro v hv
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotientMap R G v = 0
    rw [← linearInverse_jet R G v, show jet R G v = 0 from hv, map_zero]
  · exact square_le_jet_ker R G

/-- Every augmentation and scalar-extended group moment is realized. -/
theorem jet_surjective : Function.Surjective (jet R G) := by
  have hm : ∀ m : MomentSpace R G, ∃ v, jet R G v = TrivSqZeroExt.inr m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r g =>
      refine ⟨r • (MonoidAlgebra.of R G g.toMul - 1), ?_⟩
      rw [map_smul, map_sub, jet_of, map_one]
      apply TrivSqZeroExt.ext <;> simp [TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]; apply TrivSqZeroExt.ext <;> simp⟩
  intro z
  obtain ⟨v, hv⟩ := hm z.snd
  refine ⟨algebraMap R (MonoidAlgebra R G) z.fst + v, ?_⟩
  rw [map_add, AlgHom.commutes, hv]
  change TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd = z
  apply TrivSqZeroExt.ext <;> simp

/-- The first-order group algebra is the square-zero extension by the scalar-extended group. -/
def quotientEquiv : SquareQuotient R G ≃ₐ[R] TrivSqZeroExt R (MomentSpace R G) := by
  change (MonoidAlgebra R G ⧸ (augmentationIdeal R G)^2) ≃ₐ[R] _
  rw [← jet_ker_eq_square]
  exact Ideal.quotientKerAlgEquivOfSurjective (jet_surjective R G)

#print axioms jet_ker_eq_square
#print axioms quotientEquiv

end GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet
