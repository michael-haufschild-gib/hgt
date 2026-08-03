import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Mathlib.Analysis.Complex.Basic

/-!
# Crossed products of invariant smooth coefficient algebras

This file supplies the missing algebraic inclusion needed to turn coefficient smoothness into an
honest crossed-product statement.  An invariant complex subalgebra `S ⊆ A` inherits the monoid
action.  Its skew monoid algebra maps injectively into the ambient skew monoid algebra, and an
ambient degree-zero coefficient belongs to the image exactly when that coefficient belongs to `S`.

The result applies in particular to a `ℤ/2`-crossed product.  It prevents a false weakening in
which membership of a corona coefficient is discussed without constructing its crossed-product
inclusion.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable (G A : Type*) [Monoid G] [Semiring A] [Algebra ℂ A]
  [MulSemiringAction G A] [SMulCommClass G ℂ A]

/-- A complex coefficient subalgebra preserved by the monoid action used in a skew crossed
product. -/
structure InvariantSubalgebra where
  S : Subalgebra ℂ A
  smul_mem : ∀ (g : G) {a : A}, a ∈ S → g • a ∈ S

variable {G A}

/-- Restricted monoid action on an invariant coefficient subalgebra. -/
instance (D : InvariantSubalgebra G A) : SMul G D.S where
  smul g a := ⟨g • (a : A), D.smul_mem g a.property⟩

omit [SMulCommClass G ℂ A] in
@[simp] theorem InvariantSubalgebra.coe_smul
    (D : InvariantSubalgebra G A) (g : G) (a : D.S) :
    ((g • a : D.S) : A) = g • (a : A) := rfl

/-- The restricted action is by semiring endomorphisms. -/
instance (D : InvariantSubalgebra G A) : MulSemiringAction G D.S where
  smul_zero g := by ext; simp
  smul_add g a b := by ext; simp
  smul_one g := by ext; simp
  smul_mul g a b := by ext; simp
  one_smul a := by ext; simp
  mul_smul g h a := by
    ext
    exact mul_smul g h (a : A)

/-- The restricted action continues to commute with complex scalars. -/
instance (D : InvariantSubalgebra G A) : SMulCommClass G ℂ D.S where
  smul_comm g c a := by ext; exact smul_comm g c (a : A)

/-- Algebraic smooth crossed product associated with an invariant smooth coefficient algebra. -/
abbrev InvariantSubalgebra.smoothCrossedProduct (D : InvariantSubalgebra G A) :=
  SkewMonoidAlgebra D.S G

/-- Ambient algebraic crossed product. -/
abbrev ambientCrossedProduct := SkewMonoidAlgebra A G

/-- Coefficient inclusion into the identity component of the ambient crossed product. -/
private def InvariantSubalgebra.coefficientAlgHom (D : InvariantSubalgebra G A) :
    D.S →ₐ[ℂ] ambientCrossedProduct (G := G) (A := A) where
  __ := SkewMonoidAlgebra.singleOneRingHom.comp D.S.val
  commutes' c := by
    ext g
    simp [SkewMonoidAlgebra.singleOneRingHom]

/-- Covariance relation for the restricted coefficient inclusion. -/
private theorem InvariantSubalgebra.coefficient_covariant
    (D : InvariantSubalgebra G A) {x : D.S} (g : G) :
    D.coefficientAlgHom (g • x) * SkewMonoidAlgebra.of A G g =
      SkewMonoidAlgebra.of A G g * D.coefficientAlgHom x := by
  simp [InvariantSubalgebra.coefficientAlgHom, SkewMonoidAlgebra.of_apply,
    SkewMonoidAlgebra.singleOneRingHom, SkewMonoidAlgebra.single_mul_single]

/-- Canonical algebra homomorphism from the smooth crossed product to the ambient crossed
product. -/
noncomputable def InvariantSubalgebra.crossedProductInclusion
    (D : InvariantSubalgebra G A) :
    D.smoothCrossedProduct →ₐ[ℂ] ambientCrossedProduct (G := G) (A := A) :=
  SkewMonoidAlgebra.liftNCAlgHom D.coefficientAlgHom
    (SkewMonoidAlgebra.of A G)
    (fun {x} y => D.coefficient_covariant (x := x) y)

@[simp] theorem InvariantSubalgebra.crossedProductInclusion_single
    (D : InvariantSubalgebra G A) (g : G) (a : D.S) :
    D.crossedProductInclusion (SkewMonoidAlgebra.single g a) =
      SkewMonoidAlgebra.single g (a : A) := by
  calc
    D.crossedProductInclusion (SkewMonoidAlgebra.single g a) =
        D.coefficientAlgHom a * SkewMonoidAlgebra.of A G g := by
      exact SkewMonoidAlgebra.liftNC_single _ _ _ _
    _ = SkewMonoidAlgebra.single g (a : A) := by
      simp [InvariantSubalgebra.coefficientAlgHom, SkewMonoidAlgebra.of_apply,
        SkewMonoidAlgebra.singleOneRingHom]

@[simp] theorem InvariantSubalgebra.crossedProductInclusion_coeff
    (D : InvariantSubalgebra G A) (F : D.smoothCrossedProduct) (g : G) :
    (D.crossedProductInclusion F).coeff g = (F.coeff g : A) := by
  classical
  induction F using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add F H hF hH => simp [hF, hH]
  | single h a =>
      rw [D.crossedProductInclusion_single]
      change (Finsupp.single h (a : A)) g = ((Finsupp.single h a) g : A)
      by_cases hgh : g = h
      · subst g
        simp
      · simp [hgh]

/-- Smooth crossed-product inclusion is injective. -/
theorem InvariantSubalgebra.crossedProductInclusion_injective
    (D : InvariantSubalgebra G A) :
    Function.Injective D.crossedProductInclusion := by
  intro F H h
  apply SkewMonoidAlgebra.coeff_injective
  ext g
  simpa only [D.crossedProductInclusion_coeff] using
    congrArg (fun K => K.coeff g) h

/-- Coefficientwise topology on an algebraic crossed product, induced from the product topology on
all coefficient functions. -/
@[reducible] noncomputable def crossedProductCoefficientwiseTopology
    [TopologicalSpace A] :
    TopologicalSpace (ambientCrossedProduct (G := G) (A := A)) :=
  TopologicalSpace.induced (fun F g => F.coeff g) inferInstance

/-- For a finite acting monoid, a dense invariant coefficient algebra has dense smooth crossed
product image in the coefficientwise topology.  Every finite list of coefficient neighborhoods is
met simultaneously. -/
theorem InvariantSubalgebra.crossedProductInclusion_denseRange_coefficientwise
    [Finite G] [TopologicalSpace A]
    (D : InvariantSubalgebra G A) (hDense : Dense (D.S : Set A)) :
    letI : TopologicalSpace (ambientCrossedProduct (G := G) (A := A)) :=
      crossedProductCoefficientwiseTopology
    DenseRange D.crossedProductInclusion := by
  letI : TopologicalSpace (ambientCrossedProduct (G := G) (A := A)) :=
    crossedProductCoefficientwiseTopology
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro F
  rw [mem_closure_iff]
  intro o ho hFo
  rw [isOpen_induced_iff] at ho
  rcases ho with ⟨t, ht, hto⟩
  have hFt : (fun g => F.coeff g) ∈ t := by
    have : F ∈ (fun K g => K.coeff g) ⁻¹' t := by simpa [hto] using hFo
    exact this
  have hPiDense : Dense (Set.univ.pi fun _ : G => (D.S : Set A)) :=
    dense_pi Set.univ fun _ _ => hDense
  rcases hPiDense.exists_mem_open ht ⟨_, hFt⟩ with ⟨q, hqS, hqt⟩
  let qS : G → D.S := fun g => ⟨q g, hqS g (Set.mem_univ g)⟩
  let X : D.smoothCrossedProduct :=
    SkewMonoidAlgebra.coeffAddEquiv.symm (Finsupp.equivFunOnFinite.symm qS)
  have hcoeff : (fun g => (D.crossedProductInclusion X).coeff g) = q := by
    funext g
    rw [D.crossedProductInclusion_coeff]
    change ((Finsupp.equivFunOnFinite.symm qS) g : D.S) = q g
    simp [qS]
  refine ⟨D.crossedProductInclusion X, ?_, ⟨X, rfl⟩⟩
  rw [← hto]
  change (fun g => (D.crossedProductInclusion X).coeff g) ∈ t
  rw [hcoeff]
  exact hqt

/-- Exact degree-zero range test: a coefficient lifts to the smooth crossed product if and only if
it is smooth in the invariant coefficient algebra. -/
theorem InvariantSubalgebra.degreeZero_mem_crossedProductRange_iff
    (D : InvariantSubalgebra G A) (a : A) :
    SkewMonoidAlgebra.single (1 : G) a ∈ Set.range D.crossedProductInclusion ↔
      a ∈ D.S := by
  constructor
  · rintro ⟨F, hF⟩
    have hc := congrArg (fun K => K.coeff (1 : G)) hF
    have hc' : ((F.coeff 1 : D.S) : A) = a := by
      simpa [SkewMonoidAlgebra.coeff_single] using hc
    rw [← hc']
    exact (F.coeff 1).property
  · intro ha
    refine ⟨SkewMonoidAlgebra.single 1 ⟨a, ha⟩, ?_⟩
    exact D.crossedProductInclusion_single 1 ⟨a, ha⟩

end GaloisForLFunctions.RHTower
