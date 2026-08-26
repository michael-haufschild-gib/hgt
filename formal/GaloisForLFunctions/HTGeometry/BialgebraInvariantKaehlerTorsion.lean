import GaloisForLFunctions.HTGeometry.CoLieKaehler
import GaloisForLFunctions.HTGeometry.FiniteTypeSpecialization
import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing

/-!
# Torsion invariant differentials have zero co-Lie value

For a commutative bialgebra, right translation by a rational point is obtained by slicing the
right tensor factor of comultiplication.  An invariant Kähler differential is fixed by every such
translation.  Over an algebraically closed field, a nonzero torsion denominator survives at some
rational point.  Translating that denominator to the identity and using that the algebra action on
the co-Lie module is through the counit forces the co-Lie value of the differential to vanish.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A]

/-- Slice the right tensor factor of a commutative bialgebra against a rational point. -/
def bialgebraRightSlice (φ : A →ₐ[k] k) : (A ⊗[k] A) →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A)
    ((Algebra.ofId k A).comp φ) (fun _ _ => Commute.all _ _)

/-- Right translation by a rational point, on the coordinate bialgebra. -/
def bialgebraRightTranslate (φ : A →ₐ[k] k) : A →ₐ[k] A :=
  (bialgebraRightSlice φ).comp (Bialgebra.comulAlgHom k A)

/-- Slicing the left tensor inclusion is the identity. -/
theorem bialgebraRightSlice_comp_includeLeft (φ : A →ₐ[k] k) :
    (bialgebraRightSlice φ).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) =
      AlgHom.id k A := by
  ext a
  simp [bialgebraRightSlice]

/-- Slicing the right tensor inclusion is evaluation at the point, followed by constants. -/
theorem bialgebraRightSlice_comp_includeRight (φ : A →ₐ[k] k) :
    (bialgebraRightSlice φ).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) =
      (Algebra.ofId k A).comp φ := by
  ext a
  simp [bialgebraRightSlice]

/-- Pullback of Kähler differentials along the identity algebra map is the identity. -/
theorem algHomKaehlerMap_id (w : Ω[A⁄k]) :
    algHomKaehlerMap (AlgHom.id k A) w = w := by
  have hw : w ∈ Submodule.span A
      (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, rfl⟩
    rw [algHomKaehlerMap_D]
    rfl
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro a x _ hx
    rw [algHomKaehlerMap_smul, hx]
    rfl

/-- A map factoring through the base field kills relative Kähler differentials. -/
theorem algHomKaehlerMap_comp_algebraOfId_eq_zero
    (φ : A →ₐ[k] k) (w : Ω[A⁄k]) :
    algHomKaehlerMap ((Algebra.ofId k A).comp φ) w = 0 := by
  have hw : w ∈ Submodule.span A
      (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, rfl⟩
    rw [algHomKaehlerMap_D]
    simp
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [algHomKaehlerMap_smul, hx, smul_zero]

/-- The multiplication pullback law implies invariance under every rational right translation. -/
theorem algHomKaehlerMap_bialgebraRightTranslate_eq_of_comul
    (w : Ω[A⁄k])
    (hcomul :
      algHomKaehlerMap (Bialgebra.comulAlgHom k A) w =
        algHomKaehlerMap
            (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] A) w +
          algHomKaehlerMap
            (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A) w)
    (φ : A →ₐ[k] k) :
    algHomKaehlerMap (bialgebraRightTranslate φ) w = w := by
  rw [bialgebraRightTranslate, algHomKaehlerMap_comp, hcomul, map_add]
  rw [← algHomKaehlerMap_comp, ← algHomKaehlerMap_comp]
  rw [bialgebraRightSlice_comp_includeLeft,
    bialgebraRightSlice_comp_includeRight]
  rw [algHomKaehlerMap_id, algHomKaehlerMap_comp_algebraOfId_eq_zero,
    add_zero]

/-- Evaluating a right translate at the identity equals evaluation at the translating point. -/
theorem counit_bialgebraRightTranslate (φ : A →ₐ[k] k) (a : A) :
    Coalgebra.counit (R := k) (bialgebraRightTranslate φ a) = φ a := by
  let p : (k ⊗[k] A) →ₐ[k] k :=
    Algebra.TensorProduct.lift (AlgHom.id k k) φ
      (fun _ _ => Commute.all _ _)
  have hslice (t : A ⊗[k] A) :
      Coalgebra.counit (R := k) (bialgebraRightSlice φ t) =
        p (TensorProduct.map
          (Coalgebra.counit (R := k))
          (LinearMap.id (R := k) (M := A)) t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | tmul x y => simp [bialgebraRightSlice, p, mul_comm]
  have h := DFunLike.congr_fun
    (Coalgebra.rTensor_counit_comp_comul (R := k) (A := A)) a
  change TensorProduct.map
      (Coalgebra.counit (R := k))
      (LinearMap.id (R := k) (M := A))
      (Coalgebra.comul (R := k) a) =
    (1 : k) ⊗ₜ[k] a at h
  rw [bialgebraRightTranslate, AlgHom.comp_apply]
  rw [hslice]
  change p (TensorProduct.map
      (Coalgebra.counit (R := k))
      (LinearMap.id (R := k) (M := A))
      (Coalgebra.comul (R := k) a)) = φ a
  rw [h]
  simp [p]

/-- A torsion invariant Kähler differential on a finite-type domain has zero co-Lie value. -/
theorem kaehlerToCoLie_eq_zero_of_torsion_of_rightTranslate_invariant
    [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A]
    (w : Ω[A⁄k])
    (htranslate : ∀ φ : A →ₐ[k] k,
      algHomKaehlerMap (bialgebraRightTranslate φ) w = w)
    (s : A) (hs : s ≠ 0) (htors : s • w = 0) :
    AffineGroupScheme.kaehlerToCoLie w = 0 := by
  obtain ⟨φ, hφ⟩ :=
    GaloisForLFunctions.exists_algHom_ne_zero_of_finiteType_domain k A s hs
  have htranslated : bialgebraRightTranslate φ s • w = 0 := by
    rw [← htranslate φ, ← algHomKaehlerMap_smul, htors, map_zero]
  have hcolie := congrArg AffineGroupScheme.kaehlerToCoLie htranslated
  rw [map_smul, AffineGroupScheme.smul_coLie,
    counit_bialgebraRightTranslate, map_zero] at hcolie
  exact (smul_eq_zero.mp hcolie).resolve_left hφ

/-- Right translation is natural under a morphism of commutative bialgebras. -/
theorem bialgebraRightTranslate_naturality
    {B : Type*} [CommRing B] [Bialgebra k B]
    (f : A →ₐc[k] B) (φ : B →ₐ[k] k) :
    (bialgebraRightTranslate φ).comp f.toAlgHom =
      f.toAlgHom.comp (bialgebraRightTranslate (φ.comp f.toAlgHom)) := by
  ext a
  have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) a
  change TensorProduct.map f.toLinearMap f.toLinearMap
      (Coalgebra.comul (R := k) a) =
    Coalgebra.comul (R := k) (f a) at hmap
  rw [AlgHom.comp_apply, AlgHom.comp_apply, bialgebraRightTranslate,
    bialgebraRightTranslate, AlgHom.comp_apply, AlgHom.comp_apply]
  change bialgebraRightSlice φ (Coalgebra.comul (R := k) (f a)) =
    f (bialgebraRightSlice (φ.comp f.toAlgHom)
      (Coalgebra.comul (R := k) a))
  rw [← hmap]
  have hslice (t : A ⊗[k] A) :
      bialgebraRightSlice φ
          (TensorProduct.map f.toLinearMap f.toLinearMap t) =
        f (bialgebraRightSlice (φ.comp f.toAlgHom) t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | tmul x y =>
        simp only [TensorProduct.map_tmul, bialgebraRightSlice,
          Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq,
          AlgHom.comp_apply]
        rw [map_mul]
        change f x * algebraMap k B (φ (f y)) =
          f x * f (algebraMap k A (φ (f y)))
        apply congrArg (fun z : B => f x * z)
        exact (f.toAlgHom.commutes (φ (f y))).symm
  exact hslice (Coalgebra.comul (R := k) a)

/-- Kähler pullback and the induced co-Lie map commute for a bialgebra morphism. -/
theorem kaehlerToCoLie_algHomKaehlerMap
    {B : Type*} [CommRing B] [Bialgebra k B]
    (f : A →ₐc[k] B) (w : Ω[A⁄k]) :
    AffineGroupScheme.kaehlerToCoLie
        (algHomKaehlerMap f.toAlgHom w) =
      AffineGroupScheme.coLieMap f
        (AffineGroupScheme.kaehlerToCoLie w) := by
  have hw : w ∈ Submodule.span A
      (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, rfl⟩
    rw [algHomKaehlerMap_D, AffineGroupScheme.kaehlerToCoLie_D,
      AffineGroupScheme.kaehlerToCoLie_D, AffineGroupScheme.coLieMap_d]
    rfl
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro a x _ hx
    rw [algHomKaehlerMap_smul, map_smul,
      AffineGroupScheme.smul_coLie]
    change Coalgebra.counit (R := k) (f a) •
        AffineGroupScheme.kaehlerToCoLie (algHomKaehlerMap f.toAlgHom x) =
      AffineGroupScheme.coLieMap f
        (AffineGroupScheme.kaehlerToCoLie (a • x))
    rw [show AffineGroupScheme.kaehlerToCoLie (a • x) =
        a • AffineGroupScheme.kaehlerToCoLie x by rw [map_smul],
      AffineGroupScheme.smul_coLie, map_smul,
      AffineGroupScheme.counit_bialgHom, hx]

end

end GaloisForLFunctions.HTGeometry
