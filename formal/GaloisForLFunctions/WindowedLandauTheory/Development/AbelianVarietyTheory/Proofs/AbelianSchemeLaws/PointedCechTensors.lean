import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechProductTensors

/-! Pulling a tensor of sections to a pointed slice evaluates its second factor. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

theorem appLE_comp_apply {A B C : Scheme.{0}} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (e : u ≫ v = w) {U : C.Opens} {V : B.Opens} {W : A.Opens}
    (hu : V ≤ v ⁻¹ᵁ U) (hv : W ≤ u ⁻¹ᵁ V) (hw : W ≤ w ⁻¹ᵁ U) (x : Γ(C, U)) :
    u.appLE V W hv (v.appLE U V hu x) = w.appLE U W hw x := by
  subst w
  exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE u v U V W hu hv) x

theorem id_appLE_self {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) :
    (𝟙 X : X ⟶ X).appLE U U (by exact le_rfl) a = a := by
  have e : (𝟙 X : X ⟶ X).appLE U U (by exact le_rfl) =
      X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact Category.id_comp _
  exact (ConcreteCategory.congr_hom e a).trans (resG_self le_rfl a)

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
  {p : Z ⟶ X} {q : Z ⟶ Y} {y : Spec (CommRingCat.of K) ⟶ Y}
  (hy : y ≫ g = 𝟙 _) {V : Y.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V)

/-- Evaluation at the rational point on an affine chart through it. -/
def evalAt : SectionRing g V →ₐ[K] K where
  toRingHom := (Scheme.ΓSpecIso _).hom.hom.comp (y.appLE V ⊤ hV).hom
  commutes' c := by
    let S := Spec (CommRingCat.of K)
    let e := Scheme.ΓSpecIso (CommRingCat.of K)
    change e.hom (y.appLE V ⊤ hV (g.appLE ⊤ V le_top (e.inv c))) = c
    rw [appLE_comp_apply hy le_top hV (show ⊤ ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ ⊤ from le_rfl)]
    rw [id_appLE_self]
    exact ConcreteCategory.congr_hom e.inv_hom_id c

theorem appLE_along_point {M : X.Opens} (b : SectionRing g V) :
    letI := sectionAlgebra f M
    (f ≫ y).appLE V M (le_top.trans (f.preimage_mono hV)) b =
      algebraMap K Γ(X, M) (evalAt hy hV b) := by
  letI := sectionAlgebra f M
  let c := y.appLE V ⊤ hV b
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  have h := appLE_comp_apply (rfl : f ≫ y = f ≫ y) hV
    (le_top : M ≤ f ⁻¹ᵁ ⊤) (le_top.trans (f.preimage_mono hV)) b
  change _ = f.appLE ⊤ M le_top (e.inv (e.hom c))
  rw [← h]
  exact congrArg (fun z => f.appLE ⊤ M le_top z)
    (ConcreteCategory.congr_hom e.hom_inv_id c).symm

variable (H : IsPullback p q f g) {ι : Type} (U : ι → X.Opens)
  {a : X ⟶ Z} (ha : a ≫ p = 𝟙 X) (ha' : a ≫ q = f ≫ y)

include ha ha' in
theorem tensorComponent_on_slice (i : ι) {W : Z.Opens} (hU : W ≤ p ⁻¹ᵁ U i)
    (hW : W ≤ q ⁻¹ᵁ V) (hi : U i ≤ a ⁻¹ᵁ W)
    (x : chartSections (f := f) U ⊗[K] SectionRing g V) :
    a.appLE W (U i) hi (tensorComponent H U V i hU hW x) =
      TensorProduct.rid K (chartSections (f := f) U) ((evalAt hy hV).toLinearMap.lTensor _ x) i := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (a.appLE W (U i) hi).hom.map_zero
  | tmul x y' =>
    simp only [LinearMap.lTensor_tmul, tensorComponent_tmul, TensorProduct.rid_tmul,
      Pi.smul_apply, Algebra.smul_def, AlgHom.toLinearMap_apply]
    have h₁ := (appLE_comp_apply ha hU hi
      (show U i ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U i from le_rfl) (x i)).trans (id_appLE_self _ _)
    have h₂ := (appLE_comp_apply ha' hW hi (le_top.trans (f.preimage_mono hV)) y').trans
      (appLE_along_point (f := f) (M := U i) hy hV y')
    exact ((a.appLE W (U i) hi).hom.map_mul _ _).trans
      ((congrArg₂ (· * ·) h₁ h₂).trans (mul_comm _ _))
  | add x y hx hy' =>
    simp only [map_add, Pi.add_apply]
    exact ((a.appLE W (U i) hi).hom.map_add _ _).trans (congrArg₂ (· + ·) hx hy')

end GlobalTheory.CechOne
