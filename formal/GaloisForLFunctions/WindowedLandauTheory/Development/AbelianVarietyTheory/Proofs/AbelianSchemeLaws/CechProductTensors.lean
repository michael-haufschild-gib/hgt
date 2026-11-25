import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProductSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Tensor coordinates for restrictions and differences on an affine rectangle cover. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TensorProduct
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

/-- Linear functionals annihilating the range detect membership in that range after
tensoring over a field. -/
theorem mem_range_rTensor_of_forall_dual {K A B C : Type} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (δ : A →ₗ[K] B) (z : B ⊗[K] C)
    (h : ∀ l : B →ₗ[K] K, l ∘ₗ δ = 0 → TensorProduct.lid K C (l.rTensor C z) = 0) :
    ∃ y, δ.rTensor C y = z := by
  classical
  have hex := rTensor_exact C (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)
  refine (hex z).mp ?_
  let b := Module.Basis.ofVectorSpace K (B ⧸ LinearMap.range δ)
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, Finsupp.zero_apply, ← LinearMap.rTensor_comp_apply]
  apply h
  ext x
  simp [(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self δ x)]

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
  {p : Z ⟶ X} {q : Z ⟶ Y} (H : IsPullback p q f g)
  {ι : Type} (U : ι → X.Opens) (V : Y.Opens)

abbrev chartSections := ∀ i, SectionRing f (U i)

/-- Evaluate a tensor of chart functions on an open of its affine rectangle. -/
def tensorComponent (i : ι) {W : Z.Opens} (hU : W ≤ p ⁻¹ᵁ U i) (hV : W ≤ q ⁻¹ᵁ V) :
    chartSections (f := f) U ⊗[K] SectionRing g V →ₗ[K] SectionRing (p ≫ f) W :=
  (Algebra.TensorProduct.productMap
    (sectionPullbackLE (p := p) (f := f) (q := p) (g := f) rfl hU)
    (sectionPullbackLE H.w hV)).toLinearMap ∘ₗ
      (LinearMap.proj i).rTensor (SectionRing g V)

theorem tensorComponent_tmul (i : ι) {W : Z.Opens} (hU : W ≤ p ⁻¹ᵁ U i) (hV : W ≤ q ⁻¹ᵁ V)
    (x : chartSections (f := f) U) (y : SectionRing g V) :
    tensorComponent H U V i hU hV (x ⊗ₜ[K] y) = p.appLE _ _ hU (x i) * q.appLE _ _ hV y := by
  simp only [tensorComponent, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.proj_apply]
  rfl

private theorem tensorComponent_on_rectangle [Fintype ι] [DecidableEq ι] (i : ι) (hU : IsAffineOpen (U i))
    (hV : IsAffineOpen V) (x : chartSections (f := f) U ⊗[K] SectionRing g V) :
    tensorComponent H U V i inf_le_left inf_le_right x =
      productSectionsEquiv H (U i) V hU hV
        (TensorProduct.piLeft K (SectionRing g V) (fun j => SectionRing f (U j)) x i) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero (tensorComponent H U V i _ _),
      map_zero (TensorProduct.piLeft K (SectionRing g V) (fun j => SectionRing f (U j)))]
    exact (map_zero (productSectionsEquiv H (U i) V hU hV)).symm
  | tmul x y =>
    rw [tensorComponent_tmul]
    exact (productSectionsEquiv_tmul H (U i) V hU hV (x i) y).symm
  | add a b ha hb =>
    rw [map_add (tensorComponent H U V i _ _),
      map_add (TensorProduct.piLeft K (SectionRing g V) (fun j => SectionRing f (U j)))]
    change _ = productSectionsEquiv H (U i) V hU hV (_ + _)
    rw [map_add, ← ha, ← hb]

theorem exists_tensor_of_sections [Finite ι] (hU : ∀ i, IsAffineOpen (U i)) (hV : IsAffineOpen V)
    (c : ∀ i, Γ(Z, p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ V)) :
    ∃ x, ∀ i, tensorComponent H U V i inf_le_left inf_le_right x = c i := by
  classical
  cases nonempty_fintype ι
  let e := TensorProduct.piLeft K (SectionRing g V) (fun j => SectionRing f (U j))
  let y : ∀ i, SectionRing f (U i) ⊗[K] SectionRing g V :=
    fun i => (productSectionsEquiv H (U i) V (hU i) hV).symm (c i)
  refine ⟨e.symm y, fun i => ?_⟩
  rw [tensorComponent_on_rectangle H U V i (hU i) hV, e.apply_symm_apply]
  exact (productSectionsEquiv H (U i) V (hU i) hV).apply_symm_apply (c i)

theorem tensor_eq_of_sections_eq [Finite ι] (hU : ∀ i, IsAffineOpen (U i)) (hV : IsAffineOpen V)
    {x y : chartSections (f := f) U ⊗[K] SectionRing g V}
    (h : ∀ i, tensorComponent H U V i inf_le_left inf_le_right x =
      tensorComponent H U V i inf_le_left inf_le_right y) : x = y := by
  classical
  cases nonempty_fintype ι
  apply (TensorProduct.piLeft K (SectionRing g V) (fun j => SectionRing f (U j))).injective
  funext i
  apply (productSectionsEquiv H (U i) V (hU i) hV).injective
  exact ((tensorComponent_on_rectangle H U V i (hU i) hV x).symm.trans (h i)).trans
    (tensorComponent_on_rectangle H U V i (hU i) hV y)

theorem res_tensorComponent (i : ι) {W W' : Z.Opens}
    (hi : W ≤ p ⁻¹ᵁ U i) (hv : W ≤ q ⁻¹ᵁ V) (h : W' ≤ W)
    (x : chartSections (f := f) U ⊗[K] SectionRing g V) :
    resG Z h (tensorComponent H U V i hi hv x) =
      tensorComponent H U V i (h.trans hi) (h.trans hv) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero (tensorComponent H U V i hi hv),
      map_zero (tensorComponent H U V i (h.trans hi) (h.trans hv))]
    exact (resG Z h).map_zero
  | tmul a b => simp only [tensorComponent_tmul, map_mul, resG_appLE]
  | add a b ha hb =>
    let A := tensorComponent H U V i hi hv
    let B := tensorComponent H U V i (h.trans hi) (h.trans hv)
    exact (congrArg (resG Z h) (A.map_add a b)).trans
      (((resG Z h).map_add (A a) (A b)).trans
        ((congrArg₂ (· + ·) ha hb).trans (B.map_add a b).symm))

theorem tensorComponent_restrict_right {V' : Y.Opens} (h : V' ≤ V) (i : ι) {W : Z.Opens}
    (hi : W ≤ p ⁻¹ᵁ U i) (hv : W ≤ q ⁻¹ᵁ V')
    (x : chartSections (f := f) U ⊗[K] SectionRing g V) :
    tensorComponent H U V' i hi hv ((sectionRes g (homOfLE h)).toLinearMap.lTensor _ x) =
      tensorComponent H U V i hi (hv.trans (q.preimage_mono h)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, tensorComponent_tmul]
    exact congrArg (p.appLE _ _ hi (a i) * ·) (appLE_resG hv h b)
  | add a b ha hb => simp only [map_add, ha, hb]

abbrev overlap (i : ι × ι) := U i.1 ⊓ U i.2

/-- The difference of chart functions on each ordered overlap. -/
def chartDifference :
    chartSections (f := f) U →ₗ[K] chartSections (f := f) (overlap U) :=
  LinearMap.pi fun i =>
    (sectionRes f (homOfLE (inf_le_left : overlap U i ≤ U i.1))).toLinearMap ∘ₗ LinearMap.proj i.1 -
      (sectionRes f (homOfLE (inf_le_right : overlap U i ≤ U i.2))).toLinearMap ∘ₗ LinearMap.proj i.2

theorem tensorComponent_difference (i : ι × ι) {W : Z.Opens}
    (hi : W ≤ p ⁻¹ᵁ overlap U i) (hv : W ≤ q ⁻¹ᵁ V)
    (x : chartSections (f := f) U ⊗[K] SectionRing g V) :
    tensorComponent H (overlap U) V i hi hv ((chartDifference (f := f) U).rTensor _ x) =
      tensorComponent H U V i.1 (hi.trans (p.preimage_mono inf_le_left)) hv x -
        tensorComponent H U V i.2 (hi.trans (p.preimage_mono inf_le_right)) hv x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, tensorComponent_tmul, chartDifference, LinearMap.pi_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    let F : Γ(X, overlap U i) →+* Γ(Z, W) := (p.appLE _ _ hi).hom
    let y : Γ(Z, W) := q.appLE _ _ hv b
    let d₁ : Γ(X, overlap U i) := resG X inf_le_left (a i.1)
    let d₂ : Γ(X, overlap U i) := resG X inf_le_right (a i.2)
    change F (d₁ - d₂) * y = _
    refine (congrArg (fun z : Γ(Z, W) => z * y) (F.map_sub d₁ d₂)).trans
      ((sub_mul (F d₁) (F d₂) y).trans ?_)
    exact congrArg₂ (· - ·) (congrArg (fun x : Γ(Z, W) => x * y) (appLE_resG hi inf_le_left (a i.1)))
      (congrArg (fun x : Γ(Z, W) => x * y) (appLE_resG hi inf_le_right (a i.2)))
  | add a b ha hb => simp only [map_add, ha, hb, sub_add_sub_comm]

end GlobalTheory.CechOne
