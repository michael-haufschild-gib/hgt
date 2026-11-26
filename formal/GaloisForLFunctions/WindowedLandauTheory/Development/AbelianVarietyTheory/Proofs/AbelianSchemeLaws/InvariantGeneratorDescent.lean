import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionInvariantFunctions
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafSectionGerms

/-! Descent of invariant functions on charts descends a generator of a formal product
of line bundles. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatDescent

private theorem descend_generator {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I K : Type} [Fintype K] (f : K → (Y ⟶ X)) (d : K → ℤ) (q : Z ⟶ Y)
    (τ : I → (Z ⟶ Z)) (hτ : ∀ i, τ i ≫ q = q)
    (hd : ∀ (U : Y.Opens) (a : Γ(Z, q ⁻¹ᵁ U)),
      (∀ i (e : q ⁻¹ᵁ U ≤ τ i ⁻¹ᵁ (q ⁻¹ᵁ U)), (τ i).appLE _ _ e a = a) →
      ∃! b : Γ(Y, U), q.app U b = a)
    {u : (LB.LinComb L (fun k => q ≫ f k) d).Gen} (hu : u.IsGen)
    (hinv : ∀ i z J, Good L z J → val u (τ i) z J = val u (𝟙 Z) z J) :
    ∃ v : (LB.LinComb L f d).Gen, v.IsGen := by
  have hinj (U : Y.Opens) : Function.Injective (q.app U) := by
    intro b c h
    refine (hd U (q.app U b) fun i e => fn_ext fun z hz => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Z) z e hz _).trans ((gs_pull (𝟙 Z) (τ i) z (q ⁻¹ᵁ U) (e hz) _).trans
      ((gs_pull (𝟙 Z ≫ τ i) q z U (e hz) _).trans (Eq.trans ?_ (gs_pull (𝟙 Z) q z U hz _).symm)))
    rw [Category.assoc, hτ]
  have hunit (U : Y.Opens) (a : Γ(Z, q ⁻¹ᵁ U)ˣ)
      (ha : ∀ i (e : q ⁻¹ᵁ U ≤ τ i ⁻¹ᵁ (q ⁻¹ᵁ U)), res e (pullU (τ i) _ a) = a) :
      ∃ b : Γ(Y, U)ˣ, pullU q U b = a := by
    obtain ⟨b, hb, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨c, hc, -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (τ i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have hbc : b * c = 1 := hinj U (by rw [map_mul, map_one, hb, hc]; exact a.mul_inv)
    exact ⟨⟨b, c, hbc, (mul_comm _ _).trans hbc⟩, Units.ext hb⟩
  let M := LB.LinComb L f d
  let M' := LB.LinComb L (fun k => q ≫ f k) d
  have le (j : K → L.ι) : q ⁻¹ᵁ M.U j ≤ M'.U j :=
    fun z hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
  have hchart (j : K → L.ι) : ∃ b : Γ(Y, M.U j)ˣ,
      pullU q (M.U j) b = res (le j) (u.s j) := by
    refine hunit (M.U j) _ fun i e => unit_ext fun z hz => ?_
    choose J hJ using fun g : Z ⟶ X => exists_chart hL (g z)
    have hGood : Good L z J := hJ
    refine (gm_res (𝟙 Z) z e hz _).trans ((gm_pull (𝟙 Z) (τ i) z (q ⁻¹ᵁ M.U j) (e hz) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (τ i) z (le j) (e hz) _).trans (Eq.trans ?_ (gm_res (𝟙 Z) z (le j) hz _).symm)
    refine (gen_trans hu (τ i) z (le j (e hz)) (hGood.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Z) z (le j hz) (hGood.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i z J hGood)
    have he (k : K) : τ i ≫ q ≫ f k = 𝟙 Z ≫ q ≫ f k :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f k) (hτ i)).trans (Category.id_comp _).symm)
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun g : Z ⟶ X => gm g z (L.U (j k) ⊓ L.U (J g)) (L.g (j k) (J g)) ^ d k) (he k)
  choose b hb using hchart
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU q (M.U i ⊓ M.U j) _ = pullU q (M.U i ⊓ M.U j) _ from unit_ext fun z hz => ?_)))⟩
  have hv (k : K → L.ι) (hk : z ∈ q ⁻¹ᵁ M.U k) :
      gm (𝟙 Z ≫ q) z (M.U k) (b k) = gm (𝟙 Z) z (M'.U k) (u.s k) :=
    (gm_pull (𝟙 Z) q z _ hk _).symm.trans
      ((congrArg (gm (𝟙 Z) z _) (hb k)).trans (gm_res (𝟙 Z) z (le k) hk _))
  refine (gm_pull (𝟙 Z) q z _ hz _).trans (Eq.trans ?_ (gm_pull (𝟙 Z) q z _ hz _).symm)
  refine ((gm_res _ z _ hz _).trans (hv i hz.1)).trans
    ((gen_trans hu (𝟙 Z) z (le i hz.1) (le j hz.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L f d (𝟙 Z ≫ q) z i j hz.1 hz.2).trans ?_)
    ((gm_res _ z _ hz _).trans (hv j hz.2)))
  simp only [trF, Category.assoc]

attribute [local instance] Over.cartesianMonoidalCategory

/-- A generator of the pullback of a formal product descends if its values are
invariant under every rational kernel translation. -/
theorem exists_generator_of_kernel_translation_invariant {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] [IsReduced A.left] [LocallyOfFiniteType A.hom]
    (q : A ⟶ A) [IsMonHom q] [Etale q.left] [Surjective q.left] [QuasiCompact q.left]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    (f : I → (A.left ⟶ X)) (d : I → ℤ)
    {u : (LB.LinComb L (fun i => q.left ≫ f i) d).Gen} (hu : u.IsGen)
    (hinv : ∀ (y : 𝟙_ (Over (Spec (.of K))) ⟶ A), y ≫ q = 1 →
      ∀ z J, Good L z J → val u ((toUnit A ≫ y) * 𝟙 A).left z J = val u (𝟙 A.left) z J) :
    ∃ v : (LB.LinComb L f d).Gen, v.IsGen := by
  let D := {y : 𝟙_ (Over (Spec (.of K))) ⟶ A // y ≫ q = 1}
  let τ (y : D) : A ⟶ A := (toUnit A ≫ y.1) * 𝟙 A
  have hτ (y : D) : τ y ≫ q = q := by
    change ((toUnit A ≫ y.1) * 𝟙 A) ≫ q = q
    rw [MonObj.mul_comp, Category.assoc, y.2, MonObj.comp_one, _root_.one_mul, Category.id_comp]
  exact descend_generator hL f d q.left (fun y : D => (τ y).left)
    (fun y => congrArg Over.Hom.left (hτ y))
    (fun U a ha => existsUnique_descend_of_kernel_translation_invariant q U a
      fun y hy => ha ⟨y, hy⟩)
    hu (fun y => hinv y.1 y.2)

end GlobalTheory.FlatDescent
