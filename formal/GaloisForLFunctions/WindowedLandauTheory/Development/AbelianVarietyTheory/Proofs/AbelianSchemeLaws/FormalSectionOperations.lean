import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionValues

/-! Pullbacks and products of sections in formal presentations. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

/-- Pull back a section and each factor in its presentation. -/
def pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε) :=
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))) =
            gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
        (gs_res _ y _ hj _).trans (gs_pull _ h y _ (l j hj) _)
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.assoc] }

theorem sval_pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullSec s h) r z J = sval s (r ≫ h) z J := by
  have hm1 := hJ.mem (fun k => h ≫ φ k) r
  have hm2 := hJ.mem φ (r ≫ h)
  simp only [Category.assoc] at hm2
  unfold sval
  exact (gs_res r z _ hm1 _).trans (gs_pull r h z _ hm2 _)

/-- Multiply sections of two formally presented bundles. -/
def mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) :
    LB.Sec (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) :=
  have l₁ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
      (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K' → L.ι, y ∈ LB.wchart L (Sum.elim φ φ') j →
          gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
            (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))) =
          gs (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            gs (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t.f (j ∘ Sum.inr)) := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y) y (l₁ j hy.1) (l₁ j' hy.2), sec_trans t (𝟙 Y) y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Sum.elim_inl, Sum.elim_inr]
      rfl }

theorem sval_mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (mulSec s t) r z J = sval s r z J * sval t r z J := by

  have hm := hJ.mem (Sum.elim φ φ') r
  unfold sval
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

/-- A global generator gives a section with the same chart coefficients. -/
def genSec {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩

theorem sval_genSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval (genSec t ht) r z J = (val t r z J).val := by
  simp only [sval, val, genSec]
  exact gs_unit r z _ (hJ.mem φ r) _

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
