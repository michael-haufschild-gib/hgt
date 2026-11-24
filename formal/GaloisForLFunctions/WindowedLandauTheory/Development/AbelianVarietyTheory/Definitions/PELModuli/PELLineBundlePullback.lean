import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundles

/-! The chart cocycle is preserved by integral products of line-bundle pullbacks. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.Semi

universe u

variable {X Y : Scheme.{u}}

@[simp] theorem res_refl {U : X.Opens} (a : Γ(X, U)ˣ) :
    res (le_rfl : U ≤ U) a = a := by
  apply Units.ext
  have e : (homOfLE (le_rfl : U ≤ U)).op = 𝟙 _ := Subsingleton.elim _ _
  simp only [res, Units.coe_map, e, Functor.map_id, CommRingCat.id_apply]

/-- Pull back a unit-valued section to a smaller open in the source. -/
def pullLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ :=
  Units.map (f.appLE U V h).hom

theorem res_pullLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens}
    (hv : V ≤ f ⁻¹ᵁ U) (hw : W ≤ V) (a : Γ(X, U)ˣ) :
    res hw (pullLE f hv a) = pullLE f (hw.trans hv) a := by
  apply Units.ext
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(Y, W) => g (a : Γ(X, U)))
    (f.appLE_map hv (homOfLE hw).op)

theorem pullLE_res (f : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (hw : W ≤ f ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pullLE f hw (res h a) =
      pullLE f (hw.trans ((Opens.map f.base).map (homOfLE h)).le) a := by
  apply Units.ext
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(Y, W) => g (a : Γ(X, U)))
    (f.map_appLE hw (homOfLE h).op)

theorem res_pullU (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)ˣ) : res h (pullU f U a) = pullLE f h a := rfl

theorem pullLE_id {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    pullLE (𝟙 X) h a = res h a := by
  apply Units.ext
  have e : (𝟙 X : X ⟶ X).appLE U V h = X.presheaf.map (homOfLE h).op := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(X, V) => g (a : Γ(X, U))) e

theorem pullLE_comp {Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (hv : V ≤ f ⁻¹ᵁ U) (hw : W ≤ h ⁻¹ᵁ V)
    (a : Γ(X, U)ˣ) :
    pullLE h hw (pullLE f hv a) =
      pullLE (h ≫ f) (hw.trans ((Opens.map h.base).map (homOfLE hv)).le) a := by
  apply Units.ext
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(Z, W) => g (a : Γ(X, U)))
    (Scheme.Hom.appLE_comp_appLE h f U V W hv hw)

namespace LB

/-- A section of the transition function on a product chart restricts
to the degreewise product of the pulled-back transitions. -/
private theorem res_linComb_g (L : LB X) {K : Type u} [Fintype K]
    (f : K → Y ⟶ X) (n : K → ℤ) (i j : K → L.ι) {V : Y.Opens}
    (h : V ≤ wchart L f i ⊓ wchart L f j) :
    res h ((LinComb L f n).g i j) =
      ∏ k, pullLE (f k) (h.trans (le_inf (inf_le_left.trans (wchart_le L f i k))
        (inf_le_right.trans (wchart_le L f j k)))) (L.g (i k) (j k)) ^ (n k) := by
  simp only [LinComb, map_prod, map_zpow, res_pullU, res_pullLE]

/-- Pullback and integral tensor powers preserve the line-bundle cocycle. -/
theorem IsLB.linComb {L : LB X} (hL : L.IsLB) {K : Type u} [Fintype K]
    (f : K → Y ⟶ X) (n : K → ℤ) : (LinComb L f n).IsLB where
  cover := top_le_iff.mp fun y _ => by
    have h (k : K) : ∃ i, f k y ∈ L.U i := by
      apply Opens.mem_iSup.mp
      rw [hL.cover]
      exact trivial
    choose i hi using h
    exact Opens.mem_iSup.mpr ⟨i, Set.mem_iInter.mpr hi⟩
  g_self i := by
    rw [res_linComb_g]
    apply Finset.prod_eq_one
    intro k _
    have hv : wchart L f i ≤ f k ⁻¹ᵁ L.U (i k) := wchart_le L f i k
    rw [← pullLE_res (f k) (le_inf le_rfl le_rfl : L.U (i k) ≤ L.U (i k) ⊓ L.U (i k)) hv,
      hL.g_self, map_one, one_zpow]
  cocycle i j k := by
    rw [res_linComb_g, res_linComb_g, res_linComb_g, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    let V := wchart L f i ⊓ wchart L f j ⊓ wchart L f k
    let U := L.U (i l) ⊓ L.U (j l) ⊓ L.U (k l)
    have hi : V ≤ f l ⁻¹ᵁ L.U (i l) := inf_le_left.trans (inf_le_left.trans (wchart_le L f i l))
    have hj : V ≤ f l ⁻¹ᵁ L.U (j l) := inf_le_left.trans (inf_le_right.trans (wchart_le L f j l))
    have hk : V ≤ f l ⁻¹ᵁ L.U (k l) := inf_le_right.trans (wchart_le L f k l)
    have hV : V ≤ f l ⁻¹ᵁ U := le_inf (le_inf hi hj) hk
    rw [← pullLE_res (f l) (inf_le_left : U ≤ L.U (i l) ⊓ L.U (j l)) hV,
      ← pullLE_res (f l) (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U ≤ L.U (j l) ⊓ L.U (k l)) hV,
      ← pullLE_res (f l) (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U ≤ L.U (i l) ⊓ L.U (k l)) hV, ← mul_zpow, ← map_mul, hL.cocycle]

theorem IsLB.pull {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) : (L.pull f).IsLB :=
  hL.linComb (fun _ : PUnit => f) (fun _ => 1)

/-- Glued generators pull back to glued generators. -/
theorem Gen.IsGen.pullGen {L : LB X} {K : Type u} [Fintype K] (f : K → Y ⟶ X)
    (n : K → ℤ) {t : Gen (LinComb L f n)} (ht : t.IsGen) {Z : Scheme.{u}} (h : Z ⟶ Y) :
    (L.pullGen f n t h).IsGen := by
  intro i j
  let f' (k : K) := h ≫ f k
  have e (i : K → L.ι) : wchart L f' i ≤ h ⁻¹ᵁ (wchart L f i) := fun _ hx =>
    Set.mem_iInter.mpr fun k => Set.mem_iInter.mp hx k
  have eij : wchart L f' i ⊓ wchart L f' j ≤ h ⁻¹ᵁ (wchart L f i ⊓ wchart L f j) :=
    le_inf (inf_le_left.trans (e i)) (inf_le_right.trans (e j))
  have hg : pullLE h eij ((LinComb L f n).g i j) = (LinComb L f' n).g i j := by
    simp only [LinComb, res_pullU, map_prod, map_zpow, pullLE_comp, f']
  simp only [LB.pullGen, res_pullU, res_pullLE]
  rw [← pullLE_res h inf_le_left eij, ← pullLE_res h inf_le_right eij, ht i j, map_mul, hg]

end LB

/-- Two successive restrictions of a unit agree with restriction to the smallest open. -/
theorem res_res {U V W : X.Opens} (hv : V ≤ U) (hw : W ≤ V) (a : Γ(X, U)ˣ) :
    res hw (res hv a) = res (hw.trans hv) a := by
  apply Units.ext
  have e := congrArg (fun g : Γ(X, U) ⟶ Γ(X, W) => g (a : Γ(X, U)))
    (X.presheaf.map_comp (homOfLE hv).op (homOfLE hw).op)
  exact e.symm

namespace LB

private theorem IsLB.restrict_cocycle {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    {V : X.Opens} (hi : V ≤ L.U i) (hj : V ≤ L.U j) (hk : V ≤ L.U k) :
    res (le_inf hi hj) (L.g i j) * res (le_inf hj hk) (L.g j k) =
      res (le_inf hi hk) (L.g i k) := by
  have e := congrArg (res (le_inf (le_inf hi hj) hk)) (hL.cocycle i j k)
  simpa only [map_mul, res_res] using e

/-- A line bundle is identified with itself by its transition functions on
the common refinement of the two trivializing covers. -/
theorem IsLB.gen_refl {L : LB X} (hL : L.IsLB) : ∃ t : LB.Iso L L, t.IsGen := by
  refine ⟨⟨fun i => L.g i.1 i.2⟩, fun i j => ?_⟩
  have hi₁ : (L.div L).U i ⊓ (L.div L).U j ≤ L.U i.1 := inf_le_left.trans inf_le_left
  have hi₂ : (L.div L).U i ⊓ (L.div L).U j ≤ L.U i.2 := inf_le_left.trans inf_le_right
  have hj₁ : (L.div L).U i ⊓ (L.div L).U j ≤ L.U j.1 := inf_le_right.trans inf_le_left
  have hj₂ : (L.div L).U i ⊓ (L.div L).U j ≤ L.U j.2 := inf_le_right.trans inf_le_right
  have a := hL.restrict_cocycle i.1 j.1 j.2 hi₁ hj₁ hj₂
  have b := hL.restrict_cocycle i.1 j.2 i.2 hi₁ hj₂ hi₂
  have c := hL.restrict_cocycle i.2 j.2 i.2 hi₂ hj₂ hi₂
  have c' : res (le_inf hi₂ hi₂) (L.g i.2 i.2) = 1 := by
    have e := congrArg (res hi₂) (hL.g_self i.2)
    simpa only [map_one, res_res] using e
  have d := inv_eq_of_mul_eq_one_right (c.trans c')
  simp only [div, map_mul, map_inv, res_res]
  rw [d, mul_right_comm, a, b]

end LB

end ReciprocityTheory.ChartRestriction.G.Semi
