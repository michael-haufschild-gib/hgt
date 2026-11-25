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
  have h : X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op = 𝟙 Γ(X, U) :=
    (congrArg X.presheaf.map e).trans (X.presheaf.map_id (op U))
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(X, U) => g (a : Γ(X, U))) h

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
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact Category.id_comp _
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(X, V) => g (a : Γ(X, U))) e

theorem pullLE_comp {Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (hv : V ≤ f ⁻¹ᵁ U) (hw : W ≤ h ⁻¹ᵁ V)
    (a : Γ(X, U)ˣ) :
    pullLE h hw (pullLE f hv a) =
      pullLE (h ≫ f) (hw.trans ((Opens.map h.base).map (homOfLE hv)).le) a := by
  apply Units.ext
  exact congrArg (fun g : Γ(X, U) ⟶ Γ(Z, W) => g (a : Γ(X, U)))
    (Scheme.Hom.appLE_comp_appLE h f U V W hv hw)

/-- Two successive restrictions of a unit agree with restriction to the smallest open. -/
theorem res_res {U V W : X.Opens} (hv : V ≤ U) (hw : W ≤ V) (a : Γ(X, U)ˣ) :
    res hw (res hv a) = res (hw.trans hv) a := by
  apply Units.ext
  have e := congrArg (fun g : Γ(X, U) ⟶ Γ(X, W) => g (a : Γ(X, U)))
    (X.presheaf.map_comp (homOfLE hv).op (homOfLE hw).op)
  exact e.symm

namespace LB

/-- A section of the transition function on a product chart restricts
to the degreewise product of the pulled-back transitions. -/
private theorem chartPair_le (L : LB X) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (i j : K → L.ι) (k : K) :
    wchart L f i ⊓ wchart L f j ≤ f k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) :=
  le_inf (inf_le_left.trans (wchart_le L f i k)) (inf_le_right.trans (wchart_le L f j k))

private def chartTransition (L : LB X) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (i j : K → L.ι) (k : K) : Γ(Y, wchart L f i ⊓ wchart L f j)ˣ :=
  res (chartPair_le L f i j k) (pullU (f k) _ (L.g (i k) (j k)))

private theorem linComb_g_eq (L : LB X) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (n : K → ℤ) (i j : K → L.ι) :
    (LinComb L f n).g i j = ∏ k, chartTransition L f i j k ^ n k := rfl

private theorem res_chartTransition (L : LB X) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (i j : K → L.ι) {V : Y.Opens}
    (h : V ≤ wchart L f i ⊓ wchart L f j) (k : K) :
    res h (chartTransition L f i j k) =
      pullLE (f k) (h.trans (chartPair_le L f i j k)) (L.g (i k) (j k)) :=
  (res_res (chartPair_le L f i j k) h _).trans (res_pullU _ _ _ _)

private theorem map_prod_zpow {R S : Type u} [CommGroup R] [CommGroup S]
    {K : Type u} [Fintype K] (f : R →* S) (a : K → R) (n : K → ℤ) :
    f (∏ k, a k ^ n k) = ∏ k, f (a k) ^ n k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_zpow f (a k) (n k)

private theorem res_linComb_g (L : LB X) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (n : K → ℤ) (i j : K → L.ι) {V : Y.Opens}
    (h : V ≤ wchart L f i ⊓ wchart L f j) :
    res h ((LinComb L f n).g i j) =
      ∏ k, pullLE (f k) (h.trans (chartPair_le L f i j k)) (L.g (i k) (j k)) ^ n k := by
  refine (congrArg (res h) (linComb_g_eq L f n i j)).trans
    ((map_prod_zpow (res h) (chartTransition L f i j) n).trans ?_)
  exact Finset.prod_congr rfl fun k _ => congrArg (fun a => a ^ n k) (res_chartTransition L f i j h k)

/-- The cocycle identity on pulled-back charts, restricted to a common smaller open. -/
theorem IsLB.pullLE_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) {V : Y.Opens}
    {i j k : L.ι} (hi : V ≤ f ⁻¹ᵁ L.U i) (hj : V ≤ f ⁻¹ᵁ L.U j)
    (hk : V ≤ f ⁻¹ᵁ L.U k) :
    pullLE f (U := L.U i ⊓ L.U j) (le_inf hi hj) (L.g i j) *
      pullLE f (U := L.U j ⊓ L.U k) (le_inf hj hk) (L.g j k) =
      pullLE f (U := L.U i ⊓ L.U k) (le_inf hi hk) (L.g i k) := by
  let U := L.U i ⊓ L.U j ⊓ L.U k
  have hV : V ≤ f ⁻¹ᵁ U := le_inf (le_inf hi hj) hk
  let h₁ : U ≤ L.U i ⊓ L.U j := inf_le_left
  let h₂ : U ≤ L.U j ⊓ L.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  let h₃ : U ≤ L.U i ⊓ L.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  calc
    _ = pullLE f hV (res h₁ (L.g i j)) * pullLE f hV (res h₂ (L.g j k)) :=
      congrArg₂ (· * ·) (pullLE_res f h₁ hV _).symm (pullLE_res f h₂ hV _).symm
    _ = pullLE f hV (res h₁ (L.g i j) * res h₂ (L.g j k)) := (map_mul _ _ _).symm
    _ = pullLE f hV (res h₃ (L.g i k)) := congrArg (pullLE f hV) (hL.cocycle i j k)
    _ = _ := pullLE_res f h₃ hV _

/-- Pullback and integral tensor powers preserve the line-bundle cocycle. -/
theorem IsLB.linComb {L : LB X} (hL : L.IsLB) {K : Type u} [Fintype K]
    (f : K → (Y ⟶ X)) (n : K → ℤ) : (LinComb L f n).IsLB where
  cover := top_le_iff.mp fun y _ => by
    have h (k : K) : ∃ i, f k y ∈ L.U i := by
      apply Opens.mem_iSup.mp
      rw [hL.cover]
      exact trivial
    choose i hi using h
    exact Opens.mem_iSup.mpr ⟨i, Set.mem_iInter.mpr hi⟩
  g_self i := by
    refine (res_linComb_g L f n i i (V := wchart L f i) (le_inf le_rfl le_rfl)).trans ?_
    refine Finset.prod_eq_one fun k _ => ?_
    let h : L.U (i k) ≤ L.U (i k) ⊓ L.U (i k) := le_inf le_rfl le_rfl
    have hv := wchart_le L f i k
    have e : pullLE (f k) (show wchart L f i ≤ f k ⁻¹ᵁ (L.U (i k) ⊓ L.U (i k)) from
        le_inf hv hv) (L.g (i k) (i k)) = 1 :=
      (pullLE_res (f k) h hv _).symm.trans
        ((congrArg (pullLE (f k) hv) (hL.g_self (i k))).trans (map_one _))
    exact (congrArg (fun a => a ^ n k) e).trans (one_zpow _)
  cocycle i j k := by
    let V := wchart L f i ⊓ wchart L f j ⊓ wchart L f k
    have vi : V ≤ wchart L f i := inf_le_left.trans inf_le_left
    have vj : V ≤ wchart L f j := inf_le_left.trans inf_le_right
    have vk : V ≤ wchart L f k := inf_le_right
    have e₁ := res_linComb_g L f n i j (le_inf vi vj)
    have e₂ := res_linComb_g L f n j k (le_inf vj vk)
    have e₃ := res_linComb_g L f n i k (le_inf vi vk)
    refine (congrArg₂ (· * ·) e₁ e₂).trans (Eq.trans (Finset.prod_mul_distrib).symm ?_)
    refine (Finset.prod_congr rfl fun l _ => ?_).trans e₃.symm
    exact (mul_zpow _ _ _).symm.trans (congrArg (fun a => a ^ n l)
      (hL.pullLE_cocycle (f l) (vi.trans (wchart_le L f i l))
        (vj.trans (wchart_le L f j l)) (vk.trans (wchart_le L f k l))))

theorem IsLB.pull {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) : (L.pull f).IsLB :=
  hL.linComb (fun _ : PUnit => f) (fun _ => 1)

/-- Glued generators pull back to glued generators. -/
theorem Gen.IsGen.pullGen {L : LB X} {K : Type u} [Fintype K] (f : K → (Y ⟶ X))
    (n : K → ℤ) {t : Gen (LinComb L f n)} (ht : t.IsGen) {Z : Scheme.{u}} (h : Z ⟶ Y) :
    (L.pullGen f n t h).IsGen := by
  intro i j
  let f' (k : K) := h ≫ f k
  let W := wchart L f i ⊓ wchart L f j
  let V := wchart L f' i ⊓ wchart L f' j
  have e (j : K → L.ι) : wchart L f' j ≤ h ⁻¹ᵁ (wchart L f j) := fun _ hx =>
    Set.mem_iInter.mpr fun k => Set.mem_iInter.mp hx k
  have eij : V ≤ h ⁻¹ᵁ W := le_inf (inf_le_left.trans (e i)) (inf_le_right.trans (e j))
  have hg₁ := (res_refl _).symm.trans (res_linComb_g L f n i j (V := W) le_rfl)
  have hg₂ := (res_refl _).symm.trans (res_linComb_g L f' n i j (V := V) le_rfl)
  have hg : pullLE h eij ((LinComb L f n).g i j) = (LinComb L f' n).g i j := by
    refine (congrArg (pullLE h eij) hg₁).trans ((map_prod _ _ _).trans ?_)
    refine (Finset.prod_congr rfl fun k _ => ?_).trans hg₂.symm
    exact (map_zpow _ _ _).trans (congrArg (fun a => a ^ n k) (pullLE_comp h (f k) _ eij _))
  let r (k : K → L.ι) : Γ(Z, wchart L f' k)ˣ := (L.pullGen f n t h).s k
  let hi : W ≤ wchart L f i := inf_le_left
  let hj : W ≤ wchart L f j := inf_le_right
  let hi' : V ≤ wchart L f' i := inf_le_left
  let hj' : V ≤ wchart L f' j := inf_le_right
  have ei : res hi' (r i) = pullLE h eij (res hi (t.s i)) :=
    (res_res (e i) hi' _).trans ((res_pullU _ _ _ _).trans (pullLE_res h hi eij _).symm)
  have ej : res hj' (r j) = pullLE h eij (res hj (t.s j)) :=
    (res_res (e j) hj' _).trans ((res_pullU _ _ _ _).trans (pullLE_res h hj eij _).symm)
  have et := congrArg (pullLE h eij) (ht i j)
  exact ei.trans (et.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg ej.symm)))

end LB

namespace LB

/-- Restriction of a quotient transition to any smaller common open. -/
theorem res_div_g (A B : LB X) {i j : (B.div A).ι} {V : X.Opens}
    (hi : V ≤ (B.div A).U i) (hj : V ≤ (B.div A).U j) :
    res (le_inf hi hj) ((B.div A).g i j) =
      res (le_inf (hi.trans inf_le_left) (hj.trans inf_le_left)) (B.g i.1 j.1) *
        (res (le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)) (A.g i.2 j.2))⁻¹ := by
  let h := le_inf hi hj
  let hb : (B.div A).U i ⊓ (B.div A).U j ≤ B.U i.1 ⊓ B.U j.1 :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  let ha : (B.div A).U i ⊓ (B.div A).U j ≤ A.U i.2 ⊓ A.U j.2 :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  change res h (res hb (B.g i.1 j.1) * (res ha (A.g i.2 j.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (res_res hb h _)
    ((map_inv _ _).trans (congrArg Inv.inv (res_res ha h _))))

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
  let x := res (le_inf hi₁ hj₁) (L.g i.1 j.1)
  let y := res (le_inf hj₁ hj₂) (L.g j.1 j.2)
  let z := res (le_inf hj₂ hi₂) (L.g j.2 i.2)
  let w := (res (le_inf hi₂ hj₂) (L.g i.2 j.2))⁻¹
  have e : res (le_inf hi₁ hi₂) (L.g i.1 i.2) = x * w * y :=
    b.symm.trans ((congrArg (· * z) a.symm).trans
      ((mul_right_comm x y z).trans (congrArg (fun c => x * c * y) d.symm)))
  have h := (res_div_g L L (i := i) (j := j) inf_le_left inf_le_right).symm.trans
    (res_refl ((L.div L).g i j))
  exact e.trans (congrArg (· * y) h)

end LB

end ReciprocityTheory.ChartRestriction.G.Semi
