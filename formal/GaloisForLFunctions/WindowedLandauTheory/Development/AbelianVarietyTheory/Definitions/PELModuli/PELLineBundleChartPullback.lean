import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback

/-! Maps between local trivializations transport generators and identify different pullback charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.Semi

universe u

variable {X Y Z : Scheme.{u}}

/-- A refinement of the pulled-back charts, with the same transition sections. -/
structure ChartPull (L' : LB Y) (L : LB X) (f : Y ⟶ X) where
  idx : L'.ι → L.ι
  le : ∀ i, L'.U i ≤ f ⁻¹ᵁ L.U (idx i)
  g : ∀ i j, L'.g i j = pullLE f (U := L.U (idx i) ⊓ L.U (idx j))
    (le_inf (inf_le_left.trans (le i)) (inf_le_right.trans (le j))) (L.g (idx i) (idx j))

namespace ChartPull

theorem restrict_g {L' : LB Y} {L : LB X} {f : Y ⟶ X} (P : ChartPull L' L f)
    {U : Y.Opens} {i j : L'.ι} (hi : U ≤ L'.U i) (hj : U ≤ L'.U j) :
    res (le_inf hi hj) (L'.g i j) = pullLE f (U := L.U (P.idx i) ⊓ L.U (P.idx j))
      (le_inf (hi.trans (P.le i)) (hj.trans (P.le j)))
      (L.g (P.idx i) (P.idx j)) := by
  exact (congrArg (res (le_inf hi hj)) (P.g i j)).trans (res_pullLE _ _ _ _)

private theorem pullChart_le (L : LB X) (f : Y ⟶ X)
    (I J : PUnit.{u+1} → L.ι) (k : PUnit.{u+1}) :
    (L.pull f).U I ⊓ (L.pull f).U J ≤ f ⁻¹ᵁ (L.U (I k) ⊓ L.U (J k)) :=
  le_inf (inf_le_left.trans (LB.wchart_le L _ I k))
    (inf_le_right.trans (LB.wchart_le L _ J k))

private def pullTransition (L : LB X) (f : Y ⟶ X)
    (I J : PUnit.{u+1} → L.ι) (k : PUnit.{u+1}) : Γ(Y, (L.pull f).U I ⊓ (L.pull f).U J)ˣ :=
  res (pullChart_le L f I J k) (pullU f (L.U (I k) ⊓ L.U (J k)) (L.g (I k) (J k)))

private theorem pull_g_prod (L : LB X) (f : Y ⟶ X) (I J : PUnit.{u+1} → L.ι) :
    (L.pull f).g I J = ∏ k, pullTransition L f I J k ^ (1 : ℤ) := rfl

private theorem prod_punit_zpow_one {M : Type u} [CommGroup M] (g : PUnit.{u+1} → M) :
    (∏ k, g k ^ (1 : ℤ)) = g PUnit.unit :=
  (Fintype.prod_subsingleton (fun k => g k ^ (1 : ℤ)) PUnit.unit).trans (zpow_one _)

private theorem pull_g (L : LB X) (f : Y ⟶ X) (I J : PUnit.{u+1} → L.ι) :
    (L.pull f).g I J = pullLE f (pullChart_le L f I J PUnit.unit) (L.g (I PUnit.unit) (J PUnit.unit)) :=
  (pull_g_prod L f I J).trans ((prod_punit_zpow_one (pullTransition L f I J)).trans
    (res_pullU f (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) (pullChart_le L f I J PUnit.unit)
      (L.g (I PUnit.unit) (J PUnit.unit))))

/-- The chosen charts of the pullback lie in the pulled-back charts of the original bundle. -/
def pull (L : LB X) (f : Y ⟶ X) : ChartPull (L.pull f) L f where
  idx J := J PUnit.unit
  le J := LB.wchart_le L _ J PUnit.unit
  g I J := pull_g L f I J

/-- The identity chart refinement leaves the transition functions unchanged. -/
def id (L : LB X) : ChartPull L L (𝟙 X) where
  idx i := i
  le _ := le_rfl
  g _ _ := (res_refl _).symm.trans (pullLE_id _ _).symm

/-- Refinements compose by functoriality of pullback on sections. -/
def comp {L'' : LB Z} {L' : LB Y} {L : LB X} {f : Z ⟶ Y} {g : Y ⟶ X}
    (P : ChartPull L'' L' f) (Q : ChartPull L' L g) : ChartPull L'' L (f ≫ g) where
  idx i := Q.idx (P.idx i)
  le i := (P.le i).trans ((Opens.map f.base).map (homOfLE (Q.le (P.idx i)))).le
  g i j := (P.g i j).trans ((congrArg (pullLE f _) (Q.g (P.idx i) (P.idx j))).trans
    (pullLE_comp f g _ _ _))

/-- A glued generator restricts to each refined chart. -/
theorem exists_gen {L' : LB Y} {L : LB X} {f : Y ⟶ X} (P : ChartPull L' L f)
    {t : L.Gen} (ht : t.IsGen) : ∃ t' : L'.Gen, t'.IsGen := by
  let s (i : L'.ι) := pullLE f (P.le i) (t.s (P.idx i))
  refine ⟨⟨s⟩, fun i j => ?_⟩
  let V := L'.U i ⊓ L'.U j
  have h : V ≤ f ⁻¹ᵁ (L.U (P.idx i) ⊓ L.U (P.idx j)) :=
    le_inf (inf_le_left.trans (P.le i)) (inf_le_right.trans (P.le j))
  have ei : res (inf_le_left : V ≤ L'.U i) (s i) =
      pullLE f h (res inf_le_left (t.s (P.idx i))) :=
    (res_pullLE f (P.le i) inf_le_left _).trans (pullLE_res f inf_le_left h _).symm
  have ej : res (inf_le_right : V ≤ L'.U j) (s j) =
      pullLE f h (res inf_le_right (t.s (P.idx j))) :=
    (res_pullLE f (P.le j) inf_le_right _).trans (pullLE_res f inf_le_right h _).symm
  exact ei.trans ((congrArg (pullLE f h) (ht (P.idx i) (P.idx j))).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (P.g i j).symm ej.symm)))

def div {A' B' : LB Y} {A B : LB X} {f : Y ⟶ X} (P : ChartPull A' A f) (Q : ChartPull B' B f) :
    ChartPull (B'.div A') (B.div A) f where
  idx i := (Q.idx i.1, P.idx i.2)
  le i := le_inf (inf_le_left.trans (Q.le i.1)) (inf_le_right.trans (P.le i.2))
  g i j := by
    let V := (B'.div A').U i ⊓ (B'.div A').U j
    let i₀ := (Q.idx i.1, P.idx i.2)
    let j₀ := (Q.idx j.1, P.idx j.2)
    let U := (B.div A).U i₀ ⊓ (B.div A).U j₀
    let hi : V ≤ B'.U i.1 := inf_le_left.trans inf_le_left
    let hj : V ≤ B'.U j.1 := inf_le_right.trans inf_le_left
    let hi' : V ≤ A'.U i.2 := inf_le_left.trans inf_le_right
    let hj' : V ≤ A'.U j.2 := inf_le_right.trans inf_le_right
    let r₁ : U ≤ B.U i₀.1 ⊓ B.U j₀.1 :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    let r₂ : U ≤ A.U i₀.2 ⊓ A.U j₀.2 :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    let h : V ≤ f ⁻¹ᵁ U := le_inf (le_inf (hi.trans (Q.le i.1)) (hi'.trans (P.le i.2)))
      (le_inf (hj.trans (Q.le j.1)) (hj'.trans (P.le j.2)))
    have e₁ : pullLE f h (res r₁ (B.g i₀.1 j₀.1)) = res (le_inf hi hj) (B'.g i.1 j.1) :=
      (pullLE_res f r₁ h _).trans (Q.restrict_g hi hj).symm
    have e₂ : pullLE f h (res r₂ (A.g i₀.2 j₀.2)) = res (le_inf hi' hj') (A'.g i.2 j.2) :=
      (pullLE_res f r₂ h _).trans (P.restrict_g hi' hj').symm
    have e₃ := (res_refl _).symm.trans (LB.res_div_g A B (i := i₀) (j := j₀) inf_le_left inf_le_right)
    have e₄ := (res_refl _).symm.trans (LB.res_div_g A' B' (i := i) (j := j) inf_le_left inf_le_right)
    have e₅ := (congrArg (pullLE f h) e₃).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) e₁ ((map_inv _ _).trans (congrArg Inv.inv e₂))))
    exact e₄.trans e₅.symm

/-- A line-bundle isomorphism pulls back along a refinement of its two covers. -/
theorem exists_iso {A' B' : LB Y} {A B : LB X} {f : Y ⟶ X} (P : ChartPull A' A f)
    (Q : ChartPull B' B f) {t : LB.Iso A B} (ht : t.IsGen) : ∃ t' : LB.Iso A' B', t'.IsGen :=
  (P.div Q).exists_gen ht

/-- Two refinements of a common pullback present isomorphic line bundles. -/
theorem iso_of_common {A B : LB Y} {L : LB X} {f : Y ⟶ X}
    (P : ChartPull A L f) (Q : ChartPull B L f) (hL : L.IsLB) :
    ∃ t : LB.Iso A B, t.IsGen := by
  refine ⟨⟨fun i => pullLE f (U := L.U (Q.idx i.1) ⊓ L.U (P.idx i.2)) (le_inf (inf_le_left.trans (Q.le i.1))
    (inf_le_right.trans (P.le i.2))) (L.g (Q.idx i.1) (P.idx i.2))⟩, fun i j => ?_⟩
  let U := (B.div A).U i ⊓ (B.div A).U j
  have hi₁ : U ≤ B.U i.1 := inf_le_left.trans inf_le_left
  have hi₂ : U ≤ A.U i.2 := inf_le_left.trans inf_le_right
  have hj₁ : U ≤ B.U j.1 := inf_le_right.trans inf_le_left
  have hj₂ : U ≤ A.U j.2 := inf_le_right.trans inf_le_right
  have hi := hi₁.trans (Q.le i.1)
  have hi' := hi₂.trans (P.le i.2)
  have hj := hj₁.trans (Q.le j.1)
  have hj' := hj₂.trans (P.le j.2)
  have e₁ := hL.pullLE_cocycle f hi hj hj'
  have e₂ := hL.pullLE_cocycle f hi hj' hi'
  have e₃ := hL.pullLE_cocycle f hi' hj' hi'
  have e₄ : pullLE f (U := L.U (P.idx i.2) ⊓ L.U (P.idx i.2))
      (le_inf hi' hi') (L.g (P.idx i.2) (P.idx i.2)) = 1 :=
    (pullLE_res f (le_inf le_rfl le_rfl) hi' _).symm.trans
      ((congrArg (pullLE f hi') (hL.g_self (P.idx i.2))).trans (map_one _))
  let a := pullLE f (U := L.U (Q.idx i.1) ⊓ L.U (Q.idx j.1))
    (le_inf hi hj) (L.g (Q.idx i.1) (Q.idx j.1))
  let b := pullLE f (U := L.U (P.idx i.2) ⊓ L.U (P.idx j.2))
    (le_inf hi' hj') (L.g (P.idx i.2) (P.idx j.2))
  let c := pullLE f (U := L.U (Q.idx j.1) ⊓ L.U (P.idx j.2))
    (le_inf hj hj') (L.g (Q.idx j.1) (P.idx j.2))
  let d := pullLE f (U := L.U (P.idx j.2) ⊓ L.U (P.idx i.2))
    (le_inf hj' hi') (L.g (P.idx j.2) (P.idx i.2))
  have e₅ : b⁻¹ = d := inv_eq_of_mul_eq_one_right (e₃.trans e₄)
  have e₆ : (B.div A).g i j = a * b⁻¹ :=
    (res_refl _).symm.trans ((LB.res_div_g A B (i := i) (j := j) inf_le_left inf_le_right).trans
      (congrArg₂ (· * ·) (Q.restrict_g hi₁ hj₁) (congrArg Inv.inv (P.restrict_g hi₂ hj₂))))
  refine (res_pullLE _ _ _ _).trans (e₂.symm.trans ?_)
  exact (congrArg (· * d) e₁.symm).trans ((mul_right_comm a c d).trans
    ((congrArg (fun u => a * u * c) e₅.symm).trans
      (congrArg₂ (· * ·) e₆.symm (res_pullLE _ _ _ _).symm)))

end ChartPull

end ReciprocityTheory.ChartRestriction.G.Semi
