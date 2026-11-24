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
  g : ∀ i j, L'.g i j = pullLE f (le_inf (inf_le_left.trans (le i))
    (inf_le_right.trans (le j))) (L.g (idx i) (idx j))

namespace ChartPull

theorem restrict_g {L' : LB Y} {L : LB X} {f : Y ⟶ X} (P : ChartPull L' L f)
    {U : Y.Opens} {i j : L'.ι} (hi : U ≤ L'.U i) (hj : U ≤ L'.U j) :
    res (le_inf hi hj) (L'.g i j) = pullLE f (le_inf (hi.trans (P.le i)) (hj.trans (P.le j)))
      (L.g (P.idx i) (P.idx j)) := by
  rw [P.g, res_pullLE]

/-- The chosen charts of the pullback lie in the pulled-back charts of the original bundle. -/
def pull (L : LB X) (f : Y ⟶ X) : ChartPull (L.pull f) L f where
  idx J := J PUnit.unit
  le J := LB.wchart_le L _ J PUnit.unit
  g I J := by
    simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one, res_pullU]

/-- The identity chart refinement leaves the transition functions unchanged. -/
def id (L : LB X) : ChartPull L L (𝟙 X) where
  idx i := i
  le _ := le_rfl
  g i j := by rw [pullLE_id, res_refl]

/-- Refinements compose by functoriality of pullback on sections. -/
def comp {L'' : LB Z} {L' : LB Y} {L : LB X} {f : Z ⟶ Y} {g : Y ⟶ X}
    (P : ChartPull L'' L' f) (Q : ChartPull L' L g) : ChartPull L'' L (f ≫ g) where
  idx i := Q.idx (P.idx i)
  le i := (P.le i).trans ((Opens.map f.base).map (homOfLE (Q.le (P.idx i)))).le
  g i j := by rw [P.g, Q.g, pullLE_comp]

/-- A glued generator restricts to each refined chart. -/
theorem exists_gen {L' : LB Y} {L : LB X} {f : Y ⟶ X} (P : ChartPull L' L f)
    {t : L.Gen} (ht : t.IsGen) : ∃ t' : L'.Gen, t'.IsGen := by
  refine ⟨⟨fun i => pullLE f (P.le i) (t.s (P.idx i))⟩, fun i j => ?_⟩
  have h : L'.U i ⊓ L'.U j ≤ f ⁻¹ᵁ (L.U (P.idx i) ⊓ L.U (P.idx j)) :=
    le_inf (inf_le_left.trans (P.le i)) (inf_le_right.trans (P.le j))
  simp only [res_pullLE]
  rw [← pullLE_res f inf_le_left h, ← pullLE_res f inf_le_right h, ht (P.idx i) (P.idx j), map_mul, P.g, pullLE_res]

def div {A' B' : LB Y} {A B : LB X} {f : Y ⟶ X} (P : ChartPull A' A f) (Q : ChartPull B' B f) :
    ChartPull (B'.div A') (B.div A) f where
  idx i := (Q.idx i.1, P.idx i.2)
  le i := le_inf (inf_le_left.trans (Q.le i.1)) (inf_le_right.trans (P.le i.2))
  g i j := by
    simp only [LB.div, map_mul, map_inv, Q.g, P.g, res_pullLE, pullLE_res]

/-- A line-bundle isomorphism pulls back along a refinement of its two covers. -/
theorem exists_iso {A' B' : LB Y} {A B : LB X} {f : Y ⟶ X} (P : ChartPull A' A f)
    (Q : ChartPull B' B f) {t : LB.Iso A B} (ht : t.IsGen) : ∃ t' : LB.Iso A' B', t'.IsGen :=
  (P.div Q).exists_gen ht

private theorem pullLE_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) {U : Y.Opens}
    {i j k : L.ι} (hi : U ≤ f ⁻¹ᵁ L.U i) (hj : U ≤ f ⁻¹ᵁ L.U j) (hk : U ≤ f ⁻¹ᵁ L.U k) :
    pullLE f (le_inf hi hj) (L.g i j) * pullLE f (le_inf hj hk) (L.g j k) =
      pullLE f (le_inf hi hk) (L.g i k) := by
  have e := congrArg (pullLE f (le_inf (le_inf hi hj) hk)) (hL.cocycle i j k)
  simpa only [map_mul, pullLE_res] using e

/-- Two refinements of a common pullback present isomorphic line bundles. -/
theorem iso_of_common {A B : LB Y} {L : LB X} {f : Y ⟶ X}
    (P : ChartPull A L f) (Q : ChartPull B L f) (hL : L.IsLB) :
    ∃ t : LB.Iso A B, t.IsGen := by
  refine ⟨⟨fun i => pullLE f (le_inf (inf_le_left.trans (Q.le i.1))
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
  have e₁ := pullLE_cocycle hL f hi hj hj'
  have e₂ := pullLE_cocycle hL f hi hj' hi'
  have e₃ := pullLE_cocycle hL f hi' hj' hi'
  have e₄ : pullLE f (le_inf hi' hi') (L.g (P.idx i.2) (P.idx i.2)) = 1 := by
    rw [← pullLE_res f (le_inf le_rfl le_rfl) hi', hL.g_self, map_one]
  have e₅ := inv_eq_of_mul_eq_one_right (e₃.trans e₄)
  simp only [LB.div, map_mul, map_inv, res_pullLE, Q.g, P.g]
  rw [e₅, mul_right_comm, e₁, e₂]

end ChartPull

end ReciprocityTheory.ChartRestriction.G.Semi
