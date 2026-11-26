import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundlePowerProducts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELSectionValues

/-! Repeated pullback factors and powers on one cover have the same transitions
on the constant charts. Twisting adds the exponents on those charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LineBundleSections

variable {X Y : Scheme.{0}}

theorem transitionPower_isLB {M : LB Y} (hM : M.IsLB) (t : ℤ) :
    (transitionPower M t).IsLB where
  cover := hM.cover
  g_self i := by
    let U := M.U i
    let r := res (le_inf le_rfl le_rfl : U ≤ U ⊓ U)
    change r (M.g i i ^ t) = (1 : Γ(Y, U)ˣ)
    exact (map_zpow r _ _).trans
      ((congrArg (fun a : Γ(Y, U)ˣ => a ^ t) (hM.g_self i)).trans (one_zpow _))
  cocycle i j k := by
    let W := M.U i ⊓ M.U j ⊓ M.U k
    let r₁ := res (inf_le_left : W ≤ M.U i ⊓ M.U j)
    let r₂ := res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W ≤ M.U j ⊓ M.U k)
    let r₃ := res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W ≤ M.U i ⊓ M.U k)
    change r₁ (M.g i j ^ t) * r₂ (M.g j k ^ t) = r₃ (M.g i k ^ t)
    exact (congrArg₂ (· * ·) (map_zpow r₁ _ _) (map_zpow r₂ _ _)).trans
      ((mul_zpow _ _ _).symm.trans
        ((congrArg (fun a : Γ(Y, W)ˣ => a ^ t) (hM.cocycle i j k)).trans (map_zpow r₃ _ _).symm))

private theorem appLE_id {U V : Y.Opens} (h : V ≤ U) :
    (𝟙 Y : Y ⟶ Y).appLE U V h = Y.presheaf.map (homOfLE h).op := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact Category.id_comp _

/-- Restrict a global section to a refinement of its trivializations. -/
def refineCoordinates {L M : LB Y} (P : ChartPull M L (𝟙 Y)) (s : L.Sec) : M.Sec :=
  globalCoordinates (pullSection P (U := ⊤) (V := ⊤) le_top (globalCoordinates.symm s))

theorem refineCoordinates_apply {L M : LB Y} (P : ChartPull M L (𝟙 Y)) (s : L.Sec) (i : M.ι) :
    (refineCoordinates P s).f i = resG Y (P.le i) (s.f (P.idx i)) := by
  let x := (globalCoordinates (L := L)).symm s
  have he : (globalCoordinates x).f (P.idx i) = s.f (P.idx i) :=
    congrArg (fun t : L.Sec => t.f (P.idx i)) (globalCoordinates.apply_symm_apply s)
  rw [← he]
  change (globalCoordinates (pullSection P (U := ⊤) (V := ⊤) le_top x)).f i = _
  simp only [globalCoordinates_apply, coord_pullSection, appLE_id, resG_resG]
  exact (resG_resG _ _ _).symm

private theorem basicOpen_refineCoordinates {L M : LB Y} (P : ChartPull M L (𝟙 Y))
    (s : L.Sec) (i : M.ι) :
    Y.basicOpen ((refineCoordinates P s).f i) = nonzeroLocus s ⊓ M.U i :=
  (congrArg (fun a : Γ(Y, M.U i) => Y.basicOpen a) (refineCoordinates_apply P s i)).trans
    (basicOpen_coord_restrict s (P.idx i) (show M.U i ≤ L.U (P.idx i) from P.le i))

theorem nonzeroLocus_refineCoordinates {L M : LB Y} (hM : M.IsLB)
    (P : ChartPull M L (𝟙 Y)) (s : L.Sec) :
    nonzeroLocus (refineCoordinates P s) = nonzeroLocus s := by
  apply le_antisymm
  · intro y hy
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ((congrArg (fun U : Y.Opens => y ∈ U) (basicOpen_refineCoordinates P s i)).mp hi).1
  · intro y hy
    obtain ⟨i, hi⟩ := exists_chart hM y
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    exact (congrArg (fun U : Y.Opens => y ∈ U) (basicOpen_refineCoordinates P s i)).mpr ⟨hy, hi⟩

/-- Vanishing on the refined cover implies vanishing in every original chart. -/
theorem coord_eq_zero_of_refineCoordinates {L M : LB Y} (hM : M.IsLB)
    (P : ChartPull M L (𝟙 Y)) (s : L.Sec)
    (h : ∀ i, (refineCoordinates P s).f i = 0) (j : L.ι) : s.f j = 0 := by
  apply fn_ext
  intro y hy
  obtain ⟨i, hi⟩ := exists_chart hM y
  have hle : M.U i ≤ L.U (P.idx i) := P.le i
  have e := (gs_res (𝟙 Y) y hle hi (s.f (P.idx i))).symm.trans
    (congrArg (gs (𝟙 Y) y (M.U i)) ((refineCoordinates_apply P s i).symm.trans (h i)))
  have e' : gs (𝟙 Y) y (L.U (P.idx i)) (s.f (P.idx i)) = 0 := by
    simpa only [gs_eq (𝟙 Y) y (M.U i) hi, map_zero] using e
  exact (gs_compat s (𝟙 Y) y hy (hle hi)).trans
    ((congrArg (fun v => (gm (𝟙 Y) y _ (L.g j (P.idx i))).val * v) e').trans
      ((mul_zero _).trans (by simp only [gs_eq (𝟙 Y) y _ hy, map_zero])))

variable (L : LB X) (π : Y ⟶ X)

/-- The transition power of a pulled-back bundle refines the presentation with
one copy of the pullback for each factor. -/
def ChartPull.repeatedPullbackPower (N : ℕ) :
    ChartPull (transitionPower (L.pull π) (N : ℤ))
      (LB.LinComb L (K := Fin N) (fun _ => π) (fun _ => 1)) (𝟙 Y) where
  idx i := fun _ => i PUnit.unit
  le i := fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  g i j := by
    rw [pullLE_id]
    let M := L.pull π
    let W := M.U i ⊓ M.U j
    let U := L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)
    let f : Fin N → (Y ⟶ X) := fun _ => π
    let a : Fin N → L.ι := fun _ => i PUnit.unit
    let b : Fin N → L.ι := fun _ => j PUnit.unit
    let V := LB.wchart L f a ⊓ LB.wchart L f b
    let h : W ≤ V := le_inf
      (fun _ hz => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hz.1 PUnit.unit)
      (fun _ hz => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hz.2 PUnit.unit)
    let hπ (k : Fin N) : V ≤ π ⁻¹ᵁ U :=
      le_inf (inf_le_left.trans (LB.wchart_le L f a k)) (inf_le_right.trans (LB.wchart_le L f b k))
    let u := L.g (i PUnit.unit) (j PUnit.unit)
    change (M.g i j) ^ (N : ℤ) = res h (∏ k, (pullLE π (hπ k) u) ^ (1 : ℤ))
    rw [map_prod]
    have he (k : Fin N) : res h ((pullLE π (hπ k) u) ^ (1 : ℤ)) = M.g i j := by
      rw [zpow_one, res_pullLE]
      exact ((ChartPull.pull L π).g i j).symm
    rw [Finset.prod_congr rfl (fun k _ => he k), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zpow_natCast]

/-- The diagonal charts of the self-twist realize the single pullback factor
with exponent one plus the twist degree. -/
def ChartPull.singlePullbackTwist (t : ℤ) :
    ChartPull (LB.LinComb L (K := PUnit) (fun _ => π) (fun _ => 1 + t))
      (twist (L.pull π) (L.pull π) t) (𝟙 Y) where
  idx i := (i, i)
  le _ := le_inf le_rfl le_rfl
  g i j := by
    rw [pullLE_id]
    let M := L.pull π
    let W := M.U i ⊓ M.U j
    let u (k : PUnit) : Γ(Y, W)ˣ :=
      pullLE π (le_inf (inf_le_left.trans (LB.wchart_le L _ i k))
        (inf_le_right.trans (LB.wchart_le L _ j k))) (L.g (i k) (j k))
    have e₁ : (LB.LinComb L (K := PUnit) (fun _ => π) (fun _ => 1 + t)).g i j =
        (M.g i j) ^ (1 + t) := by
      change (∏ k, u k ^ (1 + t)) = (∏ k, u k ^ (1 : ℤ)) ^ (1 + t)
      simp only [Fintype.prod_unique, zpow_one]
    have e₂ := res_twist_g (M := M) (H := M) t (i, i) (j, j) (W := W)
      (le_inf inf_le_left inf_le_left) (le_inf inf_le_right inf_le_right)
    simp only [res_refl] at e₂
    exact e₁.trans ((zpow_one_add _ _).trans e₂.symm)

end GlobalTheory.LineBundleSections
