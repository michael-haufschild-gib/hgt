import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafUnitGerms

/-! Germ evaluation of products and pullbacks of line-bundle generators. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Y' Z : Scheme.{0}}

variable (L : LB X)

/-- A choice of a trivialization at each image of a given point. -/
def Good (z : Z) (J : (Z ⟶ X) → L.ι) : Prop := ∀ ψ : Z ⟶ X, ψ z ∈ L.U (J ψ)

/-- Extend a compatible partial choice of trivializations. -/
theorem exists_good (hL : L.IsLB) (z : Z) {K : Type} (ψ : K → (Z ⟶ X)) (j : K → L.ι)
    (hc : ∀ a b, ψ a = ψ b → j a = j b) (hj : ∀ k, ψ k z ∈ L.U (j k)) :
    ∃ J, Good L z J ∧ ∀ k, J (ψ k) = j k := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := exists_chart hL
  refine ⟨fun ψ' => if hk : ∃ k, ψ k = ψ' then j hk.choose else (hcov (ψ' z)).choose, ?_, ?_⟩
  · intro ψ'
    dsimp only
    split_ifs with hk
    · have hm := hj hk.choose
      rw [hk.choose_spec] at hm
      exact hm
    · exact (hcov _).choose_spec
  · intro k
    dsimp only
    rw [dif_pos ⟨k, rfl⟩]
    exact hc _ _ (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', ψ k' = ψ k))

variable {L} {K K' : Type} [Fintype K] [Fintype K']

theorem Good.mem {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (φ : K → (Y ⟶ X)) (r : Z ⟶ Y) :
    r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ φ k)

/-- Evaluate a generator in the chosen trivializations after pullback. -/
def val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (t.s (fun k => J (r ≫ φ k)))

theorem val_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    val t r z J = gm r z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl

section

variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ

theorem val_mul (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) :
    val (LB.mulGen L φ ε φ' ε' t t') r z J = val t r z J * val t' r z J := by
  simp only [val, LB.mulGen, map_mul]
  congr 1
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _

theorem val_pull (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') :
    val (LB.pullGen L φ ε t h) r z J = val t (r ≫ h) z J := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  simp only [val, LB.pullGen]
  have hm : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gm_res r z _ (hJ.mem (fun k => h ≫ φ k) r) _).trans (gm_pull r h z _ hm _)

theorem val_corr {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (r : Z ⟶ Y) : val t r z J = val t' r z J := by
  have hm : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)) :=
    ⟨hJ.mem φ r, hJ.mem φ' r⟩
  have e := h (fun k => J (r ≫ φ k)) (fun k => J (r ≫ φ' k)) (fun a b hab => by simp only [hab])
    (fun a b hab => by simp only [hab]) (fun a b hab => by simp only [hab])
  have e2 := congrArg (gm r z (LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)))) e
  exact (gm_res r z inf_le_left hm _).symm.trans (e2.trans (gm_res r z inf_le_right hm _))

end

/-- Coincidence of generators can be checked on germs in coherent charts. -/
theorem corr_of_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' hj hj' hjj'
  apply unit_ext
  intro y hy
  have hyl : y ∈ LB.wchart L φ j := hy.1
  have hyr : y ∈ LB.wchart L φ' j' := hy.2
  have hc : ∀ a b, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) a =
      Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) b → Sum.elim j j' a = Sum.elim j j' b := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.id_comp] at hab ⊢
    · exact hj a b hab
    · exact hjj' a b hab
    · exact (hjj' b a hab.symm).symm
    · exact hj' a b hab
  have hjv : ∀ k, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) k y ∈ L.U (Sum.elim j j' k) := by
    rintro (k | k)
    · exact Set.mem_iInter.1 hyl k
    · exact Set.mem_iInter.1 hyr k
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k)) (Sum.elim j j') hc hjv
  have e := h y J hJ
  rw [val_of t (𝟙 Y) y J j (fun k => hJj (Sum.inl k)), val_of t' (𝟙 Y) y J j' (fun k => hJj (Sum.inr k))] at e
  exact (gm_res (𝟙 Y) y inf_le_left hy _).trans
    (e.trans (gm_res (𝟙 Y) y inf_le_right hy _).symm)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
