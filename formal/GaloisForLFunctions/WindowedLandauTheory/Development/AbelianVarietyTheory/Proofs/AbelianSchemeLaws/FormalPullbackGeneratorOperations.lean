import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorValues

/-! Generators of tensor products of pullbacks under multiplication and inversion. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}} {L : LB X} {I J : Type} [Fintype I] [Fintype J]

section

variable {f : I → (Y ⟶ X)} {e : I → ℤ} {g : J → (Y ⟶ X)} {d : J → ℤ}
  {s : LB.Gen (LB.LinComb L f e)} {t : LB.Gen (LB.LinComb L g d)}

theorem val_inv (r : Z ⟶ Y) (z : Z) (j : (Z ⟶ X) → L.ι) :
    val (LB.invGen L f e s) r z j = (val s r z j)⁻¹ :=
  map_inv _ _

theorem invGen_isGen (hs : s.IsGen) : (LB.invGen L f e s).IsGen := by
  apply isGen_of_gm
  intro y i j hi hj
  have hi' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L f i := by simpa using hi
  have hj' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L f j := by simpa using hj
  have htr : trF f (fun k => -e k) (𝟙 Y) y i j = (trF f e (𝟙 Y) y i j)⁻¹ := by
    simp only [trF, zpow_neg, Finset.prod_inv_distrib]
  exact (map_inv (gm (𝟙 Y) y (LB.wchart L f i)) (s.s i)).trans
    ((congrArg (·⁻¹) (gen_trans hs (𝟙 Y) y hi' hj')).trans
      ((mul_inv _ _).trans (congrArg₂ (· * ·) htr.symm
        (map_inv (gm (𝟙 Y) y (LB.wchart L f j)) (s.s j)).symm)))

theorem mulGen_isGen (hs : s.IsGen) (ht : t.IsGen) : (LB.mulGen L f e g d s t).IsGen := by
  apply isGen_of_gm
  intro y i j hi hj
  have factor (k : (I ⊕ J) → L.ι) (hk : y ∈ LB.wchart L (Sum.elim f g) k) :
      gm (𝟙 Y) y (LB.wchart L (Sum.elim f g) k) ((LB.mulGen L f e g d s t).s k) =
        gm (𝟙 Y) y (LB.wchart L f (k ∘ Sum.inl)) (s.s (k ∘ Sum.inl)) *
          gm (𝟙 Y) y (LB.wchart L g (k ∘ Sum.inr)) (t.s (k ∘ Sum.inr)) := by
    have hk' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (Sum.elim f g) k := by simpa using hk
    have h₁ : LB.wchart L (Sum.elim f g) k ≤ LB.wchart L f (k ∘ Sum.inl) :=
      fun z hz => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hz (Sum.inl a)
    have h₂ : LB.wchart L (Sum.elim f g) k ≤ LB.wchart L g (k ∘ Sum.inr) :=
      fun z hz => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hz (Sum.inr a)
    exact (map_mul (gm (𝟙 Y) y (LB.wchart L (Sum.elim f g) k))
      (res h₁ (s.s (k ∘ Sum.inl))) (res h₂ (t.s (k ∘ Sum.inr)))).trans
        (congrArg₂ (· * ·) (gm_res _ _ h₁ hk' _) (gm_res _ _ h₂ hk' _))
  have hl (k : (I ⊕ J) → L.ι) (hk : y ∈ LB.wchart L (Sum.elim f g) k) :
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L f (k ∘ Sum.inl) := by
    change y ∈ LB.wchart L f (k ∘ Sum.inl)
    exact Set.mem_iInter.2 fun a => Set.mem_iInter.1 hk (Sum.inl a)
  have hr (k : (I ⊕ J) → L.ι) (hk : y ∈ LB.wchart L (Sum.elim f g) k) :
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L g (k ∘ Sum.inr) := by
    change y ∈ LB.wchart L g (k ∘ Sum.inr)
    exact Set.mem_iInter.2 fun a => Set.mem_iInter.1 hk (Sum.inr a)
  have htr : trF (Sum.elim f g) (Sum.elim e d) (𝟙 Y) y i j =
      trF f e (𝟙 Y) y (i ∘ Sum.inl) (j ∘ Sum.inl) *
        trF g d (𝟙 Y) y (i ∘ Sum.inr) (j ∘ Sum.inr) := Fintype.prod_sum_type _
  exact (factor i hi).trans ((congrArg₂ (· * ·) (gen_trans hs _ _ (hl i hi) (hl j hj))
    (gen_trans ht _ _ (hr i hi) (hr j hj))).trans
      ((mul_mul_mul_comm _ _ _ _).trans (congrArg₂ (· * ·) htr.symm (factor j hj).symm)))

end

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
