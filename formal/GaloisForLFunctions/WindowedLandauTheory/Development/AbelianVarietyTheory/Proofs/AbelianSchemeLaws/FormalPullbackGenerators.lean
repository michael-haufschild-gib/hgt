import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGeneratorValues

/-! Changing a formal expression for a tensor product of pullbacks preserves its generators. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}} {L : LB X} {I J : Type} [Fintype I] [Fintype J]

/-- The two formal products give the same exponent sum at each morphism. -/
def FormEq (f : I → (Y ⟶ X)) (e : I → ℤ) (g : J → (Y ⟶ X)) (d : J → ℤ) : Prop :=
  ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ i, h (f i) ^ e i = ∏ j, h (g j) ^ d j

theorem FormEq.trF {f : I → (Y ⟶ X)} {e : I → ℤ} {g : J → (Y ⟶ X)} {d : J → ℤ}
    (h : FormEq f e g d) (r : Z ⟶ Y) (z : Z) (a b : (Y ⟶ X) → L.ι) :
    trF f e r z (a ∘ f) (b ∘ f) = trF g d r z (a ∘ g) (b ∘ g) :=
  h _ fun ψ => gm (r ≫ ψ) z (L.U (a ψ) ⊓ L.U (b ψ)) (L.g (a ψ) (b ψ))

theorem trF_trans (hL : L.IsLB) (f : I → (Y ⟶ X)) (e : I → ℤ) (r : Z ⟶ Y) (z : Z)
    {a b c : I → L.ι} (ha : r z ∈ LB.wchart L f a) (hb : r z ∈ LB.wchart L f b)
    (hc : r z ∈ LB.wchart L f c) :
    trF f e r z a b * trF f e r z b c = trF f e r z a c := by
  unfold trF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow]
  congr 1
  have hm : (r ≫ f i) z ∈ L.U (a i) ⊓ L.U (b i) ⊓ L.U (c i) :=
    ⟨⟨Set.mem_iInter.1 ha i, Set.mem_iInter.1 hb i⟩, Set.mem_iInter.1 hc i⟩
  have h := congrArg (gm (r ≫ f i) z _) (hL.cocycle (a i) (b i) (c i))
  rw [map_mul] at h
  exact (congrArg₂ (· * ·) (gm_res (r ≫ f i) z _ hm _) (gm_res (r ≫ f i) z _ hm _)).symm.trans
    (h.trans (gm_res (r ≫ f i) z _ hm _))

/-- Reexpress a generator in another presentation with the same formal factors. -/
theorem exists_gen_of_formEq (hL : L.IsLB)
    {f : I → (Y ⟶ X)} {e : I → ℤ} {g : J → (Y ⟶ X)} {d : J → ℤ}
    (h : FormEq f e g d) (s : LB.Gen (LB.LinComb L f e)) (hs : s.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L g d), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (a : (Z ⟶ X) → L.ι),
        Good L z a → val t r z a = val s r z a := by
  let W (b : J → L.ι) (a : (Y ⟶ X) → L.ι) :=
    LB.wchart L g b ⊓ LB.wchart L g (a ∘ g) ⊓ LB.wchart L f (a ∘ f)
  let u (b : J → L.ι) (a : (Y ⟶ X) → L.ι) : Γ(Y, W b a)ˣ :=
    res inf_le_left ((LB.LinComb L g d).g b (a ∘ g)) * res inf_le_right (s.s (a ∘ f))
  have hu {Z : Scheme.{0}} (b : J → L.ι) (a : (Y ⟶ X) → L.ι) (r : Z ⟶ Y) (z : Z)
      (hz : r z ∈ W b a) :
      gm r z (W b a) (u b a) =
        trF g d r z b (a ∘ g) * gm r z (LB.wchart L f (a ∘ f)) (s.s (a ∘ f)) := by
    change gm r z (W b a)
      (res inf_le_left ((LB.LinComb L g d).g b (a ∘ g)) *
        res inf_le_right (s.s (a ∘ f))) = _
    exact (map_mul (gm r z (W b a)) _ _).trans
      (congrArg₂ (· * ·)
        ((gm_res r z inf_le_left hz _).trans (gm_linComb L g d r z b (a ∘ g) hz.1.1 hz.1.2))
        (gm_res r z inf_le_right hz _))
  have cover (y : Y) : ∃ a : (Y ⟶ X) → L.ι, ∀ q, q y ∈ L.U (a q) := by
    choose a ha using fun q : Y ⟶ X => exists_chart hL (q y)
    exact ⟨a, ha⟩
  have glue (b : J → L.ι) : ∃ v : Γ(Y, LB.wchart L g b)ˣ,
      ∀ a, res (inf_le_left.trans inf_le_left : W b a ≤ LB.wchart L g b) v = u b a := by
    apply glue_unit _ _ _
    · intro y hy
      obtain ⟨a, ha⟩ := cover y
      exact Opens.mem_iSup.2 ⟨a, ⟨hy, Set.mem_iInter.2 fun i => ha _⟩, Set.mem_iInter.2 fun i => ha _⟩
    · intro a c y hy
      have ha : (𝟙 Y : Y ⟶ Y) y ∈ W b a := by
        change y ∈ W b a
        exact hy.1
      have hc : (𝟙 Y : Y ⟶ Y) y ∈ W b c := by
        change y ∈ W b c
        exact hy.2
      rw [hu b a (𝟙 Y) y ha, hu b c (𝟙 Y) y hc, gen_trans hs (𝟙 Y) y ha.2 hc.2,
        h.trF (𝟙 Y) y a c, ← mul_assoc, trF_trans hL g d (𝟙 Y) y ha.1.1 ha.1.2 hc.1.2]
  choose v hv using glue
  have eval {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (b : J → L.ι) (a : (Y ⟶ X) → L.ι) (hz : r z ∈ W b a) :
      gm r z (LB.wchart L g b) (v b) =
        trF g d r z b (a ∘ g) * gm r z (LB.wchart L f (a ∘ f)) (s.s (a ∘ f)) := by
    rw [← gm_res r z (inf_le_left.trans inf_le_left : W b a ≤ LB.wchart L g b) hz, hv b a]
    exact hu b a r z hz
  refine ⟨⟨v⟩, isGen_of_gm (fun y b c hb hc => ?_), fun Z r z a ha => ?_⟩
  · obtain ⟨a, ha⟩ := cover y
    have hg : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L g (a ∘ g) := Set.mem_iInter.2 fun i => by simpa using ha (g i)
    have hf : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L f (a ∘ f) := Set.mem_iInter.2 fun i => by simpa using ha (f i)
    have hb' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L g b := by simpa using hb
    have hc' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L g c := by simpa using hc
    show gm (𝟙 Y) y _ (v b) = _ * gm (𝟙 Y) y _ (v c)
    rw [eval (𝟙 Y) y b a ⟨⟨hb', hg⟩, hf⟩, eval (𝟙 Y) y c a ⟨⟨hc', hg⟩, hf⟩,
      ← mul_assoc, trF_trans hL g d (𝟙 Y) y hb' hc' hg]
  · let b : (Y ⟶ X) → L.ι := fun q => a (r ≫ q)
    have hg : r z ∈ LB.wchart L g (b ∘ g) := ha.mem g r
    have hf : r z ∈ LB.wchart L f (b ∘ f) := ha.mem f r
    change gm r z _ (v (b ∘ g)) = gm r z _ (s.s (b ∘ f))
    rw [eval r z (b ∘ g) b ⟨⟨hg, hg⟩, hf⟩,
      mul_eq_left.mp (trF_trans hL g d r z hg hg hg), one_mul]
    rfl

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
