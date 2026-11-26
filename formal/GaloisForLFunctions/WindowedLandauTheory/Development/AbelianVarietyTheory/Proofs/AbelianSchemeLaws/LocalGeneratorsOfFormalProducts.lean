import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGeneratorOperations
import Mathlib.AlgebraicGeometry.Restrict

/-! Local generation of formal products is preserved by division and restriction. -/

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw.Cube

variable {X Y B : Scheme.{0}} {L : LB X}
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- The formal product is trivial over a neighbourhood of each base point. -/
def LocallyGenerated (L : LB X) (p : Y ⟶ B) (f : I → (Y ⟶ X)) (d : I → ℤ) : Prop :=
  ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∃ s : (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ f i) d).Gen,
    s.IsGen

/-- Local generators can also be expressed using the ordinary line-bundle pullbacks. -/
theorem locallyGenerated_iff (hL : L.IsLB) (p : Y ⟶ B) (f : I → (Y ⟶ X)) (d : I → ℤ) :
    LocallyGenerated L p f d ↔ ∀ b : B, ∃ U : B.Opens, b ∈ U ∧
      ∃ s : ((LB.LinComb L f d).pull (p ⁻¹ᵁ U).ι).Gen, s.IsGen := by
  simp only [LocallyGenerated, trivial_pull_linComb L hL]

/-- Cancelled factors give a local generator on the entire base. -/
theorem locallyGenerated_of_cancellation (hL : L.IsLB) (p : Y ⟶ B)
    (f : I → (Y ⟶ X)) (d : I → ℤ)
    (h : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (f i) ^ d i = 1) :
    LocallyGenerated L p f d := by
  intro b
  let r := (p ⁻¹ᵁ (⊤ : B.Opens)).ι
  obtain ⟨s, hs, -⟩ := exists_gen_of_cancellation L hL (fun i => r ≫ f i) d
    (fun U _ k => h U (fun q => k (r ≫ q)))
  exact ⟨⊤, trivial, s, hs⟩

private theorem restrict_generator {p : Y ⟶ B} {V U : B.Opens} (hVU : V ≤ U)
    {f : I → (Y ⟶ X)} {d : I → ℤ}
    {s : (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ f i) d).Gen} (hs : s.IsGen) :
    ∃ t : (LB.LinComb L (fun i => (p ⁻¹ᵁ V).ι ≫ f i) d).Gen, t.IsGen := by
  let r := Y.homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx => hVU hx)
  have h (i : I) : r ≫ (p ⁻¹ᵁ U).ι ≫ f i = (p ⁻¹ᵁ V).ι ≫ f i := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have h' : ∃ t : (LB.LinComb L (fun i => r ≫ (p ⁻¹ᵁ U).ι ≫ f i) d).Gen, t.IsGen :=
    ⟨_, hs.pullGen _ _ r⟩
  rwa [funext h] at h'

/-- Divide local generators after restricting to a common base open, then express
their quotient in the specified presentation. -/
theorem LocallyGenerated.div (hL : L.IsLB) {p : Y ⟶ B} {f : I → (Y ⟶ X)} {d : I → ℤ}
    {g : J → (Y ⟶ X)} {e : J → ℤ} {b : K → (Y ⟶ X)} {c : K → ℤ}
    (h₁ : LocallyGenerated L p f d) (h₂ : LocallyGenerated L p g e)
    (he : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U),
      (∏ i, k (f i) ^ d i) * (∏ j, k (g j) ^ e j)⁻¹ = ∏ i, k (b i) ^ c i) :
    LocallyGenerated L p b c := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := h₁ x
  obtain ⟨V, hxV, t, ht⟩ := h₂ x
  let W := U ⊓ V
  let r := (p ⁻¹ᵁ W).ι
  obtain ⟨s', hs'⟩ := restrict_generator (V := W) inf_le_left hs
  obtain ⟨t', ht'⟩ := restrict_generator (V := W) inf_le_right ht
  obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL (g := fun i => r ≫ b i) (d := c)
    (fun U _ k => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact he U fun q => k (r ≫ q)) _ (mulGen_isGen hs' (invGen_isGen ht'))
  exact ⟨W, ⟨hxU, hxV⟩, u, hu⟩

end GlobalTheory.AbLaw.Cube
