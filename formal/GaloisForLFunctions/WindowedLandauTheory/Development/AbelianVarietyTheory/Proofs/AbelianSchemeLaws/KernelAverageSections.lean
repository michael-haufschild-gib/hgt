import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.KernelInvariantSectionDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback

/-! Averaging over the deck group splits pullback of functions when the
group order is invertible. The splitting commutes with restrictions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open GlobalTheory.LineBundleSections
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlatDescent

variable {Y : Scheme.{0}} {G : Type} [Group G] [Fintype G]
  {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (hτ : ∀ g, τ g ≫ q = q)
  (hmul : ∀ a b, τ a ≫ τ b = τ (a * b)) (hD : Descends q τ)

include hτ in
omit [Group G] [Fintype G] in
private theorem le_translation (g : G) (U : Y.Opens) : q ⁻¹ᵁ U ≤ τ g ⁻¹ᵁ (q ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hτ]

private def translationPull (g : G) (U : Y.Opens) : Γ(Y, q ⁻¹ᵁ U) →+* Γ(Y, q ⁻¹ᵁ U) :=
  ((τ g).appLE _ _ (le_translation hτ g U)).hom

private theorem appLE_eq_of_eq {f f' : Y ⟶ Y} (e : f = f') {U V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ f' ⁻¹ᵁ U) (b : Γ(Y, U)) :
    f.appLE U V h b = f'.appLE U V h' b := by
  subst f'
  rfl

include hmul in
omit [Fintype G] in
private theorem translationPull_mul (a b : G) (U : Y.Opens) (u : Γ(Y, q ⁻¹ᵁ U)) :
    translationPull hτ a U (translationPull hτ b U u) = translationPull hτ (a * b) U u := by
  let V := q ⁻¹ᵁ U
  let ha := le_translation hτ a U
  let hb := le_translation hτ b U
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE (τ a) (τ b) V V V hb ha) u).trans
    (appLE_eq_of_eq (hmul a b) _ _ u)

omit [Group G] [Fintype G] in
private theorem translationPull_pull (a : G) (U : Y.Opens) (u : Γ(Y, U)) :
    translationPull hτ a U (q.app U u) = q.app U u := by
  let V := q ⁻¹ᵁ U
  have e : q.appLE U V le_rfl = q.app U := (q.app_eq_appLE).symm
  rw [← e]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE (τ a) q U V V
    le_rfl (le_translation hτ a U)) u).trans (appLE_eq_of_eq (hτ a) _ _ u)

omit [Group G] [Fintype G] in
private theorem translationPull_res (a : G) {U V : Y.Opens} (i : V ≤ U) (b : Γ(Y, q ⁻¹ᵁ U)) :
    resG Y (q.preimage_mono i) (translationPull hτ a U b) =
      translationPull hτ a V (resG Y (q.preimage_mono i) b) :=
  (resG_appLE (le_translation hτ a U) (q.preimage_mono i) b).trans
    (appLE_resG (le_translation hτ a V) (q.preimage_mono i) b).symm

include hmul hD in
private theorem exists_trace (U : Y.Opens) (b : Γ(Y, q ⁻¹ᵁ U)) :
    ∃ u : Γ(Y, U), q.app U u = ∑ g, translationPull hτ g U b := by
  let z : Γ(Y, q ⁻¹ᵁ U) := ∑ g, translationPull hτ g U b
  refine hD.2 U z fun a y hy => ?_
  have hz : translationPull hτ a U z = z := by
    dsimp only [z]
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => translationPull_mul hτ hmul a b U _
  have he := gs_appLE (τ a) (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) (le_translation hτ a U) (𝟙 Y) y hy z
  rw [Category.id_comp] at he
  exact he.symm.trans (congrArg (gs (𝟙 Y) y (q ⁻¹ᵁ U)) hz)

private def trace (U : Y.Opens) (b : Γ(Y, q ⁻¹ᵁ U)) : Γ(Y, U) :=
  (exists_trace hτ hmul hD U b).choose

private theorem pull_trace (U : Y.Opens) (b : Γ(Y, q ⁻¹ᵁ U)) :
    q.app U (trace hτ hmul hD U b) = ∑ g, translationPull hτ g U b :=
  (exists_trace hτ hmul hD U b).choose_spec

private theorem trace_add (U : Y.Opens) (x y : Γ(Y, q ⁻¹ᵁ U)) :
    trace hτ hmul hD U (x + y) = trace hτ hmul hD U x + trace hτ hmul hD U y := by
  apply hD.1 U
  simp only [pull_trace, map_add, Finset.sum_add_distrib]

private theorem trace_mul (U : Y.Opens) (a : Γ(Y, U)) (b : Γ(Y, q ⁻¹ᵁ U)) :
    trace hτ hmul hD U (q.app U a * b) = a * trace hτ hmul hD U b := by
  apply hD.1 U
  simp only [pull_trace, map_mul, translationPull_pull, Finset.mul_sum]

private theorem trace_pull (U : Y.Opens) (a : Γ(Y, U)) :
    trace hτ hmul hD U (q.app U a) = (Fintype.card G : Γ(Y, U)) * a := by
  apply hD.1 U
  simp only [pull_trace, translationPull_pull, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, map_mul, map_natCast]

private theorem trace_res {U V : Y.Opens} (i : V ≤ U) (b : Γ(Y, q ⁻¹ᵁ U)) :
    resG Y i (trace hτ hmul hD U b) = trace hτ hmul hD V (resG Y (q.preimage_mono i) b) := by
  apply hD.1 V
  have e (a : Γ(Y, U)) : q.app V (resG Y i a) = resG Y (q.preimage_mono i) (q.app U a) :=
    ConcreteCategory.congr_hom (q.naturality (homOfLE i).op) a
  simp only [e, pull_trace, map_sum]
  exact Finset.sum_congr rfl fun a _ => translationPull_res hτ a i b

variable (u : Γ(Y, ⊤)ˣ)

/-- The normalized sum of the deck translations, descended to the target. -/
def averageSections (U : Y.Opens) :
    letI : Module Γ(Y, U) Γ(Y, q ⁻¹ᵁ U) := Module.compHom _ (q.app U).hom
    Γ(Y, q ⁻¹ᵁ U) →ₗ[Γ(Y, U)] Γ(Y, U) :=
  letI : Module Γ(Y, U) Γ(Y, q ⁻¹ᵁ U) := Module.compHom _ (q.app U).hom
  { toFun := fun b => resG Y le_top (u⁻¹ : Γ(Y, ⊤)ˣ).val * trace hτ hmul hD U b
    map_add' := fun x y => by rw [trace_add, mul_add]
    map_smul' := fun a b => by
      change _ * trace hτ hmul hD U (q.app U a * b) = a * (_ * trace hτ hmul hD U b)
      rw [trace_mul, mul_left_comm] }

theorem averageSections_res {U V : Y.Opens} (i : V ≤ U) (b : Γ(Y, q ⁻¹ᵁ U)) :
    resG Y i (averageSections hτ hmul hD u U b) =
      averageSections hτ hmul hD u V (resG Y (q.preimage_mono i) b) := by
  change resG Y i (resG Y le_top (u⁻¹ : Γ(Y, ⊤)ˣ).val * trace hτ hmul hD U b) =
    resG Y le_top (u⁻¹ : Γ(Y, ⊤)ˣ).val * trace hτ hmul hD V (resG Y (q.preimage_mono i) b)
  rw [map_mul, resG_resG, trace_res]

theorem averageSections_pull (hu : u.val = (Fintype.card G : Γ(Y, ⊤))) (U : Y.Opens) (a : Γ(Y, U)) :
    averageSections hτ hmul hD u U (q.app U a) = a := by
  change resG Y le_top (u⁻¹ : Γ(Y, ⊤)ˣ).val * trace hτ hmul hD U (q.app U a) = a
  have h := congrArg (resG Y (le_top : U ≤ ⊤)) (Units.inv_mul u)
  rw [map_mul, hu, map_natCast, map_one] at h
  rw [trace_pull, ← mul_assoc, h, one_mul]

end GlobalTheory.FlatDescent
