import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELIsomorphismGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafSectionGerms

/-! Pullback of sections under a change of trivialization. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem sec_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (σ : ∀ j, Γ(X', F ⁻¹ᵁ L.U j))
    (hσ : ∀ (y : X') j j', F y ∈ L.U j → F y ∈ L.U j' →
      gs (𝟙 X') y _ (σ j) = (gm F y (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 X') y _ (σ j')) :
    ∃ s : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (σ j) = (gw w r z j k).val * gs r z _ (s.f k) := by
  have le : ∀ j k, L'.U k ⊓ F ⁻¹ᵁ L.U j ≤ (L.pull F).U (fun _ => j) ⊓ L'.U k := fun j k y hy => ⟨mem_pull.2 hy.2, hy.1⟩
  have tr : ∀ (y : X') j j' k k', F y ∈ L.U j → F y ∈ L.U j' → y ∈ L'.U k → y ∈ L'.U k' → gw w (𝟙 X') y j k =
      gm F y _ (L.g j j') * (gm (𝟙 X') y _ (L'.g k k'))⁻¹ * gw w (𝟙 X') y j' k' := fun y j j' k k' a b c d => by
    have := hw _ (𝟙 X') y j j' k k' a b c d
    rwa [Category.id_comp] at this
  have glue : ∀ k, ∃ a : Γ(X', L'.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ a = ((gw w r z j k)⁻¹).val * gs r z _ (σ j) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(X', L'.U k ⊓ F ⁻¹ᵁ L.U j), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j,
        r z ∈ L'.U k ⊓ F ⁻¹ᵁ L.U j → gs r z _ (u j) = ((gw w r z j k)⁻¹).val * gs r z _ (σ j) :=
      ⟨fun j => ((res (le j k) (w.s (fun _ => j, k)))⁻¹).val * (X'.presheaf.map (homOfLE (inf_le_right : L'.U k ⊓ F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ L.U j)).op).hom (σ j), fun Z r z j hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans (congrArg Units.val
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le j k) hz _))))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' (fun j => L'.U k ⊓ F ⁻¹ᵁ L.U j) (L'.U k)
      (fun j => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hL (F y)
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩) u
      (fun j j' => fn_ext (V := (L'.U k ⊓ F ⁻¹ᵁ L.U j) ⊓ (L'.U k ⊓ F ⁻¹ᵁ L.U j')) fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y j hy.1, hu _ _ y j' hy.2, hσ y j j' hy.1.2 hy.2.2, tr y j j' k k hy.1.2 hy.2.2 hy.1.1 hy.1.1,
          gm_self hL' (𝟙 X') y hy.1.1, inv_one, _root_.mul_one, ← _root_.mul_assoc, ← Units.val_mul, mul_inv,
          mul_right_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨a, fun Z r z j h₁ h₂ => ?_⟩
    have hz : r z ∈ L'.U k ⊓ F ⁻¹ᵁ L.U j := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha j)).trans (hu Z r z j hz))
  choose a ha using glue
  refine ⟨⟨a, fun k k' => fn_ext fun y hy => ?_⟩, fun Z r z j k h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (F y)
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ha k _ _ y j hj hy.1, ha k' _ _ y j hj hy.2,
      tr y j j k k' hj hj hy.1 hy.2, gm_self hL F y hj, _root_.one_mul, mul_inv, inv_inv, Units.val_mul, _root_.mul_assoc]
  · show _ = _ * gs r z _ (a k)
    rw [ha k Z r z j h₁ h₂, Units.mul_inv_cancel_left]

theorem gs_compat (s : LB.Sec L) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {j j' : L.ι} (h : r z ∈ L.U j) (h' : r z ∈ L.U j') :
    gs r z _ (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z _ (s.f j') := by
  have hjj : r z ∈ L.U j ⊓ L.U j' := ⟨h, h'⟩
  refine (gs_res r z inf_le_left hjj _).symm.trans ?_
  exact (congrArg (gs r z (L.U j ⊓ L.U j')) (s.compat j j')).trans
    ((gs_mul r z _ hjj _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hjj _) (gs_res r z inf_le_right hjj _)))

/-- Pull back a section and express it in the new trivializations. -/
theorem sec_pull_down {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have p : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.app _).hom (s.f j)) = gs F y _ (s.f j) := fun y j h =>
    (gs_pull (𝟙 X') F y _ h _).trans (by rw [Category.id_comp])
  obtain ⟨s', hs'⟩ := sec_down hw hL hL' (fun j => (F.app _).hom (s.f j)) fun y j j' h h' =>
    (p y j h).trans ((gs_compat s F y h h').trans (congrArg _ (p y j' h').symm))
  exact ⟨s', fun Z r z j k h₁ h₂ => (gs_pull r F z _ h₁ _).symm.trans (hs' Z r z j k h₁ h₂)⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
