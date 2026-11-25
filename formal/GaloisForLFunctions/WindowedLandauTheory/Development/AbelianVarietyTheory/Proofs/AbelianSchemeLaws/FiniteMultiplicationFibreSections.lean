import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELSectionValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELPolarizations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGenerators

/-! The multiplication pullback law turns the nonvanishing opens of ample sections
into principal opens on every fibre of the multiplication morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.MulFinite

private theorem isUnit_gs {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens)
    (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

private theorem gs_pow {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens)
    (h : r z ∈ U) (a : Γ(Y, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by
  simp only [gs_eq r z U h, map_pow]

private theorem cancel_power_transition {B : Type} [CommRing B] (g u : Bˣ) (x : B) (e n : ℕ) :
    ((g ^ n).val * x) ^ e * ((g ^ e * u)⁻¹).val ^ n = x ^ e * (u⁻¹).val ^ n := by
  have h : (g ^ n) ^ e * ((g ^ e * u)⁻¹) ^ n = (u⁻¹) ^ n := by
    rw [mul_inv, mul_pow, ← mul_assoc, inv_pow, ← pow_mul, ← pow_mul, mul_comm e n,
      mul_inv_cancel, one_mul]
  have hv : (g ^ n).val ^ e * ((g ^ e * u)⁻¹).val ^ n = (u⁻¹).val ^ n := congrArg Units.val h
  rw [mul_pow, mul_comm ((g ^ n).val ^ e) (x ^ e), mul_assoc, hv]

/-- Raising a power-section to the exponent in the pullback law and dividing by the
generator gives a regular function when the image lies in one target chart. -/
theorem exists_basicOpen_preimage_of_power_section {X W Z : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin n) (fun _ => w) (fun _ => 1)))
    (m : X ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1])) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : L.ι) (h₀ : ∀ z, m (w (r z)) ∈ L.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let P := LB.LinComb L (K := Fin n) (fun _ => w) (fun _ => 1)
  let Q := LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1]
  let c (j : L.ι) : P.ι := fun _ => j
  let d (j : L.ι) : Q.ι := ![j, j₀]
  let V : L.ι → Z.Opens := fun j => (r ≫ w) ⁻¹ᵁ L.U j
  have h₁ (j : L.ι) : V j ≤ r ⁻¹ᵁ P.U (c j) :=
    fun _ hz => Set.mem_iInter.2 fun _ => hz
  have h₂ (j : L.ι) : V j ≤ (r ≫ w) ⁻¹ᵁ Q.U (d j) :=
    fun j' hz => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hz
      · exact h₀ j'
  let u (j : L.ι) : Γ(Z, V j) :=
    (r.appLE _ _ (h₁ j)).hom (s.f (c j)) ^ e *
      ((r ≫ w).appLE _ _ (h₂ j)).hom ((α.s (d j))⁻¹).val ^ n
  have hu (j : L.ι) (z : Z) (hz : z ∈ V j) :
      gs (𝟙 Z) z (V j) (u j) =
        gs r z (P.U (c j)) (s.f (c j)) ^ e *
        ((gm (r ≫ w) z (Q.U (d j)) (α.s (d j)))⁻¹).val ^ n := by
    change gs (𝟙 Z) z (V j)
      ((r.appLE _ _ (h₁ j)).hom (s.f (c j)) ^ e *
        ((r ≫ w).appLE _ _ (h₂ j)).hom ((α.s (d j))⁻¹).val ^ n) = _
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    · have h := gs_appLE r _ _ (h₁ j) (𝟙 Z) z hz (s.f (c j))
      rw [Category.id_comp] at h
      exact congrArg (· ^ e) h
    · have h := gs_appLE (r ≫ w) _ _ (h₂ j) (𝟙 Z) z hz ((α.s (d j))⁻¹).val
      rw [Category.id_comp] at h
      refine congrArg (· ^ n) (h.trans ?_)
      exact (gs_unit (r ≫ w) z _ (h₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  have hchange (j k : L.ι) (z : Z) (hj : z ∈ V j) (hk : z ∈ V k) :
      gs (𝟙 Z) z (V j) (u j) = gs (𝟙 Z) z (V k) (u k) := by
    have hg : gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) = 1 :=
      gm_self hL _ z (h₀ z)
    have hN : gm r z _ (P.g (c j) (c k)) = gm (r ≫ w) z _ (L.g j k) ^ n := by
      refine (gm_linComb L _ _ r z _ _ (h₁ j hj) (h₁ k hk)).trans ?_
      simp only [c, zpow_one]
      let g := gm (r ≫ w) z (L.U j ⊓ L.U k) (L.g j k)
      change (∏ _ : Fin n, g) = g ^ n
      exact (Finset.prod_const g).trans (congrArg (fun p => g ^ p)
        (Finset.card_univ.trans (Fintype.card_fin n)))
    have hE : trF (L := L) (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1] (r ≫ w) z (d j) (d k) =
        gm (r ≫ w) z _ (L.g j k) ^ e := by
      rw [trF, Fin.prod_univ_two]
      change gm ((r ≫ w) ≫ 𝟙 X) z _ (L.g j k) ^ (e : ℤ) *
        gm ((r ≫ w) ≫ m) z _ (L.g j₀ j₀) ^ (-1 : ℤ) = _
      rw [hg, Category.comp_id]
      simp
    have hs := (gs_compat s r z (h₁ j hj) (h₁ k hk)).trans
      (congrArg (fun t : (Z.presheaf.stalk z)ˣ => t.val * gs r z (P.U (c k)) (s.f (c k))) hN)
    have ht := (gen_trans hα (r ≫ w) z (h₂ j hj) (h₂ k hk)).trans
      (congrArg (· * gm (r ≫ w) z (Q.U (d k)) (α.s (d k))) hE)
    exact (hu j z hj).trans
      ((congrArg₂ (fun (x : Z.presheaf.stalk z) (v : (Z.presheaf.stalk z)ˣ) =>
        x ^ e * (v⁻¹).val ^ n) hs ht).trans
        ((cancel_power_transition _ _ _ _ _).trans (hu k z hk).symm))
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top) hcov u
    (fun j k => fn_ext (V := V j ⊓ V k) fun z hz =>
      (gs_res (𝟙 Z) z inf_le_left hz _).trans
        ((hchange j k z hz.1 hz.2).trans (gs_res (𝟙 Z) z inf_le_right hz _).symm))
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
  have hval : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have hunit : z ∈ Z.basicOpen a ↔
      IsUnit (gs r z (P.U (c j)) (s.f (c j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [hval, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine hunit.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨c j, (isUnit_gs r z _ (h₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ P.U k := W.basicOpen_le _ hk
    exact (gs_compat s r z (h₁ j hj) hk').symm ▸
      (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

end GlobalTheory.MulFinite
