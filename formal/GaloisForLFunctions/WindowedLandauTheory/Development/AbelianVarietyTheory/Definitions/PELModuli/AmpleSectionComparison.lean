import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.AmpleStalkPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELRelativeAmpleAffinePullback

/-! Section ratios in chosen trivializations and generation by polynomial coordinates. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AmpleLocal

variable {X Y Z : Scheme.{0}}

theorem gen_iff {R T : Type} [CommRing R] {D : Z.Opens} (ψ : R →+* Γ(Z, D)) (r : T → Γ(Z, D)) (φ : R → Fn Z)
    (ρ : T → Fn Z) (hψ : ∀ c, ∀ z ∈ D, gs (𝟙 Z) z D (ψ c) = φ c z) (hr : ∀ t, ∀ z ∈ D, gs (𝟙 Z) z D (r t) = ρ t z) :
    Gen D (Set.range φ ∪ Set.range ρ) ↔ Function.Surjective (MvPolynomial.eval₂Hom ψ r) := by
  constructor
  · intro H x
    obtain ⟨b, hb, e⟩ := H (fun z => gs (𝟙 Z) z D x) (mem_reg_iff.2 ⟨x, fun _ _ => rfl⟩)
    suffices ∃ p, ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨p, hp⟩ := this
      exact ⟨p, sec_ext fun z hz => (hp z hz).trans ((e z hz).symm.trans (gs_id D z hz x))⟩
    clear e
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨MvPolynomial.C c, fun z hz => by rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
      · exact ⟨MvPolynomial.X t, fun z hz => by rw [MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]⟩
    | zero => exact ⟨0, fun z hz => by rw [map_zero, map_zero]; rfl⟩
    | one => exact ⟨1, fun z hz => by rw [map_one, map_one]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, fun z hz => by rw [map_add, map_add, hp, hq]; rfl⟩
    | neg x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨-p, fun z hz => by rw [map_neg, map_neg, hp]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p * q, fun z hz => by rw [map_mul, map_mul, hp, hq]; rfl⟩
  · rintro H F ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := H x
    suffices ∃ b ∈ Subring.closure (Set.range φ ∪ Set.range ρ),
        ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨b, hb, e⟩ := this
      exact ⟨b, hb, fun z hz => (hx z hz).symm.trans (e z hz)⟩
    clear hx
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨φ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), fun z hz => by
        rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
    | add p q hp hq =>
      obtain ⟨a, ha, e⟩ := hp
      obtain ⟨b, hb, e'⟩ := hq
      exact ⟨a + b, add_mem ha hb, fun z hz => by rw [map_add, map_add, e, e']; rfl⟩
    | mul_X p t hp =>
      obtain ⟨a, ha, e⟩ := hp
      exact ⟨a * ρ t, mul_mem ha (Subring.subset_closure (Or.inr ⟨t, rfl⟩)), fun z hz => by
        rw [map_mul, map_mul, e, MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]; rfl⟩

section Link

variable {P : LB Y}

def sv (γ : Y → P.ι) (s : LB.Sec P) : Fn Y := fun y => gs (𝟙 Y) y (P.U (γ y)) (s.f (γ y))

variable {γ : Y → P.ι} (hγ : ∀ y, y ∈ P.U (γ y))
include hγ

theorem loc_sv (s : LB.Sec P) : IsLoc (nonzeroLocus s) ⊤ (sv γ s) := fun y =>
  (mem_nonzeroLocus s y).trans ⟨fun ⟨k, hk, hu⟩ => ⟨trivial, by
    rw [gs_compat s (𝟙 Y) y hk (hγ y)] at hu; exact isUnit_of_mul_isUnit_right hu⟩, fun hu => ⟨γ y, hγ y, hu.2⟩⟩

theorem ratio_iff (s t : LB.Sec P) (r : Γ(Y, nonzeroLocus s)) :
    (∀ k, (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (t.f k) =
      (Y.presheaf.map (homOfLE (inf_le_left : nonzeroLocus s ⊓ P.U k ≤ nonzeroLocus s)).op).hom r *
        (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (s.f k)) ↔
    ∀ y ∈ nonzeroLocus s, gs (𝟙 Y) y _ r = (sv γ t * inv (sv γ s)) y := by
  constructor
  · intro H y hy
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U (γ y) := ⟨hy, hγ y⟩
    have e := congrArg (gs (𝟙 Y) y _) (H (γ y))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy)).2 e.symm
  · intro H k
    refine fn_ext fun y hy => ?_
    have e := (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy.1)).1 (H y hy.1)
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U k := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_compat s (𝟙 Y) y hy.2 (hγ y),
      gs_compat t (𝟙 Y) y hy.2 (hγ y), mul_left_comm]
    exact congrArg _ e.symm

omit hγ

variable {ι : Type} {U : ι → Y.Opens} {G : ι → Fn Y} {N : ℕ} {κ : ι → P.ι} {c : Y → ι}
  (hκ : ∀ i, U i ≤ P.U (κ i)) (hc : ∀ y, y ∈ U (c y))
  (hg : ∀ i y, y ∈ U i → (gm (𝟙 Y) y _ (P.g (κ i) (κ (c y)))).val = G i y ^ N)
include hκ hc hg

theorem sc_sv (s : LB.Sec P) : Sc U G ⊤ N (sv (fun y => κ (c y)) s) := fun i =>
  reg_congr (reg_mono (inf_le_right.trans (hκ i)) (reg_gs (𝟙 Y) _ (s.f (κ i)))) fun y hy => by
    rw [gs_compat s (𝟙 Y) y (hκ i hy.2) (hκ _ (hc y)), hg i y hy.2]
    rfl

theorem exists_sv (hP : P.IsLB) {σ : Fn Y} (hσ : Sc U G ⊤ N σ) : ∃ s : LB.Sec P, sv (fun y => κ (c y)) s = σ := by
  have : ∀ k, (fun y => (gm (𝟙 Y) y _ (P.g k (κ (c y)))).val * σ y) ∈ Reg (P.U k) := fun k =>
    reg_glue fun z hz => ⟨P.U k ⊓ U (c z), ⟨hz, hc z⟩, reg_congr
      (mul_mem (reg_mono (inf_le_inf_left _ (hκ _)) (reg_gs (𝟙 Y) _ (P.g k (κ (c z))).val))
        (reg_mono (le_inf le_top inf_le_right) (hσ (c z)))) fun y hy => by
      show gs (𝟙 Y) y _ (P.g k (κ (c z))).val * (G (c z) y ^ N * σ y) = _
      rw [gs_unit (𝟙 Y) y (P.U k ⊓ P.U (κ (c z))) ⟨hy.1, hκ _ hy.2⟩, ← hg _ y hy.2, ← mul_assoc, ← Units.val_mul,
        gm_cocycle hP (𝟙 Y) y hy.1 (hκ _ hy.2) (hκ _ (hc y))]⟩
  choose f hf using fun k => mem_reg_iff.1 (this k)
  refine ⟨⟨f, fun k k' => fn_ext fun y hy => ?_⟩, funext fun y => ?_⟩
  · have hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k' := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm, hf k y hy.1, hf k' y hy.2,
      ← mul_assoc, ← Units.val_mul, gm_cocycle hP (𝟙 Y) y hy.1 hy.2 (hκ _ (hc y))]
  · refine (hf _ y (hκ _ (hc y))).trans ?_
    rw [gm_self hP (𝟙 Y) y (hκ _ (hc y)), Units.val_one, one_mul]

end Link

theorem Pack.mono {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {W : Z.Opens} {S S' : Set (Fn Z)} (H : Pack U G W S)
    (hS : ∀ x ∈ S, x ∈ Subring.closure S') : Pack U G W S' := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  refine ⟨N, hN, M, s, D, hs, hD, cov, aff, fun j => (gen j).mono ?_⟩
  rintro x (hx | hx)
  · exact ⟨x, Subring.closure_mono Set.subset_union_left (hS x hx), fun _ _ => rfl⟩
  · exact ⟨x, Subring.subset_closure (Or.inr hx), fun _ _ => rfl⟩

theorem cst_mem {B V : Scheme.{0}} [IsAffine B] (a : Γ(B, ⊤)) (b : V ⟶ B) [IsOpenImmersion b]
    (hb : b ''ᵁ ⊤ = B.basicOpen a) (q : Y ⟶ V) (h : Y ⟶ Z) (p : Z ⟶ B) (e : h ≫ p = q ≫ b) (c : Γ(V, ⊤)) :
    cst q c ∈ Subring.closure (pb h '' insert (inv (cst p a)) (Set.range (cst p))) := by
  obtain ⟨F, hF⟩ := pb_surj b (cst (𝟙 V) c)
  have h₁ : F ∈ Reg (B.basicOpen a) := hb ▸ reg_push b (hF ▸ reg_cst _ c)
  have h₂ : Gen ⊤ (Set.range (cst (𝟙 B))) := fun F ⟨x, hx⟩ =>
    ⟨cst (𝟙 B) x, Subring.subset_closure ⟨x, rfl⟩, fun z hz => (hx z hz).symm⟩
  obtain ⟨β, hβ, eβ⟩ := Gen.loc (isAffineOpen_top B) (loc_cst a) (reg_cst _ a) h₂ F h₁
  have : cst q c = pb h (pb p β) := by
    rw [← pb_comp, e, ← Category.comp_id q, ← pb_cst, ← hF, ← pb_comp, Category.comp_id q]
    funext y
    rw [pb_apply, pb_apply, eβ]
    rw [← hb]
    exact ⟨q y, trivial, rfl⟩
  rw [this, ← RingHom.map_closure]
  refine ⟨_, ?_, rfl⟩
  have := Subring.mem_map.2 ⟨β, hβ, (rfl : pb p β = _)⟩
  rw [RingHom.map_closure] at this
  simp only [Set.image_insert_eq, ← Set.range_comp', pb_inv, pb_cst, Category.comp_id] at this
  exact this

theorem gm_const (L : LB X) (j : Y ⟶ X) (N : ℕ) (y : Y) (i i' : L.ι) (hi : j y ∈ L.U i) (hi' : j y ∈ L.U i') :
    (gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin N) (fun _ => j) (fun _ => 1)).g (fun _ => i) (fun _ => i'))).val =
      (gm j y _ (L.g i i')).val ^ N := by
  refine (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y _ _ (Set.mem_iInter.2 fun _ => hi)
    (Set.mem_iInter.2 fun _ => hi'))).trans ?_
  simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val,
    Category.id_comp]

end GlobalTheory.AmpleLocal
