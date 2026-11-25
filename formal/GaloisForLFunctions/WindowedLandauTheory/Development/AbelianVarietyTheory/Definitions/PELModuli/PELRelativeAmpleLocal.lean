import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.AmpleSectionComparison

/-! Relative ampleness descends from an open cover of the base. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AmpleLocal

variable {X Y Z : Scheme.{0}}

theorem pack_of_relAmple {S : Scheme.{0}} (A : Over S) (L : LB A.left) (U : S.Opens) (hU : IsAffineOpen U)
    (U₀ : S.Opens) (H : RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)) (a : Γ(U.toScheme, ⊤))
    (ha : U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀) (c : (A.hom ⁻¹ᵁ U).toScheme → L.ι)
    (hc : ∀ z, (A.hom ⁻¹ᵁ U).ι z ∈ L.U (c z)) :
    ∃ W, IsLoc W ⊤ (cst (A.hom ∣_ U) a) ∧ Pack (fun i => (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i)
      (fun i z => (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val) W
      (insert (inv (cst (A.hom ∣_ U) a)) (Set.range (cst (A.hom ∣_ U)))) := by
  have : IsAffine U := hU
  have hle : U.ι ''ᵁ U.toScheme.basicOpen a ≤ U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ha hx
  let V : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ (U.ι ''ᵁ U.toScheme.basicOpen a)
  have hV : IsAffineOpen V := (((isAffineOpen_top U.toScheme).basicOpen a).image_of_isOpenImmersion
    U.ι).preimage_of_isOpenImmersion U₀.ι (by rwa [Scheme.Opens.opensRange_ι])
  obtain ⟨b, hb⟩ : ∃ b : V.toScheme ⟶ U.toScheme, b ≫ U.ι = V.ι ≫ U₀.ι :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ U₀.ι) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := y.2
      exact ⟨x, hx⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (b ≫ U.ι) := by rw [hb]; infer_instance
  have : IsOpenImmersion b := IsOpenImmersion.of_comp b U.ι
  have hb' : b ''ᵁ ⊤ = U.toScheme.basicOpen a := by
    apply U.ι.image_injective
    show U.ι ''ᵁ b ''ᵁ ⊤ = U.ι ''ᵁ _
    rw [← Scheme.Hom.comp_image]
    simp only [hb]
    rw [Scheme.Hom.comp_image, Scheme.Opens.ι_image_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.2 hle]
  let p₀ := A.hom ∣_ U₀
  let j := (p₀ ⁻¹ᵁ V).ι ≫ (A.hom ⁻¹ᵁ U₀).ι
  have hj : j ≫ A.hom = (p₀ ∣_ V) ≫ b ≫ U.ι := by
    rw [hb, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, morphismRestrict_ι]
  obtain ⟨h, hh⟩ : ∃ h : (p₀ ⁻¹ᵁ V).toScheme ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = j :=
    ⟨IsOpenImmersion.lift _ j (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ U) hj).mpr (b ((p₀ ∣_ V) y)).2), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (h ≫ (A.hom ⁻¹ᵁ U).ι) := by rw [hh]; infer_instance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp h (A.hom ⁻¹ᵁ U).ι
  have e : h ≫ (A.hom ∣_ U) = (p₀ ∣_ V) ≫ b := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hj, Category.assoc]
  have hu : ∀ z, IsUnit (cst (A.hom ∣_ U) a z) ↔ (A.hom ∣_ U) z ∈ U.toScheme.basicOpen a := fun z => by
    rw [← Category.comp_id (A.hom ∣_ U), ← pb_cst, pb_unit, Category.comp_id]
    exact ⟨fun hz => (loc_cst a _).2 ⟨trivial, hz⟩, fun hz => (loc_cst a).unit hz⟩
  refine ⟨h ''ᵁ ⊤, fun z => ⟨?_, fun hz => ?_⟩, pack_push h ?_⟩
  · rintro ⟨y, -, rfl⟩
    refine ⟨trivial, (hu _).2 ?_⟩
    rw [← hb']
    exact ⟨(p₀ ∣_ V) y, trivial, (congrArg (fun q => q y) e).symm⟩
  · have hz := (hu z).1 hz.2
    have e₁ : U.ι ((A.hom ∣_ U) z) = A.hom z.1 := morphismRestrict_base_coe A.hom U z
    have m₀ : z.1 ∈ A.hom ⁻¹ᵁ U₀ := by
      show A.hom z.1 ∈ U₀
      rw [← e₁]; exact ha hz
    have m₁ : (⟨z.1, m₀⟩ : (A.hom ⁻¹ᵁ U₀).toScheme) ∈ p₀ ⁻¹ᵁ V :=
      ⟨_, hz, e₁.trans (morphismRestrict_base_coe A.hom U₀ ⟨z.1, m₀⟩).symm⟩
    exact ⟨⟨_, m₁⟩, trivial, Subtype.ext (congrArg (fun q => q ⟨_, m₁⟩) hh)⟩
  obtain ⟨N, hN, M, s, cov, hs⟩ := H V hV
  choose aff r hr surj using hs
  let P := powOver (Over.mk p₀) (L.pull (A.hom ⁻¹ᵁ U₀).ι) V N
  let κ : L.ι → P.ι := fun i _ _ => i
  have pt : ∀ y, (A.hom ⁻¹ᵁ U).ι (h y) = (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) := fun y => congrArg (fun q => q y) hh
  have hκ : ∀ i, h ⁻¹ᵁ ((A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i) ≤ P.U (κ i) := fun i y hy =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (show (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) ∈ L.U i from pt y ▸ hy)
  have hγ : ∀ y, y ∈ P.U (κ (c (h y))) := fun y => hκ _ (hc (h y))
  refine Pack.mono (S := Set.range (cst (p₀ ∣_ V))) ⟨N, hN, M, fun i => sv (fun y => κ (c (h y))) (s i),
    fun i => nonzeroLocus (s i), fun i => sc_sv hκ (fun y => hc (h y)) (fun i y hy => ?_) (s i),
    fun i => loc_sv hγ (s i), fun y _ => Opens.mem_iSup.1 (cov.ge trivial), aff, fun i => ?_⟩ ?_
  · have hm : (A.hom ⁻¹ᵁ U).ι (h y) ∈ L.U i ⊓ L.U (c (h y)) := ⟨hy, hc (h y)⟩
    have m₁ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => i) :=
      mem_pull.2 ((pt y) ▸ hm.1)
    have m₂ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => c (h y)) :=
      mem_pull.2 ((pt y) ▸ hm.2)
    refine (gm_const _ _ N y _ _ m₁ m₂).trans ?_
    refine congrArg (· ^ N) ((congrArg Units.val (gm_pull_g L _ _ y _ _ m₁ m₂)).trans ?_)
    rw [pb_apply, ← gs_unit _ _ _ hm, stalkMap_gs h _ y _ hm, gs_unit _ y _ hm, hh]
  · exact (gen_iff _ (r i) _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply]; rfl))
      (fun m => (ratio_iff hγ (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  · rintro _ ⟨x, rfl⟩
    exact cst_mem a b hb' _ h _ e x

/-- On each affine base open, glue the ample families over a finite distinguished cover. -/
theorem relAmple_of_locally : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom →
    QuasiSeparated A.hom → (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
      RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → RelAmple A L := by
  intro S A L hL _ _ H U hU
  have : IsAffine U := hU
  have : CompactSpace (A.hom ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace (A.hom ∣_ U)
  have : QuasiSeparatedSpace (A.hom ⁻¹ᵁ U).toScheme := quasiSeparatedSpace_of_quasiSeparated (A.hom ∣_ U)
  choose c hc using fun z : (A.hom ⁻¹ᵁ U).toScheme => exists_chart hL ((A.hom ⁻¹ᵁ U).ι z)
  let good : Set Γ(U.toScheme, ⊤) := {a | ∃ U₀ : S.Opens, U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀ ∧
    RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)}
  have hspan : Ideal.span good = ⊤ := by
    rw [← (isAffineOpen_top U.toScheme).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro x _
    obtain ⟨U₀, hx, h₀⟩ := H (U.ι x)
    obtain ⟨a, ha, hxa⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le (V := U.ι ⁻¹ᵁ U₀) ⟨x, hx⟩ trivial
    exact Opens.mem_iSup.2 ⟨⟨a, U₀, ha, h₀⟩, hxa⟩
  obtain ⟨t, ht, hspan'⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  choose W hW hP using fun l : t => (ht l.2).elim fun U₀ h₀ => pack_of_relAmple A L U hU U₀ h₀.2 l.1 h₀.1 c hc
  have hcov : ∀ z, ∃ i, z ∈ (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i := fun z => ⟨c z, hc z⟩
  obtain ⟨N, hN, M, σ, hσ, cov, main⟩ := glue_pack hcov (fun _ _ => Units.isUnit _) (fun i j =>
      reg_congr (reg_gs (A.hom ⁻¹ᵁ U).ι _ (L.g i j).val) fun z hz => by
        show _ = (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val * Ring.inverse (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g j (c z))).val
        rw [gs_unit _ z _ hz, Ring.inverse_unit, ← Units.val_mul, ← gm_cocycle hL _ z hz.1 hz.2 (hc z),
          mul_inv_cancel_right])
    (cst (A.hom ∣_ U)) (reg_cst _) (fun l : t => l.1) (by rw [Subtype.range_coe_subtype]; exact hspan') W hW hP
  let κ : L.ι → (powOver A L U N).ι := fun i _ => i
  have hκ : ∀ i, (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i ≤ (powOver A L U N).U (κ i) := fun i y hy => Set.mem_iInter.2 fun _ => hy
  have hγ : ∀ y, y ∈ (powOver A L U N).U (κ (c y)) := fun y => hκ _ (hc y)
  choose s hs using fun m => exists_sv hκ hc (fun i y hy => gm_const L _ N y _ _ hy (hc y))
    (hL.linComb _ _) (hσ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (s m)) ⊤ (σ m) := fun m => hs m ▸ loc_sv hγ (s m)
  refine ⟨N, hN, M, s, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i _ (loc i)).1, ?_⟩⟩
  · obtain ⟨m, hm⟩ := cov z
    exact Opens.mem_iSup.2 ⟨m, (loc m z).2 ⟨trivial, hm⟩⟩
  · choose r hr using fun m => mem_reg_iff.1 (Sc.ratio hcov (fun _ _ => Units.isUnit _) (hσ m) (hσ i) (loc i))
    refine ⟨r, fun m => (ratio_iff hγ (s i) (s m) (r m)).2 (by rw [hs, hs]; exact hr m), ?_⟩
    exact (gen_iff _ r _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply])) hr).1 (main i _ (loc i)).2

end GlobalTheory.AmpleLocal
