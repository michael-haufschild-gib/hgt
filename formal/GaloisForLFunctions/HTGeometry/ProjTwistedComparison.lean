import GaloisForLFunctions.HTGeometry.GradedTwistedCech
import GaloisForLFunctions.HTGeometry.AffineStructureSheafAcyclic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The Čech complex of `𝒪` on `Proj` from homogeneous localizations

Let `M` be an `ℕ`-graded algebra and `w_i ∈ 𝒜_1` linear forms whose basic opens `D₊(w_i)` cover
`Proj M`.  The sections of the structure sheaf over `D₊(w_s)` are the degree-zero fractions
`M_{(w_s)}` (`Proj.basicOpenIsoAway`), and restriction is the canonical map `M_{(w_s)} → M_{(w_t)}`
(`Proj.awayMap_awayToSection`).  Hence the Čech datum of `𝒪_{Proj M}` for the cover agrees, on every
nonempty subset, with the twisted datum `twCech 𝒜 w 0` of degree-zero fractions.  Consequently:

* exactness of `twCech 𝒜 w 0` in positive degrees, together with Serre's vanishing on the affine
  opens `D₊(w_s)` and Leray's theorem, kills `H^q(Proj M, 𝒪)` for `q > 0`;
* exactness in degree `0` makes every global section of `𝒪` come from `𝒜_0`.

* `HTGeometry.projCompare` : the comparison morphism.
* `HTGeometry.proj_cohomology_vanishing` : `H^{q+1}(Proj M, 𝒪) = 0`.
* `HTGeometry.proj_globalSection_surjective` : global sections from degree zero.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-! ## Transport of positive-degree exactness along morphisms bijective off the empty subset -/

namespace FinsetCechDatum

variable {T : Type*} [DecidableEq T] [LinearOrder T] {D E : FinsetCechDatum T}

/-- **Exactness in positive degrees transports forward along a morphism that is bijective on every
nonempty subset.** -/
theorem exactAt_succ_of_bijective_nonempty (φ : Hom D E)
    (hφ : ∀ s : Finset T, s.Nonempty → Function.Bijective (φ.app s)) {p : ℕ}
    (hD : D.ExactAt (p + 1)) : E.ExactAt (p + 1) := by
  classical
  intro c hc hdc
  let c' : D.Cochain := fun s => if hs : s.Nonempty then Function.surjInv (hφ s hs).2 (c s) else 0
  have hc'φ : ∀ s, φ.app s (c' s) = c s := by
    intro s
    by_cases hs : s.Nonempty
    · simp only [c', dif_pos hs]
      exact Function.surjInv_eq (hφ s hs).2 (c s)
    · simp only [c', dif_neg hs, map_zero]
      rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      exact (hc ∅ (by simp)).symm
  have hφc' : φ.onCochain c' = c := funext hc'φ
  have hdeg : D.IsDeg c' (p + 1) := by
    intro s hs
    by_cases hne : s.Nonempty
    · apply (hφ s hne).1
      rw [hc'φ, hc s hs, map_zero]
    · simp only [c', dif_neg hne]
  have hdc' : D.d c' = 0 := by
    funext s
    by_cases hne : s.Nonempty
    · apply (hφ s hne).1
      have := congrFun (φ.d_onCochain c') s
      rw [hφc', hdc] at this
      change φ.app s (D.d c' s) = φ.app s 0
      rw [map_zero]
      exact this.symm
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [d]
  obtain ⟨b, hb, hdb⟩ := hD c' hdeg hdc'
  refine ⟨φ.onCochain b, fun s hs => ?_, ?_⟩
  · change φ.app s (b s) = 0
    rw [hb s hs, map_zero]
  · rw [φ.d_onCochain, hdb, hφc']

/-- **Sections over the covered set come from the source** when the source is exact in degree `0`,
the target is separated, and the morphism is bijective on nonempty subsets. -/
theorem surjective_bot_of_bijective_nonempty (φ : Hom D E)
    (hφ : ∀ s : Finset T, s.Nonempty → Function.Bijective (φ.app s)) (hD : D.ExactAt 0)
    (hE : E.ExactBot) : Function.Surjective (φ.app ∅) := by
  classical
  intro σ
  let c : E.Cochain := fun s => if hs : s = ∅ then hs ▸ σ else 0
  have hcbot : E.IsBot c := fun s hs => dif_neg hs.ne_empty
  have hc0 : c ∅ = σ := dif_pos rfl
  let e' : D.Cochain := fun s =>
    if hs : s.Nonempty then Function.surjInv (hφ s hs).2 (E.d c s) else 0
  have he'φ : ∀ s, s.Nonempty → φ.app s (e' s) = E.d c s := by
    intro s hs
    simp only [e', dif_pos hs]
    exact Function.surjInv_eq (hφ s hs).2 _
  have hdeg : D.IsDeg e' 0 := by
    intro s hs
    by_cases hne : s.Nonempty
    · apply (hφ s hne).1
      rw [he'φ s hne, map_zero]
      exact E.d_isDeg_of_isBot hcbot s hs
    · simp only [e', dif_neg hne]
  have hφe' : φ.onCochain e' = E.d c := by
    funext s
    by_cases hne : s.Nonempty
    · exact he'φ s hne
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      change φ.app ∅ (e' ∅) = E.d c ∅
      simp only [e', d]
      simp
  have hde' : D.d e' = 0 := by
    funext s
    by_cases hne : s.Nonempty
    · apply (hφ s hne).1
      have := congrFun (φ.d_onCochain e') s
      rw [hφe', E.d_d] at this
      change φ.app s (D.d e' s) = φ.app s 0
      rw [map_zero]
      exact this.symm
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [d]
  obtain ⟨b, hb, hdb⟩ := hD e' hdeg hde'
  have hbot : E.IsBot (φ.onCochain b - c) := by
    intro s hs
    change φ.app s (b s) - c s = 0
    rw [hb s (Finset.card_ne_zero.mpr hs), hcbot s hs, map_zero, sub_zero]
  have hdiff : E.d (φ.onCochain b - c) = 0 := by
    rw [E.d_sub, φ.d_onCochain, hdb, hφe', sub_self]
  have := congrFun (hE _ hbot hdiff) ∅
  refine ⟨b ∅, ?_⟩
  rw [← hc0]
  exact sub_eq_zero.mp this

end FinsetCechDatum

/-- Restrictions of sections of a scheme compose. -/
theorem schemeRes_res {X : Scheme.{u}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z)
      = (X.presheaf.map (homOfLE (h2.trans h1)).op).hom z :=
  RHTower.deningerRes_res (F := schemeAbSheaf X) h1 h2 z

section Comparison

variable {K : Type*} [CommRing K] {M : Type u} [CommRing M] [Algebra K M]
  {𝒜 : ℕ → Submodule K M} [GradedAlgebra 𝒜] {ι : Type*} [DecidableEq ι] [LinearOrder ι]
  {w : ι → M} (hw : ∀ i, w i ∈ 𝒜 1)

omit [LinearOrder ι] in
include hw in
/-- A degree-zero fraction is a degree-zero element of the twisted datum. -/
theorem val_mem_twPart (s : Finset ι) (a : HomogeneousLocalization.Away 𝒜 (wProd w s)) :
    a.val ∈ twPart 𝒜 w s 0 := by
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 (wProd_mem hw s) a
  rw [HomogeneousLocalization.Away.val_mk]
  exact frac_mem_twPart (m := n) hx (by simp [smul_eq_mul])

/-- Degree-zero fractions as the degree-zero twisted part. -/
noncomputable def awayToTw (s : Finset ι) :
    HomogeneousLocalization.Away 𝒜 (wProd w s) →+ twPart 𝒜 w s 0 where
  toFun a := ⟨a.val, val_mem_twPart hw s a⟩
  map_zero' := Subtype.ext HomogeneousLocalization.val_zero
  map_add' a b := Subtype.ext (HomogeneousLocalization.val_add a b)

omit [LinearOrder ι] in
theorem awayToTw_bijective (s : Finset ι) : Function.Bijective (awayToTw (𝒜 := 𝒜) hw s) := by
  refine ⟨fun a b h => HomogeneousLocalization.val_injective _ (congrArg Subtype.val h), ?_⟩
  rintro ⟨y, hy⟩
  let valHom : HomogeneousLocalization.Away 𝒜 (wProd w s) →+ LocAt w s :=
    { toFun := HomogeneousLocalization.val
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  have hle : twPart 𝒜 w s 0 ≤ valHom.range := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
    have hx' : x ∈ 𝒜 (m • s.card) := by
      rw [smul_eq_mul, ← hdeg, add_zero]
      exact hx
    refine ⟨HomogeneousLocalization.Away.mk 𝒜 (wProd_mem hw s) m x hx', ?_⟩
    change (HomogeneousLocalization.Away.mk 𝒜 (wProd_mem hw s) m x hx').val = frac w s m x
    rw [HomogeneousLocalization.Away.val_mk]
    rfl
  obtain ⟨a, ha⟩ := hle hy
  exact ⟨a, Subtype.ext ha⟩

/-- The degree-zero fractions as the twisted part, additively. -/
noncomputable def twAwayEquiv (s : Finset ι) :
    HomogeneousLocalization.Away 𝒜 (wProd w s) ≃+ twPart 𝒜 w s 0 :=
  AddEquiv.ofBijective (awayToTw hw s) (awayToTw_bijective hw s)

omit [LinearOrder ι] in
theorem twAwayEquiv_val (s : Finset ι) (a : HomogeneousLocalization.Away 𝒜 (wProd w s)) :
    (twAwayEquiv hw s a : LocAt w s) = a.val := rfl

omit [LinearOrder ι] in
theorem twVal_twAwayEquiv (s : Finset ι) (a : HomogeneousLocalization.Away 𝒜 (wProd w s)) :
    twVal hw (e := 0) (twAwayEquiv hw s a) = a.val := rfl

variable (w) in
/-- The cover of `Proj M` by the basic opens of the forms. -/
def projCover : ι → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (w i)

omit [LinearOrder ι] in
theorem coverInter_projCover (s : Finset ι) :
    coverInter ⊤ (projCover (𝒜 := 𝒜) w) s = Proj.basicOpen 𝒜 (wProd w s) := by
  induction s using Finset.induction_on with
  | empty => rw [coverInter_empty, wProd, Finset.prod_empty, Proj.basicOpen_one]
  | insert a s ha ih =>
    have : coverInter ⊤ (projCover (𝒜 := 𝒜) w) (insert a s)
        = projCover (𝒜 := 𝒜) w a ⊓ coverInter ⊤ (projCover (𝒜 := 𝒜) w) s := by
      rw [coverInter, coverInter, Finset.inf_insert]
      ac_rfl
    rw [this, ih]
    show _ = Proj.basicOpen 𝒜 (∏ i ∈ insert a s, w i)
    rw [Finset.prod_insert ha, Proj.basicOpen_mul]
    rfl

variable (w) in
/-- Sections over `D₊(w_s)` from degree-zero fractions. -/
noncomputable def sectionHom (s : Finset ι) :
    HomogeneousLocalization.Away 𝒜 (wProd w s) →+
      (sheafCech (schemeAbSheaf (Proj 𝒜)) ⊤ (projCover (𝒜 := 𝒜) w)).obj s :=
  ((Proj 𝒜).presheaf.map (homOfLE (le_of_eq (coverInter_projCover (𝒜 := 𝒜) (w := w) s))).op).hom.toAddMonoidHom.comp
    (Proj.awayToSection 𝒜 (wProd w s)).hom.toAddMonoidHom

omit [LinearOrder ι] in
theorem wProd_eq_mul_sdiff {s t : Finset ι} (h : s ⊆ t) :
    wProd w t = wProd w s * wProd w (t \ s) := by
  rw [mul_comm, wProd_sdiff_mul h]

omit [LinearOrder ι] in
/-- **Restriction of degree-zero fractions is the localization map.** -/
theorem val_awayMap_eq_resLoc {s t : Finset ι} (h : s ⊆ t)
    (a : HomogeneousLocalization.Away 𝒜 (wProd w s)) :
    (HomogeneousLocalization.awayMap 𝒜 (wProd_mem hw (t \ s)) (wProd_eq_mul_sdiff h) a).val
      = resLoc w h a.val := by
  rw [HomogeneousLocalization.val_awayMap]
  refine DFunLike.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (wProd w s))
    (RingHom.ext fun m => ?_)) a.val
  simp only [RingHom.comp_apply, resLoc_algebraMap]
  exact IsLocalization.lift_eq _ m

/-- **The comparison morphism** from the degree-zero twisted datum to the Čech datum of
`𝒪_{Proj M}`. -/
noncomputable def projCompare :
    (twCech 𝒜 w hw 0).Hom (sheafCech (schemeAbSheaf (Proj 𝒜)) ⊤ (projCover (𝒜 := 𝒜) w)) where
  app s := (sectionHom w s).comp (twAwayEquiv hw s).symm.toAddMonoidHom
  comm {s t} h y := by
    set a := (twAwayEquiv hw s).symm y with ha
    have hy : y = twAwayEquiv hw s a := by rw [ha, AddEquiv.apply_symm_apply]
    have hres : (twAwayEquiv hw t).symm ((twCech 𝒜 w hw 0).res h y)
        = HomogeneousLocalization.awayMap 𝒜 (wProd_mem hw (t \ s)) (wProd_eq_mul_sdiff h) a := by
      apply (twAwayEquiv hw t).injective
      rw [AddEquiv.apply_symm_apply]
      apply twVal_injective hw
      rw [twCech_res_val, hy, twVal_twAwayEquiv, twVal_twAwayEquiv, val_awayMap_eq_resLoc hw h a]
    change ((Proj 𝒜).presheaf.map _).hom
        (((Proj 𝒜).presheaf.map _).hom ((Proj.awayToSection 𝒜 (wProd w s)).hom a))
      = ((Proj 𝒜).presheaf.map _).hom ((Proj.awayToSection 𝒜 (wProd w t)).hom
          ((twAwayEquiv hw t).symm ((twCech 𝒜 w hw 0).res h y)))
    rw [hres]
    have key := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection 𝒜 (wProd_mem hw (t \ s))
      (wProd_eq_mul_sdiff h))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at key
    rw [key, schemeRes_res, schemeRes_res]

theorem schemeRes_self {X : Scheme.{u}} {U : X.Opens} (z : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_refl U)).op).hom z = z :=
  RHTower.deningerRes_self (F := schemeAbSheaf X) U z

omit [LinearOrder ι] in
/-- **The comparison is bijective over every nonempty subset.** -/
theorem projCompare_bijective {s : Finset ι} (hs : s.Nonempty) :
    Function.Bijective ((projCompare (𝒜 := 𝒜) hw).app s) := by
  have hm : 0 < s.card := Finset.card_pos.mpr hs
  haveI : IsIso (Proj.awayToSection 𝒜 (wProd w s)) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 (wProd w s) (wProd_mem hw s) hm]
    infer_instance
  have h1 : Function.Bijective (Proj.awayToSection 𝒜 (wProd w s)).hom :=
    ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒜 (wProd w s))
  have h2 : Function.Bijective ((Proj 𝒜).presheaf.map
      (homOfLE (le_of_eq (coverInter_projCover (𝒜 := 𝒜) (w := w) s))).op).hom := by
    refine Function.bijective_iff_has_inverse.mpr ⟨((Proj 𝒜).presheaf.map
      (homOfLE (le_of_eq (coverInter_projCover (𝒜 := 𝒜) (w := w) s).symm)).op).hom, fun z => ?_,
        fun z => ?_⟩
    · rw [schemeRes_res, schemeRes_self]
    · rw [schemeRes_res, schemeRes_self]
  exact (h2.comp h1).comp (twAwayEquiv hw s).symm.bijective

/-- **Leray on `Proj`**: positive-degree exactness of the degree-zero twisted datum kills the
higher cohomology of the structure sheaf. -/
theorem proj_cohomology_vanishing [HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} (Proj 𝒜))]
    (hcov : ⨆ i, Proj.basicOpen 𝒜 (w i) = ⊤)
    (hexact : ∀ p : ℕ, (twCech 𝒜 w hw 0).ExactAt (p + 1)) (q : ℕ)
    (x : RHTower.deningerSheafCohomology.{u} ⊤ (schemeAbSheaf (Proj 𝒜)) (q + 1)) : x = 0 := by
  refine leray_vanishing (V := ⊤) (U := projCover (𝒜 := 𝒜) w) (le_of_eq hcov.symm)
    ⟨fun s hs => ?_, fun p => ?_⟩ q x
  · rw [coverInter_projCover]
    exact affine_acyclicOn (Proj.isAffineOpen_basicOpen 𝒜 _ (wProd_mem hw s)
      (Finset.card_pos.mpr hs))
  · exact FinsetCechDatum.exactAt_succ_of_bijective_nonempty (projCompare hw)
      (fun _ hs => projCompare_bijective hw hs) (hexact p)

/-- **Global sections come from degree zero.** -/
theorem proj_globalSection_surjective (hcov : ⨆ i, Proj.basicOpen 𝒜 (w i) = ⊤)
    (h0 : (twCech 𝒜 w hw 0).ExactAt 0) :
    Function.Surjective ((projCompare (𝒜 := 𝒜) hw).app ∅) :=
  FinsetCechDatum.surjective_bot_of_bijective_nonempty (projCompare hw)
    (fun _ hs => projCompare_bijective hw hs) h0 (sheafCech_exactBot _ (le_of_eq hcov.symm))

end Comparison

end HTGeometry
