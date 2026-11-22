import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistTrivialization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines
import GaloisForLFunctions.RHTower.Deninger.DeningerSheafGluing

/-! A section on one chart extends after multiplication by a sufficiently large
power of the chart coordinate. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RHTower
open GlobalTheory.SchemeCohomology.ProjTwist

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}}

private abbrev restrictRing {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →+* Γ(X, W) :=
  (X.presheaf.map (homOfLE h).op).hom

private abbrev restrictModule (F : X.Modules) {V W : X.Opens} (h : W ≤ V) : Γ(F, V) →+ Γ(F, W) :=
  (F.presheaf.map (homOfLE h).op).hom.toAddMonoidHom

private theorem restrictModule_comp (F : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : Γ(F, U)) : restrictModule F h₂ (restrictModule F h₁ s) = restrictModule F (h₂.trans h₁) s :=
  (F.presheaf.map_comp_apply (homOfLE h₁).op (homOfLE h₂).op s).symm

private theorem restrictRing_comp {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : Γ(X, U)) : restrictRing h₂ (restrictRing h₁ s) = restrictRing (h₂.trans h₁) s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

private theorem restrictModule_smul (F : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (f : Γ(X, V)) (s : Γ(F, V)) :
    restrictModule F h (f • s) = restrictRing h f • restrictModule F h s :=
  F.map_smul (homOfLE h).op f s

section Coordinates

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type*} [Fintype ι]
  {v : ι → A} (hv : ∀ i, v i ∈ 𝒜 1)

private abbrev coordOpen (i : ι) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (v i)

private abbrev ratio (i j : ι) : Γ(Proj 𝒜, coordOpen (𝒜 := 𝒜) (v := v) i) :=
  coordinateRatio (hv i) (hv j)

local notation "U" => coordOpen (𝒜 := 𝒜) (v := v)

variable (F : (Proj 𝒜).Modules) [F.IsQuasicoherent]

private theorem exists_chart_lift (j : ι) (s : Γ(F, U j)) :
    ∃ e : ℕ, ∃ g : ∀ i, Γ(F, U i), ∀ i,
      restrictModule F (inf_le_left : U i ⊓ U j ≤ U i) (g i) =
        restrictRing (inf_le_left : U i ⊓ U j ≤ U i) (ratio hv i j) ^ e •
          restrictModule F (inf_le_right : U i ⊓ U j ≤ U j) s := by
  classical
  have h (i : ι) : ∃ e : ℕ, ∃ g : Γ(F, U i),
      restrictModule F (inf_le_left : U i ⊓ U j ≤ U i) g =
        restrictRing (inf_le_left : U i ⊓ U j ≤ U i) (ratio hv i j) ^ e •
          restrictModule F (inf_le_right : U i ⊓ U j ≤ U j) s := by
    have hD := basicOpen_coordinateRatio (hv i) (hv j)
    have ha := Proj.isAffineOpen_basicOpen 𝒜 _ (hv i) Nat.one_pos
    have hl := (hasBasicOpenLocalization_of_isQuasicoherent F ha (ratio hv i j)).1
    let W := (Proj 𝒜).basicOpen (ratio hv i j)
    have hWj : W ≤ U j := hD.le.trans inf_le_right
    obtain ⟨e, g, hg⟩ := hl (restrictModule F hWj s)
    refine ⟨e, g, ?_⟩
    have he := congrArg (restrictModule F hD.ge) hg.symm
    simpa only [restrictModule_comp, restrictModule_smul, map_pow, restrictRing_comp] using he
  choose e g hg using h
  refine ⟨Finset.univ.sup e, fun i => ratio hv i j ^ (Finset.univ.sup e - e i) • g i, fun i => ?_⟩
  rw [restrictModule_smul, hg, smul_smul, map_pow, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ i))]

private theorem chart_lift_restrict {j : ι} {s : Γ(F, U j)} {m : ℕ} {g : ∀ i, Γ(F, U i)}
    (hg : ∀ i, restrictModule F (inf_le_left : U i ⊓ U j ≤ U i) (g i) =
      restrictRing (inf_le_left : U i ⊓ U j ≤ U i) (ratio hv i j) ^ m •
        restrictModule F (inf_le_right : U i ⊓ U j ≤ U j) s)
    {W : (Proj 𝒜).Opens} {i : ι} (hi : W ≤ U i) (hj : W ≤ U j) :
    restrictModule F hi (g i) = restrictRing hi (ratio hv i j) ^ m • restrictModule F hj s := by
  have h := congrArg (restrictModule F (le_inf hi hj)) (hg i)
  simpa only [restrictModule_comp, restrictModule_smul, map_pow, restrictRing_comp] using h

/-- After clearing denominators on all overlaps, the chart sections satisfy the
transition rule for the images of the negative twist generators. -/
theorem exists_compatible_chart_lifts (j : ι) (s : Γ(F, U j)) :
    ∃ m : ℕ, ∃ g : ∀ i, Γ(F, U i), g j = s ∧ ∀ i k,
      restrictModule F (inf_le_left : U i ⊓ U k ≤ U i) (g i) =
        restrictRing (inf_le_left : U i ⊓ U k ≤ U i) (ratio hv i k) ^ m •
          restrictModule F (inf_le_right : U i ⊓ U k ≤ U k) (g k) := by
  classical
  obtain ⟨e, g, hg⟩ := exists_chart_lift hv F j s
  have hkill (i k : ι) :
      let il : U i ⊓ U k ≤ U i := inf_le_left
      let kr : U i ⊓ U k ≤ U k := inf_le_right
      ∃ b : ℕ, restrictRing il (ratio hv i j) ^ b •
        (restrictModule F il (g i) -
          restrictRing il (ratio hv i k) ^ e • restrictModule F kr (g k)) = 0 := by
    let W := U i ⊓ U k
    let il : W ≤ U i := inf_le_left
    let kr : W ≤ U k := inf_le_right
    let f := restrictRing il (ratio hv i j)
    have ha : IsAffineOpen W := by
      change IsAffineOpen (Proj.basicOpen 𝒜 (v i) ⊓ Proj.basicOpen 𝒜 (v k))
      rw [← Proj.basicOpen_mul]
      exact Proj.isAffineOpen_basicOpen 𝒜 _ (SetLike.mul_mem_graded (hv i) (hv k)) (by decide)
    apply (hasBasicOpenLocalization_of_isQuasicoherent F ha f).2
    have hW : (Proj 𝒜).basicOpen f = W ⊓ (U i ⊓ U j) := by
      rw [Scheme.basicOpen_res, basicOpen_coordinateRatio]
    let h : (Proj 𝒜).basicOpen f ≤ W := Scheme.basicOpen_le _ _
    have hj : (Proj 𝒜).basicOpen f ≤ U j := hW.le.trans (inf_le_right.trans inf_le_right)
    change restrictModule F h
      (restrictModule F il (g i) - restrictRing il (ratio hv i k) ^ e •
        restrictModule F kr (g k)) = 0
    rw [map_sub, restrictModule_comp, restrictModule_smul, map_pow, restrictRing_comp,
      restrictModule_comp, chart_lift_restrict hv F hg (h.trans il) hj,
      chart_lift_restrict hv F hg (h.trans kr) hj, smul_smul, sub_eq_zero]
    have hr := congrArg (restrictRing h) (coordinateRatio_mul (hv i) (hv k) (hv j))
    rw [map_mul, restrictRing_comp, restrictRing_comp, restrictRing_comp] at hr
    rw [← mul_pow, hr]
  choose b hb using hkill
  let B := Finset.univ.sup fun ik : ι × ι => b ik.1 ik.2
  let t (i : ι) := ratio hv i j ^ B • g i
  refine ⟨B + e, t, ?_, ?_⟩
  · have hj := chart_lift_restrict hv F hg (i := j) (W := U j) le_rfl le_rfl
    have hM (z : Γ(F, U j)) : restrictModule F le_rfl z = z := by
      simp [restrictModule]
    simp only [hM, coordinateRatio_self, map_one, one_pow, one_smul] at hj
    rw [t, coordinateRatio_self, one_pow, one_smul, hj]
  · intro i k
    let il : U i ⊓ U k ≤ U i := inf_le_left
    let kr : U i ⊓ U k ≤ U k := inf_le_right
    have hbk : b i k ≤ B := Finset.le_sup (f := fun ik : ι × ι => b ik.1 ik.2)
      (Finset.mem_univ (i, k))
    have hz := hb i k
    change restrictRing il (ratio hv i j) ^ b i k •
      (restrictModule F il (g i) - restrictRing il (ratio hv i k) ^ e •
        restrictModule F kr (g k)) = 0 at hz
    have hB : restrictRing il (ratio hv i j) ^ B •
        (restrictModule F il (g i) - restrictRing il (ratio hv i k) ^ e •
          restrictModule F kr (g k)) = 0 := by
      rw [← Nat.sub_add_cancel hbk, pow_add, mul_smul, hz, smul_zero]
    rw [smul_sub, sub_eq_zero, smul_smul] at hB
    have hr := coordinateRatio_mul (hv i) (hv k) (hv j)
    change restrictRing il (ratio hv i k) * restrictRing kr (ratio hv k j) =
      restrictRing il (ratio hv i j) at hr
    change restrictModule F il (t i) =
      restrictRing il (ratio hv i k) ^ (B + e) • restrictModule F kr (t k)
    dsimp only [t]
    rw [restrictModule_smul, restrictModule_smul, map_pow, map_pow, smul_smul, hB,
      ← hr, mul_pow, pow_add]
    congr 1
    ac_rfl

/-- Every section on a coordinate chart is the image of the local generator of
some negative twist under a global module morphism. -/
theorem exists_twist_hom_lifting_section (hcov : ⨆ i, U i = ⊤) (j : ι) (s : Γ(F, U j)) :
    ∃ (m : ℕ) (f : twistingSheaf 𝒜 (-(m : ℤ)) ⟶ F),
      f.app (U j) (coordinatePower (hv j) (-(m : ℤ))) = s := by
  classical
  obtain ⟨m, g, hgj, hg⟩ := exists_compatible_chart_lifts hv F j s
  let T := twistingSheaf 𝒜 (-(m : ℤ))
  let b (i : ι) := coordinatePower (hv i) (-(m : ℤ))
  let φ (i : ι) (W : (Proj 𝒜).Opens) (h : W ≤ U i) : Γ(Proj 𝒜, W) ≃ₗ[Γ(Proj 𝒜, W)] Γ(T, W) :=
    LinearEquiv.ofBijective
      { toFun := fun r => r • restrictModule T h (b i)
        map_add' := fun _ _ => add_smul _ _ _
        map_smul' := fun r t => mul_smul r t _ }
      (coordinatePower_basis (hv i) _ h)
  let localMap (i : ι) {W : (Proj 𝒜).Opens} (h : W ≤ U i) (z : Γ(T, W)) :=
    (φ i W h).symm z • restrictModule F h (g i)
  have hscalar (i : ι) {V W : (Proj 𝒜).Opens} (h : W ≤ V) (hi : V ≤ U i) (z : Γ(T, V)) :
      (φ i W (h.trans hi)).symm (restrictModule T h z) =
        restrictRing h ((φ i V hi).symm z) := by
    apply (φ i W (h.trans hi)).injective
    rw [LinearEquiv.apply_symm_apply]
    have hz := (φ i V hi).apply_symm_apply z
    change (φ i V hi).symm z • restrictModule T hi (b i) = z at hz
    change restrictModule T h z = restrictRing h ((φ i V hi).symm z) •
      restrictModule T (h.trans hi) (b i)
    rw [← restrictModule_comp, ← restrictModule_smul, hz]
  have hlocal (i : ι) {V W : (Proj 𝒜).Opens} (h : W ≤ V) (hi : V ≤ U i) (z : Γ(T, V)) :
      restrictModule F h (localMap i hi z) =
        localMap i (h.trans hi) (restrictModule T h z) := by
    rw [localMap, localMap, restrictModule_smul, restrictModule_comp, hscalar]
  have hoverlap (i k : ι) (W : (Proj 𝒜).Opens) (hi : W ≤ U i) (hk : W ≤ U k) (z : Γ(T, W)) :
      localMap i hi z = localMap k hk z := by
    have hb0 := congrArg (restrictModule T (le_inf hi hk)) (coordinatePower_neg_overlap (hv i) (hv k) m)
    have hg0 := congrArg (restrictModule F (le_inf hi hk)) (hg i k)
    have hb' : restrictModule T hi (b i) =
        restrictRing hi (ratio hv i k) ^ m • restrictModule T hk (b k) := by
      simpa only [restrictModule_comp, restrictModule_smul, map_pow, restrictRing_comp] using hb0
    have hg' : restrictModule F hi (g i) =
        restrictRing hi (ratio hv i k) ^ m • restrictModule F hk (g k) := by
      simpa only [restrictModule_comp, restrictModule_smul, map_pow, restrictRing_comp] using hg0
    have he : (φ k W hk).symm z = (φ i W hi).symm z * restrictRing hi (ratio hv i k) ^ m := by
      apply (φ k W hk).injective
      rw [LinearEquiv.apply_symm_apply]
      change z = _ • restrictModule T hk (b k)
      rw [mul_smul, ← hb']
      exact ((φ i W hi).apply_symm_apply z).symm
    change (φ i W hi).symm z • restrictModule F hi (g i) =
      (φ k W hk).symm z • restrictModule F hk (g k)
    rw [hg', he, mul_smul]
  let A := (SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).obj F
  let Wc (W : (Proj 𝒜).Opens) (i : ι) := W ⊓ U i
  have hWc (W : (Proj 𝒜).Opens) : W ≤ ⨆ i, Wc W i := by
    change W ≤ ⨆ i, W ⊓ U i
    rw [← inf_iSup_eq, hcov, inf_top_eq]
  have lift (W : (Proj 𝒜).Opens) (z : Γ(T, W)) : ∃ y : Γ(F, W), ∀ i,
      restrictModule F (inf_le_left : Wc W i ≤ W) y =
        localMap i (inf_le_right : Wc W i ≤ U i)
          (restrictModule T (inf_le_left : Wc W i ≤ W) z) := by
    refine deningerGlue' (F := A) (fun i => (inf_le_left : Wc W i ≤ W)) (hWc W) _ ?_
    intro i k D hi hk
    change restrictModule F hi (localMap i _ (restrictModule T _ z)) =
      restrictModule F hk (localMap k _ (restrictModule T _ z))
    rw [hlocal, hlocal, restrictModule_comp, restrictModule_comp]
    exact hoverlap i k _ _ _ _
  choose f hf using lift
  have hsep (W : (Proj 𝒜).Opens) {a b : Γ(F, W)}
      (h : ∀ i, restrictModule F (inf_le_left : Wc W i ≤ W) a =
        restrictModule F (inf_le_left : Wc W i ≤ W) b) : a = b :=
    deningerRes_ext (F := A) (fun i => (inf_le_left : Wc W i ≤ W)) (hWc W) a b h
  have hzero (W : (Proj 𝒜).Opens) : f W 0 = 0 := by
    apply hsep W
    intro i
    rw [hf, map_zero, map_zero]
    exact (zero_smul _ _)
  have hadd (W : (Proj 𝒜).Opens) (x y : Γ(T, W)) : f W (x + y) = f W x + f W y := by
    apply hsep W
    intro i
    simp only [hf, map_add, localMap, add_smul]
  have hsmul (W : (Proj 𝒜).Opens) (r : Γ(Proj 𝒜, W)) (z : Γ(T, W)) :
      f W (r • z) = r • f W z := by
    apply hsep W
    intro i
    simp only [restrictModule_smul, hf, localMap, map_smul, smul_assoc]
  have hres {V W : (Proj 𝒜).Opens} (h : W ≤ V) (z : Γ(T, V)) :
      f W (restrictModule T h z) = restrictModule F h (f V z) := by
    apply hsep W
    intro i
    have hh : Wc W i ≤ Wc V i := inf_le_inf_right (U i) h
    rw [hf, restrictModule_comp, ← restrictModule_comp F (inf_le_left : Wc V i ≤ V) hh,
      hf, hlocal, restrictModule_comp, restrictModule_comp]
  let hom : T ⟶ F := SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom ⟨f W.unop, hzero W.unop, hadd W.unop⟩
      naturality := fun _ _ i => AddCommGrpCat.ext (hres i.unop.le) }
    (fun W => hsmul W.unop)
  refine ⟨m, hom, ?_⟩
  change f (U j) (b j) = s
  have he : U j ≤ Wc (U j) j := le_inf le_rfl le_rfl
  have h := congrArg (restrictModule F he) (hf (U j) (b j) j)
  rw [restrictModule_comp, hlocal, restrictModule_comp] at h
  have hM (M : (Proj 𝒜).Modules) (z : Γ(M, U j)) : restrictModule M le_rfl z = z := by
    simp [restrictModule]
  simp only [hM] at h
  rw [h, ← hgj]
  change (φ j (U j) le_rfl).symm (b j) • g j = g j
  have h1 : (φ j (U j) le_rfl).symm (b j) = 1 := by
    apply (φ j (U j) le_rfl).injective
    rw [LinearEquiv.apply_symm_apply]
    change b j = (1 : Γ(Proj 𝒜, U j)) • restrictModule T le_rfl (b j)
    rw [hM, one_smul]
  rw [h1, one_smul]

end Coordinates

end GlobalTheory.SchemeCohomology
