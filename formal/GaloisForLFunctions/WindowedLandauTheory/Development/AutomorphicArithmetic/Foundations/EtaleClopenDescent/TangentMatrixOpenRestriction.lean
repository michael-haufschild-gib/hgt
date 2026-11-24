import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CotangentRowsLocalization

/-! At a fixed point, the affine cotangent matrix survives restriction
of the correspondence to open subschemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.W1

variable {k : Type} [Field k] {Z Y : Scheme.{0}}
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

private theorem pullback_restrict_restrict (c : Y ⟶ Z) (hc : c ≫ s = t)
    {U U' : Z.Opens} {V V' : Y.Opens} (hU : U' ≤ U) (hV : V ≤ c ⁻¹ᵁ U)
    (hV' : V' ≤ c ⁻¹ᵁ U') (hVV : V' ≤ V) (a : SectionRing s U) :
    sectionRes t (homOfLE hV') (sectionPullback hc U' (sectionRes s (homOfLE hU) a)) =
      sectionRes t (homOfLE hVV) (sectionRes t (homOfLE hV) (sectionPullback hc U a)) := by
  change (Z.presheaf.map (homOfLE hU).op ≫ c.app U' ≫ Y.presheaf.map (homOfLE hV').op).hom a =
    (c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ Y.presheaf.map (homOfLE hVV).op).hom a
  congr 2
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

private theorem image_preimage_open {X : Scheme.{0}} (W : X.Opens) {U : X.Opens} (hU : U ≤ W) :
    W.ι ''ᵁ W.ι ⁻¹ᵁ U = U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hU]

private theorem isAffineOpen_on_open {X : Scheme.{0}} (W : X.Opens) {U : X.Opens}
    (hU : U ≤ W) (ha : IsAffineOpen U) : IsAffineOpen (W.ι ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι, image_preimage_open W hU]
  exact ha

private def sectionOpenEquiv {X : Scheme.{0}} (r : X ⟶ Spec (CommRingCat.of k))
    (W : X.Opens) {U : X.Opens} (hU : U ≤ W) :
    SectionRing r U ≃ₐ[k] SectionRing (W.ι ≫ r) (W.ι ⁻¹ᵁ U) := by
  haveI : IsIso (W.ι.app U) := by
    rw [Scheme.Opens.ι_app]
    have key {A B : X.Opens} (f : A ⟶ B) (he : A = B) : IsIso (X.presheaf.map f.op) := by
      subst B
      haveI : IsIso f := by
        rw [Subsingleton.elim f (𝟙 A)]
        infer_instance
      infer_instance
    exact key _ (image_preimage_open W hU)
  exact AlgEquiv.ofBijective (sectionPullback (f := W.ι) rfl U)
    (ConcreteCategory.bijective_of_isIso (W.ι.app U))

private theorem restrict_pullback_square {Z' Y' : Scheme.{0}}
    {s' : Z' ⟶ Spec (CommRingCat.of k)} {t' : Y' ⟶ Spec (CommRingCat.of k)}
    {i : Z' ⟶ Z} {j : Y' ⟶ Y} {c : Y ⟶ Z} {c' : Y' ⟶ Z'}
    (hi : i ≫ s = s') (hj : j ≫ t = t') (hc : c ≫ s = t) (hc' : c' ≫ s' = t')
    (he : c' ≫ i = j ≫ c) {U : Z.Opens} {V : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U)
    (hV' : j ⁻¹ᵁ V ≤ c' ⁻¹ᵁ (i ⁻¹ᵁ U)) (a : SectionRing s U) :
    sectionPullback hj V (sectionRes t (homOfLE hV) (sectionPullback hc U a)) =
      sectionRes t' (homOfLE hV') (sectionPullback hc' (i ⁻¹ᵁ U) (sectionPullback hi U a)) := by
  change (c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ j.app V).hom a =
    (i.app U ≫ c'.app (i ⁻¹ᵁ U) ≫ Y'.presheaf.map (homOfLE hV').op).hom a
  have key (f g : Y' ⟶ Z) (h : f = g)
      (u : j ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (v : j ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) :
      f.appLE U (j ⁻¹ᵁ V) u = g.appLE U (j ⁻¹ᵁ V) v := by
    subst g
    rfl
  have hl : c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ j.app V =
      (j ≫ c).appLE U (j ⁻¹ᵁ V) (fun _ hx => hV hx) := by
    rw [Scheme.Hom.comp_appLE, j.app_eq_appLE (U := V), j.map_appLE]
  have hr : i.app U ≫ c'.app (i ⁻¹ᵁ U) ≫ Y'.presheaf.map (homOfLE hV').op =
      (c' ≫ i).appLE U (j ⁻¹ᵁ V) hV' := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun f => f.hom a) (hl.trans ((key _ _ he.symm _ _).trans hr.symm))

/-- An affine cotangent matrix at a fixed point is preserved when
both sides of the correspondence are restricted to open subschemes. -/
theorem IsTan.restrictOpen
    {d : ℕ} {c₁ c₂ : Y ⟶ Z} {h₁ : c₁ ≫ s = t} {h₂ : c₂ ≫ s = t}
    (P : Z.Opens) (Q : Y.Opens) {c₁' c₂' : Q.toScheme ⟶ P.toScheme}
    (e₁ : c₁' ≫ P.ι = Q.ι ≫ c₁) (e₂ : c₂' ≫ P.ι = Q.ι ≫ c₂)
    (h₁' : c₁' ≫ (P.ι ≫ s) = Q.ι ≫ t) (h₂' : c₂' ≫ (P.ι ≫ s) = Q.ι ≫ t)
    (y' : Q.toScheme.BaseFieldPointOver k (Q.ι ≫ t))
    (hfix : (y'.hom ≫ Q.ι) ≫ c₁ = (y'.hom ≫ Q.ι) ≫ c₂)
    {M : Matrix (Fin d) (Fin d) k}
    (h : IsTan d h₁ h₂ (mapBaseFieldPoint (f := Q.ι) rfl y') M) :
    IsTan d h₁' h₂' y' M := by
  let y := mapBaseFieldPoint (f := Q.ι) (s := t) rfl y'
  obtain ⟨U, V, hv₁, hv₂, a, hy, hUa, hVa, hrows⟩ := h
  have heval₁ (x : Q.toScheme) : P.ι (c₁' x) = c₁ (Q.ι x) :=
    congrArg (fun f : Q.toScheme ⟶ Z => f x) e₁
  have heval₂ (x : Q.toScheme) : P.ι (c₂' x) = c₂ (Q.ι x) :=
    congrArg (fun f : Q.toScheme ⟶ Z => f x) e₂
  have hP : c₁ (y.hom default) ∈ P :=
    heval₁ (y'.hom default) ▸ (c₁' (y'.hom default)).property
  have hQ : y.hom default ∈ Q := (y'.hom default).property
  obtain ⟨f, hf, hf₁⟩ := hUa.exists_basicOpen_le ⟨_, hP⟩ (hv₁ hy)
  let U₀ := Z.basicOpen f
  have hcenter : c₁ (y.hom default) = c₂ (y.hom default) :=
    congrArg (fun f : Spec (CommRingCat.of k) ⟶ Z => f default) hfix
  have hf₂ : c₂ (y.hom default) ∈ U₀ := hcenter ▸ hf₁
  let W := Q ⊓ (c₁ ⁻¹ᵁ U₀ ⊓ c₂ ⁻¹ᵁ U₀)
  have hyW : y.hom default ∈ W := ⟨hQ, hf₁, hf₂⟩
  obtain ⟨g, hg, hgy⟩ := hVa.exists_basicOpen_le ⟨_, hyW⟩ hy
  let V₀ := Y.basicOpen g
  have hUle : U₀ ≤ U := Z.basicOpen_le f
  have hVle : V₀ ≤ V := Y.basicOpen_le g
  have hVQ : V₀ ≤ Q := fun x hx => (hg hx).1
  have hV₁ : V₀ ≤ c₁ ⁻¹ᵁ U₀ := fun x hx => (hg hx).2.1
  have hV₂ : V₀ ≤ c₂ ⁻¹ᵁ U₀ := fun x hx => (hg hx).2.2
  let a₀ (l : Fin d) := sectionRes s (homOfLE hUle) (a l)
  let r := sectionRes t (homOfLE hVle)
  letI : Algebra (SectionRing t V) (SectionRing t V₀) := r.toRingHom.toAlgebra
  letI : IsScalarTower k (SectionRing t V) (SectionRing t V₀) :=
    .of_algebraMap_eq fun c => (r.commutes c).symm
  letI : IsLocalization (Submonoid.powers (show SectionRing t V from g)) (SectionRing t V₀) :=
    hVa.isLocalization_basicOpen g
  have hEval (b : SectionRing t V) : affinePointEval y hgy (r b) = affinePointEval y hy b := by
    have h := Y.presheaf.germ_res_apply (homOfLE hVle) (y.hom default) hgy b
    exact (localPointEvalAlg_germ y hgy (r b)).symm.trans
      ((congrArg (localPointEvalAlg y) h).trans (localPointEvalAlg_germ y hy b))
  have hloc := hrows.localization (Submonoid.powers (show SectionRing t V from g)) hEval
  have hloc' : HasCotangentRows (affinePointEval y hgy)
      (fun l => sectionRes t (homOfLE hV₁) (sectionPullback h₁ U₀ (a₀ l)))
      (fun l => sectionRes t (homOfLE hV₂) (sectionPullback h₂ U₀ (a₀ l))) M := by
    rw [funext (fun l => pullback_restrict_restrict c₁ h₁ hUle hv₁ hV₁ hVle (a l)),
      funext (fun l => pullback_restrict_restrict c₂ h₂ hUle hv₂ hV₂ hVle (a l))]
    exact hloc
  have hV₁' : Q.ι ⁻¹ᵁ V₀ ≤ c₁' ⁻¹ᵁ (P.ι ⁻¹ᵁ U₀) := by
    intro x hx
    change P.ι (c₁' x) ∈ U₀
    exact (heval₁ x).symm ▸ hV₁ hx
  have hV₂' : Q.ι ⁻¹ᵁ V₀ ≤ c₂' ⁻¹ᵁ (P.ι ⁻¹ᵁ U₀) := by
    intro x hx
    change P.ι (c₂' x) ∈ U₀
    exact (heval₂ x).symm ▸ hV₂ hx
  let a' (l : Fin d) := sectionPullback (f := P.ι) (s := s) rfl U₀ (a₀ l)
  have hy' : y'.hom default ∈ Q.ι ⁻¹ᵁ V₀ := hgy
  refine ⟨P.ι ⁻¹ᵁ U₀, Q.ι ⁻¹ᵁ V₀, hV₁', hV₂', a', hy',
    isAffineOpen_on_open P hf (hUa.basicOpen f), isAffineOpen_on_open Q hVQ (hVa.basicOpen g), ?_⟩
  let ρ := sectionOpenEquiv t Q hVQ
  have hρ (b : SectionRing t V₀) : affinePointEval y' hy' (ρ b) = affinePointEval y hgy b :=
    (affinePointEval_pullback (f := Q.ι) rfl y' V₀ hgy b).symm
  have e₁' (l : Fin d) :
      ρ (sectionRes t (homOfLE hV₁) (sectionPullback h₁ U₀ (a₀ l))) =
        sectionRes (Q.ι ≫ t) (homOfLE hV₁')
          (sectionPullback h₁' (P.ι ⁻¹ᵁ U₀) (a' l)) :=
    restrict_pullback_square rfl rfl h₁ h₁' e₁ hV₁ hV₁' (a₀ l)
  have e₂' (l : Fin d) :
      ρ (sectionRes t (homOfLE hV₂) (sectionPullback h₂ U₀ (a₀ l))) =
        sectionRes (Q.ι ≫ t) (homOfLE hV₂')
          (sectionPullback h₂' (P.ι ⁻¹ᵁ U₀) (a' l)) :=
    restrict_pullback_square rfl rfl h₂ h₂' e₂ hV₂ hV₂' (a₀ l)
  rw [← funext e₁', ← funext e₂']
  exact hloc'.algEquiv ρ hρ

end GlobalTheory.W1
