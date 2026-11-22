import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import GaloisForLFunctions.HTGeometry.AffineStructureSheafAcyclic

/-! Relative forms have vanishing higher cohomology on affine opens. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry RHTower

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u w

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)

private theorem relativeForms_localization {U V : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (e : V = X.basicOpen g) (i : V ⟶ U) :
    (∀ y : Γ(relativeForms s n, V), ∃ (m : ℕ) (x : Γ(relativeForms s n, U)),
      (relativeForms s n).presheaf.map i.op x = (X.presheaf.map i.op g) ^ m • y) ∧
    ∀ x : Γ(relativeForms s n, U), (relativeForms s n).presheaf.map i.op x = 0 →
      ∃ m : ℕ, g ^ m • x = 0 := by
  subst V
  have hi : i = homOfLE (X.basicOpen_le g) := Subsingleton.elim _ _
  subst i
  let A := affineFormsSections s n hU
  let B := affineFormsSections s n (hU.basicOpen g)
  have H := formsOn_basicOpen (s := s) hU (show SectionRing s U from g) n
  let r := sectionRes s (homOfLE (X.basicOpen_le g))
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨ω, rfl⟩ := B.surjective y
    obtain ⟨m, ξ, hξ⟩ := H.1 ω
    refine ⟨m, A ξ, ?_⟩
    change (relativeForms s n).presheaf.map (homOfLE (X.basicOpen_le g)).op
      (formsOnToSections s n U ξ) = (r g) ^ m • B ω
    rw [formsOnToSections_res, ← hξ]
    exact B.map_smul _ _
  · intro x hx
    obtain ⟨ω, rfl⟩ := A.surjective x
    have e' := (formsOnToSections_res s n (homOfLE (X.basicOpen_le g)) ω).symm.trans hx
    have hzero : ExteriorDifferentials.map r n ω = 0 :=
      B.injective (e'.trans (B.map_zero).symm)
    obtain ⟨m, hm⟩ := H.2 ω hzero
    exact ⟨m, (A.map_smul (g ^ m) ω).symm.trans ((congrArg A hm).trans A.map_zero)⟩

private abbrev abelianForms (s : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s n)

private theorem forms_basicCover_exactAt {W : X.Opens} {l : ℕ} (γ : Fin l → Γ(X, W))
    (hW : IsAffineOpen W) (hcov : W ≤ ⨆ i, basicCover γ i) (p : ℕ) :
    (sheafCech (abelianForms s n) W (basicCover γ)).ExactAt p := by
  classical
  let M := relativeForms s n
  let D := sheafCech (abelianForms s n) W (basicCover γ)
  let I := coverInter W (basicCover γ)
  letI partModule (a : Finset (Fin l)) : Module Γ(X, W) (D.obj a) :=
    Module.compHom (Γ(M, I a)) (basicCoverRes γ a)
  have hres : ∀ {a b : Finset (Fin l)} (h : a ⊆ b) (r : Γ(X, W)) (x : D.obj a),
      D.res h (r • x) = r • D.res h x := by
    intro a b h r x
    let i : I b ⟶ I a := homOfLE (coverInter_anti (U := basicCover γ) h)
    change M.presheaf.map i.op (basicCoverRes γ a r • (show Γ(M, I a) from x)) =
      basicCoverRes γ b r • M.presheaf.map i.op x
    rw [M.map_smul]
    exact congrArg (fun c : Γ(X, I b) => c • M.presheaf.map i.op x) (basicCoverRes_comp γ h r)
  have hspan : Ideal.span (Set.range γ) = ⊤ := by
    refine (hW.self_le_iSup_basicOpen_iff (s := Set.range γ)).mp (hcov.trans (iSup_le fun i => ?_))
    exact le_iSup_of_le ⟨γ i, Set.mem_range_self i⟩ le_rfl
  have hI (a : Finset (Fin l)) : IsAffineOpen (I a) := by
    change IsAffineOpen (coverInter W (basicCover γ) a)
    rw [coverInter_basicCover γ a]
    exact hW.basicOpen _
  have e (j : Fin l) (a : Finset (Fin l)) :
      I (insert j a) = X.basicOpen (basicCoverRes γ a (γ j)) := by
    change coverInter W (basicCover γ) (insert j a) =
      X.basicOpen (X.presheaf.map (homOfLE (coverInter_le W (basicCover γ) a)).op (γ j))
    rw [coverInter_insert, Scheme.basicOpen_res, inf_comm]
    rfl
  refine D.exactAt_of_localized hres γ hspan ?_ ?_ p
  · intro j a y
    let h := Finset.subset_insert j a
    let i : I (insert j a) ⟶ I a := homOfLE (coverInter_anti (U := basicCover γ) h)
    obtain ⟨m, x, hxy⟩ := (relativeForms_localization s n (hI a) (basicCoverRes γ a (γ j))
      (e j a) i).1 y
    refine ⟨m, x, ?_⟩
    change M.presheaf.map i.op x = basicCoverRes γ (insert j a) ((γ j) ^ m) •
      (show Γ(M, I (insert j a)) from y)
    rw [map_pow, ← basicCoverRes_comp γ h (γ j)]
    exact hxy
  · intro j a x hx
    let h := Finset.subset_insert j a
    let i : I (insert j a) ⟶ I a := homOfLE (coverInter_anti (U := basicCover γ) h)
    obtain ⟨m, hm⟩ := (relativeForms_localization s n (hI a) (basicCoverRes γ a (γ j))
      (e j a) i).2 x hx
    refine ⟨m, ?_⟩
    change basicCoverRes γ a ((γ j) ^ m) • (show Γ(M, I a) from x) = 0
    rw [map_pow]
    exact hm

private theorem forms_cartanExact {U : X.Opens} (hU : IsAffineOpen U) :
    CartanExact (basicOpensOf U) (abelianForms s n) := by
  rintro _ ⟨f, rfl⟩ l V hVB hVU hcov p
  choose g hg using hVB
  let γ : Fin l → Γ(X, X.basicOpen f) :=
    fun i => X.presheaf.map (homOfLE (X.basicOpen_le f)).op (g i)
  have e : V = basicCover γ := by
    funext i
    rw [basicCover, Scheme.basicOpen_res, ← hg i]
    exact (inf_eq_right.mpr (hVU i)).symm
  subst V
  exact forms_basicCover_exactAt s n γ (hU.basicOpen f) hcov (p + 1)

/-- The abelian sheaf underlying the sheaf of relative forms is acyclic on affine opens. -/
theorem relativeForms_acyclicOn [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {U : X.Opens} (hU : IsAffineOpen U) : DeningerAcyclicOn.{w} (abelianForms s n) U :=
  fun q x => cartan_vanishing (cartanBasis_basicOpensOf hU) q _
    (forms_cartanExact s n hU) U ⟨1, (Scheme.basicOpen_one X).symm⟩ x

end GlobalTheory.SchemeCohomology
