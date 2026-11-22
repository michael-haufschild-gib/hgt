import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.QuasicoherenceOnAffines
import GaloisForLFunctions.HTGeometry.AffineStructureSheafAcyclic

/-! Quasi-coherent sheaves have vanishing higher cohomology on affine opens. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry RHTower

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u w

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]

private abbrev abelianModuleSheaf (M : X.Modules) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

private theorem localizedSections {U V : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (e : V = X.basicOpen g) (i : V ⟶ U) :
    (∀ y : Γ(M, V), ∃ (m : ℕ) (x : Γ(M, U)),
      (X.presheaf.map i.op g) ^ m • y = M.presheaf.map i.op x) ∧
    ∀ x : Γ(M, U), M.presheaf.map i.op x = 0 → ∃ m : ℕ, g ^ m • x = 0 := by
  subst V
  have hi : i = homOfLE (X.basicOpen_le g) := Subsingleton.elim _ _
  subst i
  exact hasBasicOpenLocalization_of_isQuasicoherent M hU g

private theorem module_basicCover_exactAt {W : X.Opens} {l : ℕ} (γ : Fin l → Γ(X, W))
    (hW : IsAffineOpen W) (hcov : W ≤ ⨆ i, basicCover γ i) (p : ℕ) :
    (sheafCech (abelianModuleSheaf M) W (basicCover γ)).ExactAt p := by
  classical
  let D := sheafCech (abelianModuleSheaf M) W (basicCover γ)
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
    obtain ⟨m, x, hxy⟩ := (localizedSections M (hI a) (basicCoverRes γ a (γ j))
      (e j a) i).1 y
    refine ⟨m, x, ?_⟩
    change M.presheaf.map i.op x = basicCoverRes γ (insert j a) ((γ j) ^ m) •
      (show Γ(M, I (insert j a)) from y)
    rw [map_pow, ← basicCoverRes_comp γ h (γ j)]
    exact hxy.symm
  · intro j a x hx
    let h := Finset.subset_insert j a
    let i : I (insert j a) ⟶ I a := homOfLE (coverInter_anti (U := basicCover γ) h)
    obtain ⟨m, hm⟩ := (localizedSections M (hI a) (basicCoverRes γ a (γ j))
      (e j a) i).2 x hx
    refine ⟨m, ?_⟩
    change basicCoverRes γ a ((γ j) ^ m) • (show Γ(M, I a) from x) = 0
    rw [map_pow]
    exact hm

private theorem module_cartanExact {U : X.Opens} (hU : IsAffineOpen U) :
    CartanExact (basicOpensOf U) (abelianModuleSheaf M) := by
  rintro _ ⟨f, rfl⟩ l V hVB hVU hcov p
  choose g hg using hVB
  let γ : Fin l → Γ(X, X.basicOpen f) :=
    fun i => X.presheaf.map (homOfLE (X.basicOpen_le f)).op (g i)
  have e : V = basicCover γ := by
    funext i
    rw [basicCover, Scheme.basicOpen_res, ← hg i]
    exact (inf_eq_right.mpr (hVU i)).symm
  subst V
  exact module_basicCover_exactAt M γ (hU.basicOpen f) hcov (p + 1)

/-- The underlying abelian sheaf of a quasi-coherent module is acyclic on affine opens. -/
theorem quasicoherent_acyclicOn [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {U : X.Opens} (hU : IsAffineOpen U) : DeningerAcyclicOn.{w} (abelianModuleSheaf M) U :=
  fun q x => cartan_vanishing (cartanBasis_basicOpensOf hU) q _
    (module_cartanExact M hU) U ⟨1, (Scheme.basicOpen_one X).symm⟩ x

end GlobalTheory.SchemeCohomology
