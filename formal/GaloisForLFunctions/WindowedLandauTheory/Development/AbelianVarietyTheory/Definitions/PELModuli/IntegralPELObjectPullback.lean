import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELRelativeAmplePullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELWeilBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELTangentPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELTateTransport

/-! Integral PEL moduli objects and their prime-to-p level structures commute with base change. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
open GlobalTheory.UPel.HT GlobalTheory.LiePull
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPull

/-- Pullback preserves the polarization, order action, Lie conditions and Tate tower. -/
theorem exists_objMap_pull {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]
    {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) :
    ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  let A' : Over S' := (Over.pullback f).obj o.A
  let φ : A'.left ⟶ o.A.left := pφ f o.A
  let φ₂ : (A' ⊗ A').left ⟶ (o.A ⊗ o.A).left := pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := isSquare f o.A
  have hab : IsAbelianScheme A' := o.ab.pullback f
  letI : IsCommMonObj A' := hab.comm
  let a' : OActN D.O A' := o.act.pullback f
  have hact (c : D.O) : (a'.act c).left ≫ φ = φ ≫ (o.act.act c).left :=
    pullback_map_left_fst' f (o.act.act c)
  let P' := o.P.pull φ₂
  have hP' : P'.IsLB := o.isLB.pull φ₂
  have iso : LBIso P' (o.P.pull φ₂) := hP'.gen_refl
  have dg := SiegelPull.diag_iso sq o.isLB hP' iso
  obtain ⟨eK, heK, hK⟩ := o.kerP
  have hid : Over.Hom.left (𝟙 A') ≫ φ = φ ≫ Over.Hom.left (𝟙 o.A) := by
    change 𝟙 _ ≫ φ = φ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  let eta' := fun y => pullSections pb (o.eta y)
  let o' : Obj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := a'
      P := P'
      isLB := hP'
      rig₁ := SiegelPull.pull_axis_gen f o.A o.isLB (1 : A' ⟶ A') (𝟙 A') 1 (𝟙 o.A)
        (one_left_pφ f o.A) hid o.rig₁
      rig₂ := SiegelPull.pull_axis_gen f o.A o.isLB (𝟙 A') (1 : A' ⟶ A') (𝟙 o.A) 1
        hid (one_left_pφ f o.A) o.rig₂
      symm := SiegelPull.pull_symmetric f o.A o.isLB o.symm
      ample := by
        letI := hab.proper
        exact PolPull.relAmple_baseChange pb.1 (o.isLB.pull _) (hP'.pull _) dg inferInstance inferInstance o.ample
      kerP := ⟨eK, heK, SiegelPull.kernel_pullback pb sq o.isLB hP' iso eK hK⟩
      rosati := fun c => SiegelPull.pull_adjoint f o.A o.act o.isLB c _ (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ : ∃ e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ o.A),
            ∀ v, (e v).left = v.left ≫ φ :=
          exists_pushEquiv pb (epsPtR x) (epsPtR (x ≫ f)).hom (Category.assoc _ _ _).symm
        have hβ : (x ≫ f) ≫ s = spMap β := (Category.assoc _ _ _).trans hx
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) hβ (e v)
          ((isTanScal_iff_of_pushEquiv pb o.act a' hact x e he _ _ v).mp hv)
        refine ⟨fun i => e.symm (w i), fun i c => ?_, e.injective ?_⟩
        · apply (isTanScal_iff_of_pushEquiv pb o.act a' hact x e he _ _ (e.symm (w i))).mpr
          rw [e.apply_symm_apply]
          exact hw i c
        · rw [hvw, map_list_prod, List.map_ofFn]
          simp only [Function.comp_def, e.apply_symm_apply]
      lieRank := fun k _ _ x β hx i => (lieMult_pull pb
        (o.act.restrict (algebraMap (𝓞 D.F) D.O)) (a'.restrict (algebraMap (𝓞 D.F) D.O))
        (fun c => hact _) x (β.comp (b.t i)) D.m).mpr
          (o.lieRank k (x ≫ f) β ((Category.assoc _ _ _).trans hx) i)
      eta := eta'
      eta_add := fun y z => (congrArg (pullSections pb) (o.eta_add y z)).trans (map_mul _ _ _)
      eta_lin := fun c y => (congrArg (pullSections pb) (o.eta_lin c y)).trans
        (pullSections_comp pb (o.eta y) (hact c))
      eta_ker := fun y => (congrArg (pullSections pb) (o.eta_ker y)).trans (map_one _)
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β ((Category.assoc _ _ _).trans hx)
        obtain ⟨u, hu⟩ := exists_pushEquiv pb (Over.mk x) (x ≫ f) rfl
        have he (c : D.O) (g : Over.mk x ⟶ A') : u (g ≫ a'.act c) = u g ≫ o.act.act c := by
          apply Over.OverMorphism.ext
          simp only [hu, Over.comp_left, Category.assoc, hact]
          exact (Category.assoc _ _ _).symm
        have hpair (n : ℕ) (g g' : Over.mk x ⟶ A') (z : kˣ) :=
          (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (o.isLB.pull _) (hP'.pull _)
            pb dg (Over.mk x) n g g' (u g) (u g') (unitOn z) (hu g) (hu g')).mpr
        refine ⟨I.transport u he hpair, fun y => u.injective ?_⟩
        change u (toUnit _ ≫ eta' y) = u (u.symm (I.ev N y))
        rw [u.apply_symm_apply, ← hI y]
        exact Over.OverMorphism.ext ((hu _).trans (pullSections_eval pb (Over.mk x) (o.eta y))) }
  refine ⟨o', ⟨?_⟩⟩
  exact
    { φ := φ
      φ₂ := φ₂
      cart := pb
      sq := sq
      act := hact
      pol := iso
      eta := fun y => pullSections_left pb (o.eta y) }

end GlobalTheory.HTPull
