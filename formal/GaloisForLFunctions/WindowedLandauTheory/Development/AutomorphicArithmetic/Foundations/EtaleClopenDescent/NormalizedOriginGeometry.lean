import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedCotangentMatrix
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedChartRows
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedRowCotangent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CotangentDeterminants
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace

/-! Pinned projective coordinates pull back to origin fibre points.
At a fixed point the normalized rows give the geometric cotangent determinants. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.PD GlobalTheory.SchemeCohomology GlobalTheory.WH

namespace GlobalTheory.SchemeCohomology

private theorem sectionEquiv_coe_of_eq {k ι : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {s : X ⟶ Spec (CommRingCat.of k)} [Algebra k X.functionField]
    {U : ι → X.Opens} {B : Finset ι → Subalgebra k X.functionField}
    (h : IsAffCover s U B) {I : Finset ι} (hI : I.Nonempty)
    {W : X.Opens} (hW : I.inf U = W) (hη : genericPoint X ∈ W) (a : SectionRing s W) :
    (((hW ▸ h.sectionEquiv I hI : SectionRing s W ≃ₐ[k] B I) a) : X.functionField) =
      (X.presheaf.germ W _ hη).hom a := by
  subst W
  rfl

private theorem chartPointEquiv_eval_of_eq {k ι : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {s : X ⟶ Spec (CommRingCat.of k)} [Algebra k X.functionField]
    {U : ι → X.Opens} {B : Finset ι → Subalgebra k X.functionField}
    (h : IsAffCover s U B) {I : Finset ι} (hI : I.Nonempty)
    (y : X.BaseFieldPointOver k s) (hy : y.hom default ∈ I.inf U)
    {W : X.Opens} (hW : I.inf U = W) (a : SectionRing s W) :
    h.chartPointEquiv I hI ⟨y, hy⟩ ((hW ▸ h.sectionEquiv I hI : SectionRing s W ≃ₐ[k] B I) a) =
      affinePointEval y (hW ▸ hy) a := by
  subst W
  exact h.chartPointEquiv_eval I hI ⟨y, hy⟩ a

/-- A point over the base is determined by its underlying scheme map. -/
theorem baseFieldPoint_eq_of_hom_eq {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of k)} {y z : X.BaseFieldPointOver k s}
    (h : y.hom = z.hom) : y = z := by
  cases y
  cases z
  cases h
  rfl

variable {k : Type} [Field k] {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z} [IsFinite c₁] [IsDominant c₁]
  {d : ℕ}

/-- Vanishing of the origin coordinate ratios at the image point
pulls back to vanishing of the normalized origin coordinates. -/
theorem originValues_pullback_of_pinning (h₁ : c₁ ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom →
      ∀ (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens),
      ∀ (hZ : IsAffCover s U (rB k Z.functionField x))
        (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
        (y : Y.BaseFieldPointOver k t)
        (hy : (mapBaseFieldPoint h₁ y).hom default ∈ U 0),
        (∀ (j : Fin d) (hη : genericPoint Z ∈ U 0) (a : SectionRing s (U 0)),
          (Z.presheaf.germ (U 0) _ hη).hom a = algebraMap F Z.functionField (x j.succ / x 0) →
            affinePointEval (mapBaseFieldPoint h₁ y) hy a = 0) →
        ∃ hy₀ : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf (fun i => c₁ ⁻¹ᵁ U i),
          ∀ j : Fin d, hY.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy₀⟩
            ⟨_, tco_mem k Y.functionField x j⟩ = 0 := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ _ _ _ _ _ hff x U hZ hY y hy hz
  let I : Finset (Fin (d + 1)) := {0}
  let hI : I.Nonempty := Finset.singleton_nonempty 0
  let V := c₁ ⁻¹ᵁ U 0
  let hU : I.inf U = U 0 := Finset.inf_singleton
  let hV : I.inf (fun i => c₁ ⁻¹ᵁ U i) = V := Finset.inf_singleton
  let eZ : SectionRing s (U 0) ≃ₐ[k] rB k Z.functionField x I := hU ▸ hZ.sectionEquiv I hI
  let eY : SectionRing t V ≃ₐ[k] rB k Y.functionField x I := hV ▸ hY.sectionEquiv I hI
  have hη : genericPoint Z ∈ U 0 := hU ▸ hZ.ne I
  have hη' : genericPoint Y ∈ V := hV ▸ hY.ne I
  have hy' : y.hom default ∈ V := hy
  have hy₀ : y.hom default ∈ I.inf (fun i => c₁ ⁻¹ᵁ U i) := hV.symm ▸ hy'
  let ev := hY.chartPointEquiv I hI ⟨y, hy₀⟩
  refine ⟨hy₀, fun j => ?_⟩
  let a := eZ.symm ⟨_, tco_mem k Z.functionField x j⟩
  have ha : (Z.presheaf.germ (U 0) _ hη).hom a =
      algebraMap F Z.functionField (x j.succ / x 0) :=
    (sectionEquiv_coe_of_eq hZ hI hU hη a).symm.trans
      (congrArg Subtype.val (eZ.apply_symm_apply _))
  have hcomp : eY (sectionPullback h₁ (U 0) a) = (⟨_, tco_mem k Y.functionField x j⟩ : rB k Y.functionField x I) := by
    apply Subtype.ext
    calc
      _ = (Y.presheaf.germ V _ hη').hom (sectionPullback h₁ (U 0) a) :=
        sectionEquiv_coe_of_eq hY hI hV hη' _
      _ = c₁.functionFieldPullback.hom ((Z.presheaf.germ (U 0) _ hη).hom a) :=
        (c₁.functionFieldPullback_germ (U 0) hη a).symm
      _ = _ := by rw [ha, ← hff, ← IsScalarTower.algebraMap_apply]
  change ev ⟨_, tco_mem k Y.functionField x j⟩ = 0
  rw [← hcomp]
  exact (chartPointEquiv_eval_of_eq hY hI y hy₀ hV _).trans
    ((affinePointEval_pullback h₁ y (U 0) hy a).symm.trans (hz j hη a ha))

variable [Etale c₁] [IsFinite c₂] [Etale c₂] [IsDominant c₂]
  [SmoothOfRelativeDimension d t] [IsSeparated s]

/-- The normalized coefficients of the second pullback have the same
determinants as a matrix obtained from affine differential values. -/
theorem exists_normalizedOriginRows_matching_tangent (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom →
      ∀ (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens),
      ∀ (hZ : IsAffCover s U (rB k Z.functionField x))
        (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
        (hL : IsFinCover k Y.functionField x)
        [IsReduced ((rB k Y.functionField x {0}) ⧸ originIdeal k Y.functionField x)],
        let j₂ := functionFieldPullbackAlg c₂ h₂
        let B := rB k Y.functionField x {0}
        ∀ (f : OriginFibrePoint k Y.functionField x)
          (hf : IsFix B f.1 j₂ (rB k Z.functionField x {0})) (M : Matrix (Fin d) (Fin d) k),
          W1.IsTan d h₁ h₂ ((hY.chartPointEquiv {0} (Finset.singleton_nonempty 0)).symm f.1).1 M →
          ∃ A : Matrix (Fin d) (Fin d) k,
            (∀ m, ∃ (c : B) (g : Fin d → B), f.1 c ≠ 0 ∧
              (c : Y.functionField) * j₂ (algebraMap F Z.functionField (x m.succ / x 0)) =
                ∑ l, (g l : Y.functionField) * algebraMap F Y.functionField (x l.succ / x 0) ∧
              ∀ l, f.1 (g l) = f.1 c * A m l) ∧
            (1 - A).det = (1 - M).det ∧
            (1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det =
              (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C).det := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ _ _ _ _ _ hff x U hZ hY hL hred j₂ B f hf M hTan
  let I : Finset (Fin (d + 1)) := {0}
  let hI : I.Nonempty := Finset.singleton_nonempty 0
  let V := c₁ ⁻¹ᵁ U 0
  let hU : I.inf U = U 0 := Finset.inf_singleton
  let hV : I.inf (fun i => c₁ ⁻¹ᵁ U i) = V := Finset.inf_singleton
  let eZ : SectionRing s (U 0) ≃ₐ[k] rB k Z.functionField x I := hU ▸ hZ.sectionEquiv I hI
  let eY : SectionRing t V ≃ₐ[k] B := hV ▸ hY.sectionEquiv I hI
  let p := (hY.chartPointEquiv I hI).symm f.1
  let y := p.1
  have he : hY.chartPointEquiv I hI p = f.1 := (hY.chartPointEquiv I hI).apply_symm_apply f.1
  have hfix : y.hom ≫ c₁ = y.hom ≫ c₂ :=
    (isFix_normalized_iff h₁ h₂ hff x U hZ hY hI y p.2).mp (he.symm ▸ hf)
  have hfix' : mapBaseFieldPoint h₁ y = mapBaseFieldPoint h₂ y := baseFieldPoint_eq_of_hom_eq hfix
  have hη : genericPoint Z ∈ U 0 := hU ▸ hZ.ne I
  have hη' : genericPoint Y ∈ V := hV ▸ hY.ne I
  have hy₁ : y.hom default ∈ V := hV ▸ p.2
  have hy₂ : y.hom default ∈ c₂ ⁻¹ᵁ U 0 := by
    change c₂ (y.hom default) ∈ U 0
    have heval : c₁ (y.hom default) = c₂ (y.hom default) :=
      congrArg (fun f : Spec (CommRingCat.of k) ⟶ Z => f default) hfix
    exact heval ▸ hy₁
  have hW : IsAffineOpen (U 0) := hU ▸ hZ.affine I hI
  have hEval (a : SectionRing t V) : f.1 (eY a) = affinePointEval y hy₁ a := by
    rw [← he]
    exact chartPointEquiv_eval_of_eq hY hI y p.2 hV a
  obtain ⟨A, hA⟩ := exists_fixedChartRows hL f.1 f.2 j₂ hf
  obtain ⟨b, hb⟩ := exists_cotangentBasis_of_normalizedRows h₁ h₂ hW hη y hy₁ hy₂ hfix' hff
    eZ eY (sectionEquiv_coe_of_eq hZ hI hU hη) (sectionEquiv_coe_of_eq hY hI hV hη')
    hL f.1 hEval f.2 A hA
  obtain ⟨a, ha⟩ := hTan.exists_cotangentBasis hfix' hW hy₁ hy₂
  let T := (fixedCotangentEquiv h₁ h₂ y hfix' hW hy₁ hy₂).toLinearMap
  obtain ⟨hA₀, hA₁⟩ := det_eq_of_cotangentRows b a T A hb
  obtain ⟨hM₀, hM₁⟩ := det_eq_of_cotangentRows a a T M ha
  exact ⟨A, hA, hA₀.trans hM₀.symm, hA₁.trans hM₁.symm⟩

end GlobalTheory.SchemeCohomology
