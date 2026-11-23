import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedChartValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleNormalizedCharts

/-! Fixed rational points of an étale correspondence on normalized charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.PD GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k E L : Type} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
  [Algebra E L]

/-- Compare the value of the two rational pullbacks at an evaluation of a chart. -/
def IsFix (B : Subalgebra k L) (e : B →ₐ[k] k) (j₂ : E →ₐ[k] L) (B₀ : Subalgebra k E) : Prop :=
  ∀ b ∈ B₀, ∀ h₁ : algebraMap E L b ∈ B, Val B e (j₂ b) (e ⟨_, h₁⟩)

variable {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
  {c₁ c₂ : Y ⟶ Z} [IsFinite c₁] [IsDominant c₁] [IsDominant c₂]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)} [IsSeparated s]

/-- The algebraic fixed-point test on any nonempty normalized intersection
agrees with equality of the two images of the rational point. -/
theorem isFix_normalized_iff (hc₁ : c₁ ≫ s = t) (hc₂ : c₂ ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom →
      ∀ {d : ℕ} (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens)
        (_hZ : IsAffCover s U (rB k Z.functionField x))
        (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
        {I : Finset (Fin (d + 1))} (hI : I.Nonempty)
        (y : Y.BaseFieldPointOver k t) (hy : y.hom default ∈ I.inf (fun i => c₁ ⁻¹ᵁ U i)),
        IsFix (rB k Y.functionField x I) (hY.chartPointEquiv I hI ⟨y, hy⟩)
          (functionFieldPullbackAlg c₂ hc₂) (rB k Z.functionField x I) ↔
          y.hom ≫ c₁ = y.hom ≫ c₂ := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ _ _ _ _ _ h₁ d x U hZ hY I hI y hy
  let V (i : Fin (d + 1)) := c₁ ⁻¹ᵁ U i
  let W := I.inf U
  let W' := c₁ ⁻¹ᵁ W
  let pull : InfTopHom Z.Opens Y.Opens :=
    ⟨⟨fun U => c₁ ⁻¹ᵁ U, fun _ _ => c₁.preimage_inf⟩, c₁.preimage_top⟩
  have h : I.inf V = W' := (map_finset_inf pull I U).symm
  have hy' : y.hom default ∈ W' := h ▸ hy
  have hη' : genericPoint Y ∈ W' := h ▸ hY.ne I
  let iZ := hZ.sectionEquiv I hI
  let iY : SectionRing t W' ≃ₐ[k] rB k Y.functionField x I := h ▸ hY.sectionEquiv I hI
  let e := hY.chartPointEquiv I hI ⟨y, hy⟩
  have hi (P : Y.Opens) (hP : I.inf V = P) (hη : genericPoint Y ∈ P)
      (hyP : y.hom default ∈ P) (b : SectionRing t P) :
      let i : SectionRing t P ≃ₐ[k] rB k Y.functionField x I := hP ▸ hY.sectionEquiv I hI
      (i b : Y.functionField) = (Y.presheaf.germ P _ hη).hom b ∧
        e (i b) = affinePointEval y hyP b := by
    subst P
    exact ⟨rfl, hY.chartPointEquiv_eval I hI ⟨y, hy⟩ b⟩
  have hg (a : SectionRing t W') : (iY a : Y.functionField) =
      (Y.presheaf.germ W' _ hη').hom a := (hi W' h hη' hy' a).1
  have he (a : SectionRing t W') : e (iY a) = affinePointEval y hy' a :=
    (hi W' h hη' hy' a).2
  have hcompat (a : SectionRing s W) :
      rBPullback (L := Y.functionField) x I (iZ a) =
      iY (sectionPullback hc₁ W a) := by
    apply Subtype.ext
    rw [rBPullback_coe, hg, h₁, hZ.sectionEquiv_apply_coe]
    exact c₁.functionFieldPullback_germ W (hZ.ne I) a
  have hvalue (a : SectionRing s W) :
      e (rBPullback (L := Y.functionField) x I (iZ a)) =
        affinePointEval (mapBaseFieldPoint hc₁ y) hy' a := by
    rw [hcompat a, he]
    exact (affinePointEval_pullback hc₁ y W hy' a).symm
  rw [← fixed_iff_chart_values hc₁ (hZ.affine I hI) ((hZ.affine I hI).preimage c₁)
    y hy' (hZ.ne I) iY e hg he]
  constructor
  · intro H a
    have H' := H (iZ a).val (iZ a).2 (rBPullback (L := Y.functionField) x I (iZ a)).2
    change Val _ e (c₂.functionFieldPullback.hom (iZ a).val)
      (e (rBPullback (L := Y.functionField) x I (iZ a))) at H'
    exact (show (iZ a : Z.functionField) = _ from hZ.sectionEquiv_apply_coe I hI a) ▸
      hvalue a ▸ H'
  · intro H b hb hb'
    let a := iZ.symm ⟨b, hb⟩
    have ha : iZ a = ⟨b, hb⟩ := iZ.apply_symm_apply _
    have H' := H a
    rw [← hvalue a] at H'
    change Val _ _ (functionFieldPullbackAlg c₂ hc₂ (iZ a).val)
      (e (rBPullback (L := Y.functionField) x I (iZ a))) at H'
    rw [ha] at H'
    exact H'

end GlobalTheory.WH
