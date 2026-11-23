import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFibreParameters
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalPointCotangent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalCotangentBasis

/-! First-order expansions in normalized origin coordinates represent
the fixed-point cotangent map of the étale correspondence. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry GlobalTheory.PD GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z} [IsFinite c₁] [Etale c₁] [IsDominant c₁]
  [IsFinite c₂] [Etale c₂] [IsDominant c₂]
  [Algebra k Z.functionField] [Algebra k Y.functionField]
  [Algebra F Z.functionField] [Algebra F Y.functionField] [Algebra Z.functionField Y.functionField]
  [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
  [IsScalarTower F Z.functionField Y.functionField]
  {d : ℕ} [SmoothOfRelativeDimension d t] {x : Fin (d + 1) → F}

/-- The cleared rows on a reduced normalized origin chart are the rows
of the fixed-point cotangent map in its origin-coordinate basis. -/
theorem exists_cotangentBasis_of_normalizedRows
    (hc₁ : c₁ ≫ s = t) (hc₂ : c₂ ≫ s = t)
    {U : Z.Opens} (hU : IsAffineOpen U) (hη : genericPoint Z ∈ U)
    (y : Y.BaseFieldPointOver k t) (hy₁ : y.hom default ∈ c₁ ⁻¹ᵁ U)
    (hy₂ : y.hom default ∈ c₂ ⁻¹ᵁ U)
    (hfix : mapBaseFieldPoint hc₁ y = mapBaseFieldPoint hc₂ y)
    (hff : algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom)
    (iZ : SectionRing s U ≃ₐ[k] rB k Z.functionField x {0})
    (iY : SectionRing t (c₁ ⁻¹ᵁ U) ≃ₐ[k] rB k Y.functionField x {0})
    (hgZ : ∀ a, (iZ a : Z.functionField) = (Z.presheaf.germ U _ hη).hom a)
    (hgY : ∀ a, (iY a : Y.functionField) =
      (Y.presheaf.germ (c₁ ⁻¹ᵁ U) (genericPoint Y)
        (by simpa [c₁.map_genericPoint_of_isDominant] using hη)).hom a)
    (hL : IsFinCover k Y.functionField x)
    [IsReduced ((rB k Y.functionField x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem k Y.functionField x j⟩ : rB k Y.functionField x {0})))]
    (e : rB k Y.functionField x {0} →ₐ[k] k)
    (he : ∀ a, e (iY a) = affinePointEval y hy₁ a)
    (hz : ∀ j, e ⟨_, tco_mem k Y.functionField x j⟩ = 0)
    (M : Matrix (Fin d) (Fin d) k)
    (hM : ∀ m, ∃ (c : rB k Y.functionField x {0}) (g : Fin d → rB k Y.functionField x {0}),
      e c ≠ 0 ∧
      (c : Y.functionField) * c₂.functionFieldPullback.hom
        (algebraMap F Z.functionField (x m.succ / x 0)) =
          ∑ l, (g l : Y.functionField) * algebraMap F Y.functionField (x l.succ / x 0) ∧
      ∀ l, e (g l) = e c * M m l) :
    ∃ b : Module.Basis (Fin d) k (CotangentAt y), ∀ m,
      fixedCotangentEquiv hc₁ hc₂ y hfix hU hy₁ hy₂ (b m) = ∑ l, M m l • b l := by
  let V := c₁ ⁻¹ᵁ U
  let S := SectionRing t V
  let B := rB k Y.functionField x {0}
  let τ (j : Fin d) : B := ⟨_, tco_mem k Y.functionField x j⟩
  let a (j : Fin d) : SectionRing s U := iZ.symm ⟨_, tco_mem k Z.functionField x j⟩
  have ha (j : Fin d) : (Z.presheaf.germ U _ hη).hom (a j) =
      algebraMap F Z.functionField (x j.succ / x 0) := by
    rw [← hgZ, show iZ (a j) = ⟨_, tco_mem k Z.functionField x j⟩ from iZ.apply_symm_apply _]
  let u (j : Fin d) : S := sectionPullback hc₁ U (a j)
  have hu (j : Fin d) : iY (u j) = τ j := by
    apply Subtype.ext
    change (iY (sectionPullback hc₁ U (a j)) : Y.functionField) =
      algebraMap F Y.functionField (x j.succ / x 0)
    exact (hgY _).trans ((c₁.functionFieldPullback_germ U hη (a j)).symm.trans (by
      rw [ha]
      exact (RingHom.congr_fun hff.symm _).trans
        (IsScalarTower.algebraMap_apply F Z.functionField Y.functionField _).symm))
  let ε := affinePointEval y hy₁
  have hε (j : Fin d) : ε (u j) = 0 := ((he _).symm.trans (congrArg e (hu j))).trans (hz j)
  have hreg (v : S) (hv : ε v = 0) :
      ∃ (c : S) (g : Fin d → S), ε c ≠ 0 ∧ c * v = ∑ j, g j * u j := by
    obtain ⟨c, g, hc, hg⟩ := exists_regular_parameters_of_reduced_quotient hL e (iY v)
      ((he v).trans hv)
    refine ⟨iY.symm c, fun j => iY.symm (g j), ?_, ?_⟩
    · rw [← he, iY.apply_symm_apply, hc]
      exact one_ne_zero
    · apply iY.injective
      simpa only [map_mul, map_sum, iY.apply_symm_apply, hu] using hg
  have hV := hU.preimage c₁
  obtain ⟨q⟩ := nonempty_affineCotangentFibreBasis t d hV y hy₁
  have hdim : Module.finrank k (CotangentFibre ε) = d :=
    (Module.finrank_eq_card_basis q).trans (Fintype.card_fin d)
  obtain ⟨b₀, hb₀⟩ := exists_basis_of_cotangentFibre_parameters ε u hε hdim hreg
  let b := b₀.map (chartCotangentEquiv y hV hy₁)
  have hb (j : Fin d) : b j = cotangentAtD y (sectionGermAlg t hy₁ (u j)) := by
    rw [Module.Basis.map_apply, hb₀, chartCotangentEquiv_D]
  let P := y.hom default
  let j := (stalkToFunctionField P).hom
  letI := stalkBaseAlgebra t P
  let p : B →ₐ[k] Y.presheaf.stalk P := (sectionGermAlg t hy₁).comp iY.symm.toAlgHom
  let ε' := localPointEvalAlg y
  have hp (v : B) : j (p v) = v := by
    change j ((Y.presheaf.germ V P hy₁).hom (iY.symm v)) = v
    rw [show j ((Y.presheaf.germ V P hy₁).hom (iY.symm v)) = (iY (iY.symm v) : Y.functionField)
      from (ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hy₁
        (genericPoint_specializes P)) (iY.symm v)).trans (hgY _).symm, iY.apply_symm_apply]
  have hpe (v : B) : ε' (p v) = e v :=
    (localPointEvalAlg_germ y hy₁ (iY.symm v)).trans ((he _).symm.trans
      (congrArg e (iY.apply_symm_apply v)))
  have hpu (l : Fin d) : p (τ l) = sectionGermAlg t hy₁ (u l) := by
    change sectionGermAlg t hy₁ (iY.symm (τ l)) = _
    rw [← hu, iY.symm_apply_apply]
  let w (m : Fin d) := sectionGermAlg t hy₂ (sectionPullback hc₂ U (a m))
  have hw (m : Fin d) : j (w m) = c₂.functionFieldPullback.hom
      (algebraMap F Z.functionField (x m.succ / x 0)) := by
    rw [← ha m]
    exact (ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hy₂
      (genericPoint_specializes P)) _).trans (c₂.functionFieldPullback_germ U hη (a m)).symm
  have hwe (m : Fin d) : ε' (w m) = 0 := by
    have eq := congrArg (fun z : Z.BaseFieldPointOver k s => z.hom) hfix
    calc
      _ = affinePointEval y hy₂ (sectionPullback hc₂ U (a m)) :=
        localPointEvalAlg_germ y hy₂ _
      _ = pointEval (y.hom ≫ c₂) U hy₂ (a m) := (affinePointEval_pullback hc₂ y U hy₂ _).symm
      _ = pointEval (y.hom ≫ c₁) U hy₁ (a m) := pointEval_congr eq.symm U hy₂ hy₁ _
      _ = ε (u m) := affinePointEval_pullback hc₁ y U hy₁ _
      _ = 0 := hε m
  refine ⟨b, fun m => ?_⟩
  rw [hb, fixedCotangentEquiv_D hc₁ hc₂ y hfix hU hy₁ hy₂ (a m)]
  obtain ⟨c, g, hc, hcg, hcoeff⟩ := hM m
  have heq : p c * w m = ∑ l, p (g l) * p (τ l) := by
    apply stalkToFunctionField_injective P
    change j (p c * w m) = j (∑ l, p (g l) * p (τ l))
    simpa only [map_sum, map_mul, hp, hw] using hcg
  have hd := smul_cotangentFibreD_eq_sum ε' (fun l => p (τ l)) (fun l => p (g l))
    (w m) (p c) (hwe m) (fun l => (hpe (τ l)).trans (hz l)) heq
  have hb' (l : Fin d) : cotangentFibreD ε' (p (τ l)) = b l :=
    (congrArg (cotangentAtD y) (hpu l)).trans (hb l).symm
  simp only [hpe, hcoeff, mul_smul, hb'] at hd
  rw [← Finset.smul_sum] at hd
  exact (smul_right_injective _ hc) hd

end GlobalTheory.WH
