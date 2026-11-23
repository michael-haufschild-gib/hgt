import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverCechPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverCechSubcover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverCechTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleJoinedCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveHodgeFiniteness

/-! For a finite étale correspondence, the pullback of a regular rational
cocycle extends to the joined cover with its right components prescribed.
Tracing its left components computes the correspondence on Hodge cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH
open scoped GlobalTheory.CechDR

namespace GlobalTheory.SchemeCohomology

private theorem map_mem_cycles {k M N : Type} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {C : Cx k M} {D : Cx k N} {g : M →ₗ[k] N} (hg : IsMap C D g)
    {n : ℤ} {a : M} (ha : a ∈ C.Z n) : g a ∈ D.Z n := by
  obtain ⟨hC, hD⟩ := hg n a ha.1
  exact ⟨hC, LinearMap.mem_ker.mpr
    (hD.symm.trans ((congrArg g (LinearMap.mem_ker.mp ha.2)).trans (map_zero g)))⟩

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z] {c₁ c₂ : Y ⟶ Z}
  [IsFinite c₁] [IsFinite c₂] [Etale c₁] [Etale c₂] [IsDominant c₁] [IsDominant c₂]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {d : ℕ} [Smooth s] [SmoothOfRelativeDimension d t] [IsSeparated s]

/-- An exact lift of the pulled-back cocycle computes the geometric
correspondence by tracing the cocycle on the left subcover. -/
theorem exists_joinedChartCocycle (h₁ : c₁ ≫ s = t) (h₂ : c₂ ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := c₁.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower h₁
    letI := finiteDimensional_functionFieldPullback c₁
    letI := functionFieldPullback_etale (f := c₁) s
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower F Z.functionField Y.functionField]
      (x : Fin (d + 1) → F) {U : Fin (d + 1) → Z.Opens},
    IsFinCover k Z.functionField x → ∀ h : IsAffCover s U (rB k Z.functionField x),
    ∀ (p q : ℕ),
    let j₂ := functionFieldPullbackAlg c₂ h₂
    let C := cech (fun I => omB k Z.functionField (rB k Z.functionField x I) p)
    let D := cech (fun I => omB k Y.functionField (RY x j₂ (lft I) (rgt I)) p)
    ∀ b : C.Z q, ∃ bt : D.Z q,
      (∀ J, bt.val (uni ∅ J) = pullbackDR j₂ (b.val J)) ∧
      ∃ a : C.Z q,
        (∀ I, a.val I = traceDR k Z.functionField Y.functionField (bt.val (uni I ∅))) ∧
        h.hodgeCechEquiv p q
          (hodgeTrace h₁ p q (hodgePullback h₂ p q ((h.hodgeCechEquiv p q).symm (Submodule.Quotient.mk b)))) =
          Submodule.Quotient.mk a := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := c₁.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower h₁
  letI := finiteDimensional_functionFieldPullback c₁
  letI := functionFieldPullback_etale (f := c₁) s
  intro F _ _ _ _ _ _ _ x U hfin h p q j₂ C D b
  have hff : algebraMap Z.functionField Y.functionField = c₁.functionFieldPullback.hom := rfl
  obtain ⟨-, hL⟩ := isFinCover_pullback h₁ hff x U hfin h
  have hR := isAffCover_pullbackChartAlgebra d h₂ U (rB k Z.functionField x) h
  have hD := isAffCover_joined_normalized h₁ h₂ hff x U hfin h
  let ι := Fin (d + 1)
  let B (I : Finset (ι ⊕ₗ ι)) := omB k Y.functionField (RY x j₂ (lft I) (rgt I)) p
  let L (I : Finset ι) := omB k Y.functionField (rB k Y.functionField x I) p
  let R (I : Finset ι) := omB k Y.functionField (R2 x j₂ I) p
  have eL (I : Finset ι) (_ : I.Nonempty) :
      RY x j₂ (lft (I.map joinedLeft.toEmbedding)) (rgt (I.map joinedLeft.toEmbedding)) =
        rB k Y.functionField x I := by
    rw [map_joinedLeft, lft_uni, rgt_uni]
    change rB k Y.functionField x I ⊔ R2 x j₂ ∅ = _
    rw [pullbackChartAlgebra_rB_empty, sup_bot_eq]
  have eR (I : Finset ι) (_ : I.Nonempty) :
      RY x j₂ (lft (I.map joinedRight.toEmbedding)) (rgt (I.map joinedRight.toEmbedding)) =
        R2 x j₂ I := by
    rw [map_joinedRight, lft_uni, rgt_uni]
    change rB k Y.functionField x ∅ ⊔ R2 x j₂ I = _
    rw [rB_empty, bot_sup_eq]
  have eL' I hI : B (I.map joinedLeft.toEmbedding) = L I := congrArg (fun A => omB k _ A p) (eL I hI)
  have eR' I hI : B (I.map joinedRight.toEmbedding) = R I := congrArg (fun A => omB k _ A p) (eR I hI)
  let l := restrictIndex (k := k) (M := DR k Y.functionField) (joinedLeft (ι := ι) (κ := ι))
  let r := restrictIndex (k := k) (M := DR k Y.functionField) (joinedRight (ι := ι) (κ := ι))
  have hl : IsMap D (cech L) l := isMap_restrictIndex B L joinedLeft fun I hI => (eL' I hI).le
  have hr : IsMap D (cech R) r := isMap_restrictIndex B R joinedRight fun I hI => (eR' I hI).le
  have hleft (z : HodgeCohomology t p q) :
      D.hmap (cech L) l hl q (hD.hodgeCechEquiv p q z) = hL.hodgeCechEquiv p q z :=
    hD.hodgeCechEquiv_subcover joinedLeft hL eL p q z
  have hright (z : HodgeCohomology t p q) :
      D.hmap (cech R) r hr q (hD.hodgeCechEquiv p q z) = hR.hodgeCechEquiv p q z :=
    hD.hodgeCechEquiv_subcover joinedRight hR eR p q z
  have hright' : D.hmap (cech R) r hr q =
      (hR.hodgeCechEquiv p q).toLinearMap.comp (hD.hodgeCechEquiv p q).symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    obtain ⟨u, rfl⟩ := (hD.hodgeCechEquiv p q).surjective z
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hright u
  have hbij : Function.Bijective (D.hmap (cech R) r hr q) := by
    rw [hright']
    exact (hR.hodgeCechEquiv p q).bijective.comp (hD.hodgeCechEquiv p q).symm.bijective
  let P := mapCochain (ι := ι) (pullbackDR j₂).toLinearMap
  have hB (I : Finset ι) (_ : I.Nonempty) : (rB k Z.functionField x I).map j₂ ≤ R2 x j₂ I := by
    intro a ha
    exact isIntegral_algebraMap (x := (⟨a, ha⟩ : (rB k Z.functionField x I).map j₂))
  have hP : IsMap C (cech R) P := isMap_mapCochain _ R _ fun I hI =>
    IsDRMap.regularForms k (isDRMap_pullbackDR k j₂) (hB I hI) p
  obtain ⟨bt, hbt⟩ := exists_cycleLift_restrictIndex B R joinedRight eR'
    (hD.isCechComplex p) q hbij.surjective ⟨P b.val, map_mem_cycles hP b.property⟩
  let z := (h.hodgeCechEquiv p q).symm (Submodule.Quotient.mk b)
  let w := hodgePullback h₂ p q z
  have hPclass : hR.hodgeCechEquiv p q w = C.hmap (cech R) P hP q (Submodule.Quotient.mk b) := by
    have he := h.hodgeCechEquiv_pullback hR h₂ j₂ (functionFieldPullbackAlg_germ c₂ h₂) hB p q z
    simpa only [z, LinearEquiv.apply_symm_apply] using he
  have hbtclass : (Submodule.Quotient.mk bt : D.H q) = hD.hodgeCechEquiv p q w := by
    apply hbij.injective
    rw [hright, hPclass]
    exact congrArg (Submodule.Quotient.mk :
      (cech R).Z q → (cech R).H q) (Subtype.ext hbt)
  let T := mapCochain (ι := ι) (traceDR k Z.functionField Y.functionField)
  have hT : IsMap (cech L) C T := isMap_mapCochain L _ _ fun I hI =>
    IsAffCover.traceDR_mem_regularForms h₁ h hL hI hI (preimage_coverInter c₁.base ⊤ U I) p
  have hbL : l bt.val ∈ (cech L).Z q := map_mem_cycles hl bt.property
  let a : C.Z q := ⟨T (l bt.val), map_mem_cycles hT hbL⟩
  refine ⟨bt, ?_, a, ?_, ?_⟩
  · intro J
    have he := congrFun hbt J
    change r bt.val J = P b.val J at he
    simpa only [r, restrictIndex_apply, map_joinedRight, P, mapCochain_apply] using he
  · intro I
    change T (l bt.val) I = _
    rw [T, mapCochain_apply, l, restrictIndex_apply, map_joinedLeft]
  · calc
      _ = (cech L).hmap C T hT q (hL.hodgeCechEquiv p q w) :=
        IsAffCover.hodgeCechEquiv_trace h₁ h hL p q w
      _ = (cech L).hmap C T hT q (D.hmap (cech L) l hl q (Submodule.Quotient.mk bt)) :=
        congrArg ((cech L).hmap C T hT q) ((hleft w).symm.trans
          (congrArg (D.hmap (cech L) l hl q) hbtclass.symm))
      _ = _ := rfl

end GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

open GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of k)} [Algebra k X.functionField] [Smooth s]
  {ι : Type} [LinearOrder ι] {U : ι → X.Opens} {A : Finset ι → Subalgebra k X.functionField}

/-- On a projective scheme, the regular rational Čech cohomology is
finite-dimensional in each bidegree. -/
theorem IsAffCover.finiteDimensional_rationalCech_of_projective (h : IsAffCover s U A)
    (hs : UpperTheory.Cb.IsProjOver s) (p q : ℕ) :
    FiniteDimensional k ((cech (fun I => omB k X.functionField (A I) p)).H q) := by
  letI := hodgeCohomology_finite_of_projective s hs p q
  exact Module.Finite.equiv (h.hodgeCechEquiv p q)

end GlobalTheory.PD
