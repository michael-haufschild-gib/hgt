import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IntegralClosureFiniteImage
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothNormalCharts

/-! Finite pullback of a smooth affine cover is computed by integral
closure in the source function field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {k E L : Type} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]

/-- Normalize the image of a chart algebra in an extension field. -/
abbrev pullbackChartAlgebra (j : E →ₐ[k] L) (B : Subalgebra k E) : Subalgebra k L :=
  (integralClosure (B.map j) L).restrictScalars k

variable {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z] {c : Y ⟶ Z}
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

private theorem generic_mem_preimage_of_dominant [IsDominant c] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) : genericPoint Y ∈ c ⁻¹ᵁ U := by
  change c (genericPoint Y) ∈ U
  rwa [c.map_genericPoint_of_isDominant]

/-- Over a nonempty affine chart, the finite inverse image is the integral
closure of the image of its section algebra in the source function field. -/
theorem pullbackChartAlgebra_eq_range [IsFinite c] [IsDominant c] (d : ℕ)
    [SmoothOfRelativeDimension d t] (hc : c ≫ s = t) {U : Z.Opens}
    (hU : IsAffineOpen U) (hη : genericPoint Z ∈ U) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ (B : Subalgebra k Z.functionField),
      (∀ b, b ∈ B ↔ ∃ a : Γ(Z, U), (Z.presheaf.germ U _ hη).hom a = b) →
      ∀ y, y ∈ pullbackChartAlgebra (functionFieldPullbackAlg c hc) B ↔
        ∃ b : Γ(Y, c ⁻¹ᵁ U),
          (Y.presheaf.germ (c ⁻¹ᵁ U) _ (generic_mem_preimage_of_dominant hη)).hom b = y := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro B hB y
  let V := c ⁻¹ᵁ U
  let R := SectionRing t V
  have hV := hU.preimage c
  have hη' : genericPoint Y ∈ V := generic_mem_preimage_of_dominant hη
  letI : Nonempty V := ⟨⟨genericPoint Y, hη'⟩⟩
  letI : Algebra R Y.functionField := (Y.germToFunctionField V).hom.toAlgebra
  letI : IsFractionRing R Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hV
  letI : IsIntegrallyClosed R := integrallyClosed_smooth_affineOpen t d hV
  let j := functionFieldPullbackAlg c hc
  let g := sectionToFunctionField t V
  let q := sectionPullback hc U
  have he (a : SectionRing s U) : j ((Z.presheaf.germ U _ hη).hom a) = (g.comp q) a :=
    functionFieldPullbackAlg_germ c hc U hη hη' a
  have hR : B.map j = (g.comp q).range := by
    apply SetLike.ext
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := (hB y).mp hy
      exact ⟨a, (he a).symm.trans (congrArg j ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, (hB _).mpr ⟨a, rfl⟩, he a⟩
  have hr : (B.map j).toSubring = ((algebraMap R Y.functionField).comp q.toRingHom).range :=
    congrArg Subalgebra.toSubring hR
  change IsIntegral (B.map j).toSubring y ↔ ∃ b : R, algebraMap R Y.functionField b = y
  rw [hr]
  exact isIntegral_range_iff_of_finite q.toRingHom (c.finite_app U hU) y

/-- Integral closure of the chart algebras gives the pullback affine cover. -/
theorem isAffCover_pullbackChartAlgebra [IsFinite c] [IsDominant c] (d : ℕ)
    [SmoothOfRelativeDimension d t] (hc : c ≫ s = t) {ι : Type} (U : ι → Z.Opens) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ (B : Finset ι → Subalgebra k Z.functionField), IsAffCover s U B →
      IsAffCover t (fun i => c ⁻¹ᵁ U i) (fun I => pullbackChartAlgebra (functionFieldPullbackAlg c hc) (B I)) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro B hB
  let j := functionFieldPullbackAlg c hc
  let V (i : ι) := c ⁻¹ᵁ U i
  have hpre (I : Finset ι) : c ⁻¹ᵁ I.inf U = I.inf V := by
    classical
    induction I using Finset.induction_on with
    | empty => simp only [Finset.inf_empty, Scheme.Hom.preimage_top]
    | insert i I hi ih =>
      rw [Finset.inf_insert, c.preimage_inf, Finset.inf_insert]
      exact congrArg (V i ⊓ ·) ih
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro I hI
    rw [← hpre]
    exact (hB.affine I hI).preimage c
  · rw [← c.preimage_iSup, hB.cover, c.preimage_top]
  · intro I
    rw [← hpre]
    exact generic_mem_preimage_of_dominant (hB.ne I)
  · intro I hI y
    have key (W : Y.Opens) (_ : W = c ⁻¹ᵁ I.inf U) (hη : genericPoint Y ∈ W) :
        y ∈ pullbackChartAlgebra j (B I) ↔
          ∃ b : Γ(Y, W), (Y.presheaf.germ W _ hη).hom b = y := by
      subst W
      exact pullbackChartAlgebra_eq_range d hc (hB.affine I hI) (hB.ne I) (B I) (hB.ring I hI) y
    exact key _ (hpre I).symm _

end GlobalTheory.SchemeCohomology
