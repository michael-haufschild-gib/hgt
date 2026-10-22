import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularCuspCutoff
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalWeightedAngularData
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullCoreOperator

/-! Actual full modular physical tests, with compact cusp cutoffs and exact local stabilization. -/
open Set Filter Topology UpperHalfPlane ModularGroup MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMJointWave D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem physical_S (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (S • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  have h := physicalScalar_invert q ⟨z.re,z.im,z.im_pos⟩
  rw [UpperHalfPlane.modular_S_smul]
  simpa [coordinates,d4BMEisensteinInvertCoordinate,
    Complex.inv_re,Complex.inv_im,Complex.normSq_apply,sq,neg_div] using h

private theorem physical_T (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (T • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  simp only [coordinates,ModularGroup.re_T_smul,ModularGroup.im_T_smul]
  simpa [scalar] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic (physicalAngularParameter q) z.im z.re

/-- The entire physical target field is modular at its actual parameter, with its full Fourier tail. -/
theorem physicalScalar_modular (q : XiZeroCopy) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (A • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  have hA : A ∈ Subgroup.closure {S,T} := by simp [SpecialLinearGroup.SL2Z_generators]
  suffices ∀ z : UpperHalfPlane,
      scalar (physicalAngularParameter q) (coordinates (A • z)) =
      scalar (physicalAngularParameter q) (coordinates z) from this z
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff,mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact physical_S q
    · exact physical_T q
  | one => intro w; simp
  | mul g h _ _ ig ih => intro w; rw [mul_smul,ig,ih]
  | inv g _ ig => intro w; simpa using (ig (g⁻¹ • w)).symm

/-- Conjugation matches the test-first Hilbert convention of the original response equation. -/
def physicalTestField (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  conj (scalar (physicalAngularParameter q) (coordinates z))

theorem physicalTestField_smooth (q : XiZeroCopy) : ChartSmooth (physicalTestField q) := by
  intro z
  have hs : ContDiffAt ℝ ∞ (scalar (physicalAngularParameter q)) (coordinates z) :=
    (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.im_pos)
  have he : (physicalTestField q) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      fun w : ℂ => conj (scalar (physicalAngularParameter q) (angularCoordinates w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,physicalTestField,coordinates,angularCoordinates,
      ofComplex_apply_of_im_pos hw]
    rfl
  have hs' : ContDiffAt ℝ ∞ (scalar (physicalAngularParameter q) ∘ angularCoordinates) (z:ℂ) :=
    hs.comp (z:ℂ) angularCoordinates.contDiff.contDiffAt
  have hh : ContDiffAt ℝ ∞
      (fun w : ℂ => conj (scalar (physicalAngularParameter q) (angularCoordinates w))) (z:ℂ) := by
    exact Complex.conjCLE.contDiff.contDiffAt.comp (z:ℂ) hs'
  exact hh.congr_of_eventuallyEq he

theorem physicalTestField_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    physicalTestField q (γ • z) = physicalTestField q z := by
  induction γ using QuotientGroup.induction_on with
  | H A => simp only [PSL2Z_mk_smul,physicalTestField,physicalScalar_modular]

private theorem scale_one_le (n : ℕ) : (1:ℝ) ≤ (n:ℝ)+1 := by
  have : (0:ℝ) ≤ n := by positivity
  linarith

/-- A constructed original core field, with no compactness, seam, or smoothness premise supplied. -/
def physicalCoreCutoff (q : XiZeroCopy) (n : ℕ) : CoreField where
  field z := modularCuspCutoff ((n:ℝ)+1) z*physicalTestField q z
  smooth z := (modularCuspCutoff_smooth _ (scale_one_le n) z).mul
    (physicalTestField_smooth q z)
  invariant γ z := by
    rw [modularCuspCutoff_invariant _ (scale_one_le n),
      physicalTestField_invariant]
  compact := by
    obtain ⟨K,hK,hc⟩ := modularCuspCutoff_compact ((n:ℝ)+1) (scale_one_le n)
    refine ⟨K,hK,?_⟩
    intro z hz hn
    change modularCuspCutoff ((n:ℝ)+1) z*physicalTestField q z = 0
    rw [hc z hz hn,zero_mul]

/-- At every fixed original cell point, the entire physical test germ eventually stabilizes. -/
theorem physicalCoreCutoff_eventually_germ (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, (physicalCoreCutoff q n).field =ᶠ[𝓝 z] physicalTestField q := by
  filter_upwards [modularCuspCutoff_eventually_one z hz] with n hn
  filter_upwards [hn] with w hw
  change modularCuspCutoff ((n:ℝ)+1) w*physicalTestField q w = physicalTestField q w
  rw [hw,one_mul]

/-- The native core Laplacian eventually agrees pointwise with the complete physical test Laplacian. -/
theorem physicalCoreCutoff_eventually_laplacian (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, (physicalCoreCutoff q n).laplacian.field z =
      chartLaplacian (physicalTestField q) z := by
  filter_upwards [physicalCoreCutoff_eventually_germ q z hz] with n hn
  exact chartLaplacian_congr hn

end
end RHTower.D4BMJointSource
