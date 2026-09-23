import GaloisForLFunctions.HTGeometry.HalfPlaneHardyModelSpace
import GaloisForLFunctions.RHTower.DetectorDuality
import GaloisForLFunctions.RHTower.SuzukiModelSpaceConjugation
import GaloisForLFunctions.RHTower.SuzukiModelKernel
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelOperator
import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram
import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension
import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank

/-!
# Totality of upper-half-plane Hardy Cauchy features

The boundary Cauchy vectors indexed by every point of the open upper half-plane have dense
complex span in the upper Hardy boundary space.  The proof uses the existing Fourier--Laplace
totality theorem on the conjugated vector, so no circle model or unproved boundary-value theorem
is needed.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance halfPlaneHardyCauchyTotalityLocalInst1 : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

/-- Pointwise complex conjugation is antiunitary on whole-line `L²`. -/
theorem inner_star_star_realLineL2 (u v : RealLineL2) :
    inner ℂ (star u) (star v) = (starRingEnd ℂ) (inner ℂ u v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star u,
    MeasureTheory.Lp.coeFn_star v] with x hu hv
  rw [hu, hv]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.inner_apply', map_mul,
    Complex.conj_conj]

/-- The reproducing Cauchy features over the open upper half-plane have dense span in upper Hardy
boundary space. -/
theorem topologicalClosure_span_lowerCauchyFeatureAt_eq_top :
    (Submodule.span ℂ (Set.range (fun w : {w : ℂ // 0 < w.im} =>
      lowerCauchyFeatureAt w.1 w.2))).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro f hf
  have hfeature : ∀ w : {w : ℂ // 0 < w.im},
      inner ℂ (lowerCauchyFeatureAt w.1 w.2) f = 0 := by
    intro w
    have h := hf (lowerCauchyFeatureAt w.1 w.2) ⟨w, rfl⟩
    calc
      inner ℂ (lowerCauchyFeatureAt w.1 w.2) f =
          (starRingEnd ℂ) (inner ℂ f (lowerCauchyFeatureAt w.1 w.2)) :=
        (inner_conj_symm (lowerCauchyFeatureAt w.1 w.2) f).symm
      _ = 0 := by rw [h, map_zero]
  have hstarUpper : star ((f : UpperHardyL2) : RealLineL2) ∈ RHTower.hardyL2 := by
    apply RHTower.mem_hardyL2_of_cauchyTransform_eq_zero
    intro v hv
    let w : {w : ℂ // 0 < w.im} :=
      ⟨(starRingEnd ℂ) v, by simpa using hv⟩
    have hw := hfeature w
    rw [inner_lowerCauchyFeatureAt] at hw
    calc
      (∫ x : ℝ, ((star ((f : UpperHardyL2) : RealLineL2) : RealLineL2) : ℝ → ℂ) x /
          (((x : ℝ) : ℂ) - v)) =
          ∫ x : ℝ, (starRingEnd ℂ)
            (((f : RealLineL2) : ℝ → ℂ) x /
              (((x : ℝ) : ℂ) - w.1)) := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.Lp.coeFn_star
          ((f : UpperHardyL2) : RealLineL2)] with x hx
        rw [hx, Pi.star_apply, map_div₀, map_sub, Complex.conj_ofReal]
        change (starRingEnd ℂ) (((f : RealLineL2) : ℝ → ℂ) x) /
            (((x : ℝ) : ℂ) - v) =
          (starRingEnd ℂ) (((f : RealLineL2) : ℝ → ℂ) x) /
            (((x : ℝ) : ℂ) - (starRingEnd ℂ) w.1)
        rw [show (starRingEnd ℂ) w.1 = v by
          simp only [w, Complex.conj_conj]]
      _ = (starRingEnd ℂ) (∫ x : ℝ,
          ((f : RealLineL2) : ℝ → ℂ) x /
            (((x : ℝ) : ℂ) - w.1)) := integral_conj
      _ = 0 := by rw [hw, map_zero]
  have hstarLower : star ((f : UpperHardyL2) : RealLineL2) ∈ RHTower.hardyL2ᗮ := by
    rw [← RHTower.map_star_hardyL2]
    exact ⟨(f : RealLineL2), f.property, rfl⟩
  have hself : inner ℂ (star ((f : UpperHardyL2) : RealLineL2))
      (star ((f : UpperHardyL2) : RealLineL2)) = 0 :=
    (Submodule.mem_orthogonal RHTower.hardyL2 _).mp hstarLower _ hstarUpper
  have hzero : star ((f : UpperHardyL2) : RealLineL2) = 0 :=
    inner_self_eq_zero.mp hself
  have hfzero : ((f : UpperHardyL2) : RealLineL2) = 0 := by
    have := congrArg star hzero
    rw [RHTower.star_star_lp,
      show star (0 : RealLineL2) = 0 by
        change RHTower.lpStarₛₗ 0 = 0
        exact RHTower.lpStarₛₗ.map_zero] at this
    exact this
  exact Subtype.ext hfzero

/-! ## Boundary multipliers -/

/-- A scalar function holomorphic on the closed upper half-plane and uniformly bounded there. -/
structure ClosedUpperHalfPlaneMultiplier where
  fn : ℂ → ℂ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  diff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ fn z
  norm_le : ∀ z : ℂ, 0 ≤ z.im → ‖fn z‖ ≤ bound

def ClosedUpperHalfPlaneMultiplier.boundary
    (F : ClosedUpperHalfPlaneMultiplier) (x : ℝ) : ℂ := F.fn (x : ℂ)

theorem ClosedUpperHalfPlaneMultiplier.continuous_boundary
    (F : ClosedUpperHalfPlaneMultiplier) : Continuous F.boundary := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (F.diff (x : ℂ) (by simp)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem ClosedUpperHalfPlaneMultiplier.measurable_boundary
    (F : ClosedUpperHalfPlaneMultiplier) : Measurable F.boundary :=
  F.continuous_boundary.measurable

theorem ClosedUpperHalfPlaneMultiplier.norm_boundary_le
    (F : ClosedUpperHalfPlaneMultiplier) (x : ℝ) :
    ‖F.boundary x‖ ≤ F.bound := F.norm_le (x : ℂ) (by simp)

/-- Whole-line multiplication by the boundary values of a bounded closed-upper-half-plane
multiplier. -/
def ClosedUpperHalfPlaneMultiplier.boundaryMul
    (F : ClosedUpperHalfPlaneMultiplier) : RealLineL2 →L[ℂ] RealLineL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    F.measurable_boundary F.bound_nonneg F.norm_boundary_le

theorem ClosedUpperHalfPlaneMultiplier.coe_boundaryMul
    (F : ClosedUpperHalfPlaneMultiplier) (f : RealLineL2) :
    ((F.boundaryMul f : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => F.boundary x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    F.measurable_boundary F.bound_nonneg F.norm_boundary_le f

private theorem closedUpperMultiplier_feature_mem_hardy
    (F : ClosedUpperHalfPlaneMultiplier) (w : {w : ℂ // 0 < w.im}) :
    F.boundaryMul
        ((lowerCauchyFeatureAt w.1 w.2 : UpperHardyL2) : RealLineL2) ∈
      RHTower.hardyL2 := by
  let u : ℂ → ℂ := fun z => F.fn z / (z - (starRingEnd ℂ) w.1)
  have hcont : Continuous (fun x : ℝ => u (x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hden : (x : ℂ) - (starRingEnd ℂ) w.1 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith [w.2]
    exact (((F.diff (x : ℂ) (by simp)).div
      (differentiableAt_id.sub_const _) hden).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)
  have hmem : MemLp (fun x : ℝ => u (x : ℂ)) 2 volume := by
    apply RHTower.memLp_two_of_poisson_bound
      (a := w.1.re) (b := w.1.im) (D := F.bound ^ (2 : ℕ)) w.2
      hcont.aestronglyMeasurable
    intro x
    change ‖F.fn (x : ℂ) / ((x : ℂ) - (starRingEnd ℂ) w.1)‖ ^ (2 : ℕ) ≤ _
    rw [norm_div, div_pow, RHTower.norm_sq_ofReal_sub_conj]
    gcongr
    exact F.norm_le (x : ℂ) (by simp)
  have hhardy : hmem.toLp (fun x : ℝ => u (x : ℂ)) ∈ RHTower.hardyL2 := by
    apply RHTower.mem_hardyL2_of_upperHalfPlane_decay
      (u := u) (M := 2 * F.bound) (R := 2 * ‖w.1‖ + 1)
    · intro z hz
      have hden : z - (starRingEnd ℂ) w.1 ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        norm_num at him
        linarith [w.2]
      exact (F.diff z hz).div (differentiableAt_id.sub_const _) hden
    · linarith [norm_nonneg w.1]
    · intro z hz hzR
      have hzn : 0 < ‖z‖ := by linarith [norm_nonneg w.1]
      have hhalf : ‖w.1‖ ≤ ‖z‖ / 2 := by linarith
      have hzw : ‖z‖ / 2 ≤ ‖z - (starRingEnd ℂ) w.1‖ := by
        have h := norm_sub_norm_le z ((starRingEnd ℂ) w.1)
        rw [RCLike.norm_conj] at h
        linarith
      have hzh : 0 < ‖z‖ / 2 := by linarith
      have hdenpos : 0 < ‖z - (starRingEnd ℂ) w.1‖ :=
        lt_of_lt_of_le hzh hzw
      calc
        ‖u z‖ = ‖F.fn z‖ / ‖z - (starRingEnd ℂ) w.1‖ := by
          change ‖F.fn z / (z - (starRingEnd ℂ) w.1)‖ = _
          rw [norm_div]
        _ ≤ F.bound / ‖z - (starRingEnd ℂ) w.1‖ := by
          exact (div_le_div_iff_of_pos_right hdenpos).2 (F.norm_le z hz)
        _ ≤ F.bound / (‖z‖ / 2) :=
          div_le_div_of_nonneg_left F.bound_nonneg hzh hzw
        _ = 2 * F.bound / ‖z‖ := by field_simp
  rw [← show hmem.toLp (fun x : ℝ => u (x : ℂ)) =
      F.boundaryMul
        ((lowerCauchyFeatureAt w.1 w.2 : UpperHardyL2) : RealLineL2) by
    apply MeasureTheory.Lp.ext
    filter_upwards [hmem.coeFn_toLp, F.coe_boundaryMul
      ((lowerCauchyFeatureAt w.1 w.2 : UpperHardyL2) : RealLineL2),
      coe_lowerCauchyFeatureAt w.2] with x hu hmul hfeature
    rw [hu, hmul, hfeature]
    rfl]
  exact hhardy

/-- Every bounded multiplier holomorphic through the real boundary preserves upper Hardy boundary
space. -/
theorem ClosedUpperHalfPlaneMultiplier.boundaryMul_mem_hardy
    (F : ClosedUpperHalfPlaneMultiplier) (f : UpperHardyL2) :
    F.boundaryMul ((f : UpperHardyL2) : RealLineL2) ∈ RHTower.hardyL2 := by
  let T : UpperHardyL2 →L[ℂ] RealLineL2 :=
    F.boundaryMul.comp UpperHardyL2.subtypeL
  let W : Submodule ℂ UpperHardyL2 :=
    Submodule.comap (T : UpperHardyL2 →ₗ[ℂ] RealLineL2) RHTower.hardyL2
  have hclosedW : IsClosed (W : Set UpperHardyL2) := by
    exact RHTower.isClosed_hardyL2.preimage T.continuous
  have hspan : Submodule.span ℂ
      (Set.range (fun w : {w : ℂ // 0 < w.im} =>
        lowerCauchyFeatureAt w.1 w.2)) ≤ W := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro w
    exact closedUpperMultiplier_feature_mem_hardy F w
  have hclosure := Submodule.topologicalClosure_minimal _ hspan hclosedW
  rw [topologicalClosure_span_lowerCauchyFeatureAt_eq_top] at hclosure
  exact hclosure (by simp)

/-- Restriction of a bounded closed-upper-half-plane boundary multiplier to upper Hardy space. -/
def ClosedUpperHalfPlaneMultiplier.hardyMul
    (F : ClosedUpperHalfPlaneMultiplier) : UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  (F.boundaryMul.comp UpperHardyL2.subtypeL).codRestrict
    UpperHardyL2 F.boundaryMul_mem_hardy

@[simp] theorem ClosedUpperHalfPlaneMultiplier.coe_hardyMul
    (F : ClosedUpperHalfPlaneMultiplier) (f : UpperHardyL2) :
    ((F.hardyMul f : UpperHardyL2) : RealLineL2) =
      F.boundaryMul ((f : UpperHardyL2) : RealLineL2) := rfl

/-! ## Inner quotients and literal anti-causal leakage -/

/-- Unitary whole-line boundary multiplication when the scalar boundary values are unimodular. -/
def ClosedUpperHalfPlaneMultiplier.boundaryUnitary
    (F : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖F.boundary x‖ = 1) :
    RealLineL2 ≃ₗᵢ[ℂ] RealLineL2 :=
  RHTower.unimodularMulUnitary F.boundary
    F.measurable_boundary.aestronglyMeasurable hinner

theorem ClosedUpperHalfPlaneMultiplier.boundaryUnitary_ae
    (F : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖F.boundary x‖ = 1) (f : RealLineL2) :
    F.boundaryUnitary hinner f =ᵐ[volume]
      fun x => F.boundary x * (f : ℝ → ℂ) x :=
  RHTower.unimodularMulUnitary_ae F.boundary
    F.measurable_boundary.aestronglyMeasurable hinner f

theorem ClosedUpperHalfPlaneMultiplier.boundaryMul_eq_boundaryUnitary
    (F : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖F.boundary x‖ = 1) (f : RealLineL2) :
    F.boundaryMul f = F.boundaryUnitary hinner f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [F.coe_boundaryMul f, F.boundaryUnitary_ae hinner f]
    with x hmul hunitary
  rw [hmul, hunitary]

theorem ClosedUpperHalfPlaneMultiplier.norm_hardyMul_of_inner
    (F : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖F.boundary x‖ = 1) (f : UpperHardyL2) :
    ‖F.hardyMul f‖ = ‖f‖ := by
  change ‖F.boundaryMul ((f : UpperHardyL2) : RealLineL2)‖ =
    ‖((f : UpperHardyL2) : RealLineL2)‖
  rw [F.boundaryMul_eq_boundaryUnitary hinner]
  exact (F.boundaryUnitary hinner).norm_map _

/-- Model space complementary to the invariant Hardy range of an inner boundary multiplier. -/
def closedUpperInnerModelSpace (B : ClosedUpperHalfPlaneMultiplier) :
    Submodule ℂ UpperHardyL2 :=
  (LinearMap.range (B.hardyMul : UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ

local instance (B : ClosedUpperHalfPlaneMultiplier) :
    CompleteSpace (closedUpperInnerModelSpace B) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- Projection of the analytic numerator onto the denominator model space. -/
def closedUpperInnerLeakageCore
    (A B : ClosedUpperHalfPlaneMultiplier) :
    UpperHardyL2 →L[ℂ] closedUpperInnerModelSpace B :=
  modelSpaceLeakageCore (closedUpperInnerModelSpace B) A.hardyMul

theorem isClosed_range_closedUpper_hardyMul_of_inner
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    IsClosed ((LinearMap.range
      (B.hardyMul : UpperHardyL2 →ₗ[ℂ] UpperHardyL2) :
        Submodule ℂ UpperHardyL2) : Set UpperHardyL2) :=
  isClosed_coe_range_of_isometry (B.norm_hardyMul_of_inner hinner)

/-- Multiplication by the inverse inner boundary identifies the denominator model space with a
closed subspace of lower Hardy boundary space. -/
private theorem closedUpperInnerModelEmbedding_mem
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    (k : closedUpperInnerModelSpace B) :
    (B.boundaryUnitary hinner).symm (k : RealLineL2) ∈ LowerHardyL2 := by
  intro h hh
  let f : UpperHardyL2 := ⟨h, hh⟩
  let r : UpperHardyL2 := B.hardyMul f
  have hrange : r ∈ LinearMap.range
      (B.hardyMul : UpperHardyL2 →ₗ[ℂ] UpperHardyL2) := ⟨f, rfl⟩
  have hzero : inner ℂ r k = 0 := k.property r hrange
  have hcoe : ((r : UpperHardyL2) : RealLineL2) =
      B.boundaryUnitary hinner h := by
    change B.boundaryMul h = B.boundaryUnitary hinner h
    exact B.boundaryMul_eq_boundaryUnitary hinner h
  calc
    inner ℂ h ((B.boundaryUnitary hinner).symm (k : RealLineL2)) =
        inner ℂ (B.boundaryUnitary hinner h)
          (B.boundaryUnitary hinner
            ((B.boundaryUnitary hinner).symm (k : RealLineL2))) :=
      ((B.boundaryUnitary hinner).inner_map_map h
        ((B.boundaryUnitary hinner).symm (k : RealLineL2))).symm
    _ = inner ℂ (B.boundaryUnitary hinner h) (k : RealLineL2) := by
      rw [(B.boundaryUnitary hinner).apply_symm_apply]
    _ = inner ℂ ((r : UpperHardyL2) : RealLineL2) (k : RealLineL2) := by
      rw [hcoe]
    _ = inner ℂ (r : UpperHardyL2) (k : UpperHardyL2) :=
      (UpperHardyL2.coe_inner r (k : UpperHardyL2)).symm
    _ = 0 := hzero

/-- Ambient inverse-inner multiplication on the denominator model space. -/
def closedUpperInnerModelEmbeddingAmbient
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    closedUpperInnerModelSpace B →L[ℂ] RealLineL2 :=
  (B.boundaryUnitary hinner).symm.toLinearIsometry.toContinuousLinearMap.comp
    (UpperHardyL2.subtypeL.comp (closedUpperInnerModelSpace B).subtypeL)

/-- Multiplication by the inverse inner boundary identifies the denominator model space with a
closed subspace of lower Hardy boundary space. -/
def closedUpperInnerModelEmbedding
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    closedUpperInnerModelSpace B →L[ℂ] LowerHardyL2 :=
  ((closedUpperInnerModelEmbeddingAmbient B hinner).codRestrict
    LowerHardyL2 (fun k => by
      change (B.boundaryUnitary hinner).symm (k : RealLineL2) ∈ LowerHardyL2
      exact closedUpperInnerModelEmbedding_mem B hinner k))

theorem norm_closedUpperInnerModelEmbedding
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    (k : closedUpperInnerModelSpace B) :
    ‖closedUpperInnerModelEmbedding B hinner k‖ = ‖k‖ := by
  change ‖(B.boundaryUnitary hinner).symm (k : RealLineL2)‖ =
    ‖(k : UpperHardyL2)‖
  rw [(B.boundaryUnitary hinner).symm.norm_map]
  rfl

/-- The inverse-inner model embedding, packaged as a linear isometry. -/
noncomputable def closedUpperInnerModelEmbeddingIsometry
    (B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    closedUpperInnerModelSpace B →ₗᵢ[ℂ] LowerHardyL2 where
  toLinearMap := (closedUpperInnerModelEmbedding B hinner).toLinearMap
  norm_map' := norm_closedUpperInnerModelEmbedding B hinner

/-- Whole-line multiplication by the boundary quotient `A / B`, with the inverse inner
denominator implemented by its exact unitary multiplication operator. -/
def closedUpperInnerQuotientMul
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  (B.boundaryUnitary hinner).symm.toLinearIsometry.toContinuousLinearMap.comp
    A.boundaryMul

/-- Literal anti-causal compression of the boundary quotient `A / B`. -/
def closedUpperInnerQuotientLeakage
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    UpperHardyL2 →L[ℂ] LowerHardyL2 :=
  hardyLeakage (closedUpperInnerQuotientMul A B hinner)

/-- The literal quotient leakage is exactly the denominator-model projection, followed by the
inverse-inner isometric embedding into lower Hardy space. -/
theorem closedUpperInnerQuotientLeakage_eq_modelEmbedding_comp
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    closedUpperInnerQuotientLeakage A B hinner =
      (closedUpperInnerModelEmbedding B hinner).comp
        (closedUpperInnerLeakageCore A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro q
  change inner ℂ q
      (LowerHardyL2.orthogonalProjectionOnto
        ((B.boundaryUnitary hinner).symm
          (A.boundaryMul ((f : UpperHardyL2) : RealLineL2)))) =
    inner ℂ q
      (closedUpperInnerModelEmbedding B hinner
        (closedUpperInnerLeakageCore A B f))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  let R : Submodule ℂ UpperHardyL2 :=
    LinearMap.range (B.hardyMul : UpperHardyL2 →ₗ[ℂ] UpperHardyL2)
  let K : Submodule ℂ UpperHardyL2 := closedUpperInnerModelSpace B
  have hclosedR : IsClosed (R : Set UpperHardyL2) :=
    isClosed_range_closedUpper_hardyMul_of_inner B hinner
  letI : CompleteSpace R := hclosedR.completeSpace_coe
  have hKorth : Kᗮ = R := by
    change (Rᗮ)ᗮ = R
    rw [Submodule.orthogonal_orthogonal]
  let y : UpperHardyL2 := A.hardyMul f
  let p : UpperHardyL2 := K.starProjection y
  let r : UpperHardyL2 := y - p
  have hrange : r ∈ R := by
    have hrorth : r ∈ Kᗮ := K.sub_starProjection_mem_orthogonal y
    rw [hKorth] at hrorth
    exact hrorth
  obtain ⟨g, hg⟩ := hrange
  have hinv_r :
      (B.boundaryUnitary hinner).symm (r : RealLineL2) =
        (g : RealLineL2) := by
    apply (B.boundaryUnitary hinner).injective
    rw [(B.boundaryUnitary hinner).apply_symm_apply]
    calc
      (r : RealLineL2) = (B.hardyMul g : UpperHardyL2) := by
        exact congrArg (fun u : UpperHardyL2 => (u : RealLineL2)) hg.symm
      _ = B.boundaryMul (g : RealLineL2) := rfl
      _ = B.boundaryUnitary hinner (g : RealLineL2) :=
        B.boundaryMul_eq_boundaryUnitary hinner g
  have horth :
      inner ℂ ((q : LowerHardyL2) : RealLineL2)
        ((B.boundaryUnitary hinner).symm (r : RealLineL2)) = 0 := by
    rw [hinv_r]
    exact inner_eq_zero_symm.mp
      ((Submodule.mem_orthogonal RHTower.hardyL2
        ((q : LowerHardyL2) : RealLineL2)).mp q.property
          (g : RealLineL2) g.property)
  calc
    inner ℂ ((q : LowerHardyL2) : RealLineL2)
        ((B.boundaryUnitary hinner).symm
          (A.boundaryMul ((f : UpperHardyL2) : RealLineL2))) =
      inner ℂ ((q : LowerHardyL2) : RealLineL2)
        ((B.boundaryUnitary hinner).symm (y : RealLineL2)) := by
          rfl
    _ = inner ℂ ((q : LowerHardyL2) : RealLineL2)
        ((B.boundaryUnitary hinner).symm
          ((p : RealLineL2) + (r : RealLineL2))) := by
          congr 2
          simp [r]
    _ = inner ℂ ((q : LowerHardyL2) : RealLineL2)
          ((B.boundaryUnitary hinner).symm (p : RealLineL2)) +
        inner ℂ ((q : LowerHardyL2) : RealLineL2)
          ((B.boundaryUnitary hinner).symm (r : RealLineL2)) := by
          rw [map_add, inner_add_right]
    _ = inner ℂ ((q : LowerHardyL2) : RealLineL2)
        ((B.boundaryUnitary hinner).symm (p : RealLineL2)) := by
          rw [horth, add_zero]
    _ = inner ℂ q
        (closedUpperInnerModelEmbedding B hinner
          (closedUpperInnerLeakageCore A B f)) := by
          change inner ℂ ((q : LowerHardyL2) : RealLineL2)
              ((closedUpperInnerModelEmbedding B hinner
                (closedUpperInnerLeakageCore A B f) : LowerHardyL2) : RealLineL2) =
            inner ℂ q
              (closedUpperInnerModelEmbedding B hinner
                (closedUpperInnerLeakageCore A B f))
          exact (LowerHardyL2.coe_inner q
            (closedUpperInnerModelEmbedding B hinner
              (closedUpperInnerLeakageCore A B f))).symm

/-- Literal quotient leakage and the model-space core have exactly the same Gram kernel. -/
theorem inner_closedUpperInnerQuotientLeakage_eq_core
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    (f g : UpperHardyL2) :
    inner ℂ (closedUpperInnerQuotientLeakage A B hinner f)
        (closedUpperInnerQuotientLeakage A B hinner g) =
      inner ℂ (closedUpperInnerLeakageCore A B f)
        (closedUpperInnerLeakageCore A B g) := by
  rw [closedUpperInnerQuotientLeakage_eq_modelEmbedding_comp]
  exact LinearIsometry.inner_map_map (𝕜 := ℂ)
    (closedUpperInnerModelEmbeddingIsometry B hinner)
    (closedUpperInnerLeakageCore A B f)
    (closedUpperInnerLeakageCore A B g)

theorem closedUpperInnerQuotientLeakage_apply
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    (f : UpperHardyL2) :
    closedUpperInnerQuotientLeakage A B hinner f =
      closedUpperInnerModelEmbedding B hinner
        (closedUpperInnerLeakageCore A B f) := by
  have h := congrArg (fun T : UpperHardyL2 →L[ℂ] LowerHardyL2 => T f)
    (closedUpperInnerQuotientLeakage_eq_modelEmbedding_comp A B hinner)
  exact h

/-- Isometric postprocessing carries the abstract model-core range onto the literal leakage
range. -/
noncomputable def closedUpperInnerCoreRangeToQuotientLeakageRange
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    LinearMap.range
        (closedUpperInnerLeakageCore A B :
          UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B) →ₗᵢ[ℂ]
      LinearMap.range
        (closedUpperInnerQuotientLeakage A B hinner :
          UpperHardyL2 →ₗ[ℂ] LowerHardyL2) where
  toFun := fun z =>
    ⟨closedUpperInnerModelEmbeddingIsometry B hinner z.1, by
      rcases z.property with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      calc
        closedUpperInnerQuotientLeakage A B hinner f =
            closedUpperInnerModelEmbeddingIsometry B hinner
              (closedUpperInnerLeakageCore A B f) :=
          closedUpperInnerQuotientLeakage_apply A B hinner f
        _ = closedUpperInnerModelEmbeddingIsometry B hinner z.1 := by
          exact congrArg (closedUpperInnerModelEmbeddingIsometry B hinner) hf⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact (closedUpperInnerModelEmbeddingIsometry B hinner).map_add x.1 y.1
  map_smul' := by
    intro c x
    apply Subtype.ext
    exact (closedUpperInnerModelEmbeddingIsometry B hinner).map_smul c x.1
  norm_map' := by
    intro x
    change ‖closedUpperInnerModelEmbeddingIsometry B hinner x.1‖ = ‖x.1‖
    exact (closedUpperInnerModelEmbeddingIsometry B hinner).norm_map x.1

theorem closedUpperInnerCoreRangeToQuotientLeakageRange_surjective
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    Function.Surjective
      (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner) := by
  intro y
  rcases y.property with ⟨f, hf⟩
  let z : LinearMap.range
      (closedUpperInnerLeakageCore A B :
        UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B) :=
    ⟨closedUpperInnerLeakageCore A B f, ⟨f, rfl⟩⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change closedUpperInnerModelEmbeddingIsometry B hinner
      (closedUpperInnerLeakageCore A B f) = y.1
  calc
    closedUpperInnerModelEmbeddingIsometry B hinner
        (closedUpperInnerLeakageCore A B f) =
      closedUpperInnerQuotientLeakage A B hinner f :=
        (closedUpperInnerQuotientLeakage_apply A B hinner f).symm
    _ = y.1 := hf

private theorem closedUpperInnerCoreRangeToQuotientLeakageRange_injective
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    Function.Injective
      (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner).toLinearMap := by
  intro x y hxy
  exact (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner).injective hxy

/-- The direct range isometry upgraded using its proved surjectivity. -/
noncomputable def closedUpperInnerCoreRangeQuotientLeakageEquiv
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    LinearMap.range
        (closedUpperInnerLeakageCore A B :
          UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B) ≃ₗᵢ[ℂ]
      LinearMap.range
        (closedUpperInnerQuotientLeakage A B hinner :
          UpperHardyL2 →ₗ[ℂ] LowerHardyL2) where
  toLinearEquiv := LinearEquiv.ofBijective
    (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner).toLinearMap
    ⟨closedUpperInnerCoreRangeToQuotientLeakageRange_injective A B hinner,
      closedUpperInnerCoreRangeToQuotientLeakageRange_surjective A B hinner⟩
  norm_map' := (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner).norm_map

/-- Canonical isometric equivalence between the literal quotient-leakage range and the abstract
denominator-model leakage range. -/
noncomputable def closedUpperInnerQuotientLeakageRangeEquiv
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    LinearMap.range
        (closedUpperInnerQuotientLeakage A B hinner :
          UpperHardyL2 →ₗ[ℂ] LowerHardyL2) ≃ₗᵢ[ℂ]
      LinearMap.range
        (closedUpperInnerLeakageCore A B :
          UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B) :=
  (closedUpperInnerCoreRangeQuotientLeakageEquiv A B hinner).symm

/-- Literal quotient leakage and the denominator-model core have identical algebraic rank. -/
theorem finrank_range_closedUpperInnerQuotientLeakage_eq_core
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1) :
    Module.finrank ℂ (LinearMap.range
        (closedUpperInnerQuotientLeakage A B hinner :
          UpperHardyL2 →ₗ[ℂ] LowerHardyL2)) =
      Module.finrank ℂ (LinearMap.range
        (closedUpperInnerLeakageCore A B :
          UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B)) :=
  LinearEquiv.finrank_eq
    (closedUpperInnerQuotientLeakageRangeEquiv A B hinner).toLinearEquiv

/-- A faithful numerator gives literal quotient-leakage rank equal to the finite denominator-model
dimension. -/
theorem finrank_range_closedUpperInnerQuotientLeakage_of_finiteDimensional
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    [FiniteDimensional ℂ (closedUpperInnerModelSpace B)]
    (hinj : Function.Injective
      ((A.hardyMul).adjoint.toLinearMap.domRestrict
        (closedUpperInnerModelSpace B))) :
    Module.finrank ℂ (LinearMap.range
        (closedUpperInnerQuotientLeakage A B hinner :
          UpperHardyL2 →ₗ[ℂ] LowerHardyL2)) =
      Module.finrank ℂ (closedUpperInnerModelSpace B) := by
  rw [finrank_range_closedUpperInnerQuotientLeakage_eq_core]
  exact finrank_range_modelSpaceLeakageCore_of_finiteDimensional
    (closedUpperInnerModelSpace B) A.hardyMul hinj

/-- A faithful numerator over an infinite denominator model gives genuinely infinite algebraic
rank for the literal anti-causal quotient leakage. -/
theorem not_finiteDimensional_range_closedUpperInnerQuotientLeakage
    (A B : ClosedUpperHalfPlaneMultiplier)
    (hinner : ∀ x : ℝ, ‖B.boundary x‖ = 1)
    (hmodel : ¬ FiniteDimensional ℂ (closedUpperInnerModelSpace B))
    (hinj : Function.Injective
      ((A.hardyMul).adjoint.toLinearMap.domRestrict
        (closedUpperInnerModelSpace B))) :
    ¬ FiniteDimensional ℂ (LinearMap.range
      (closedUpperInnerQuotientLeakage A B hinner :
        UpperHardyL2 →ₗ[ℂ] LowerHardyL2)) := by
  have hcore : ¬ FiniteDimensional ℂ (LinearMap.range
      (closedUpperInnerLeakageCore A B :
        UpperHardyL2 →ₗ[ℂ] closedUpperInnerModelSpace B)) := by
    exact not_finiteDimensional_range_modelSpaceLeakageCore
      (closedUpperInnerModelSpace B) A.hardyMul hmodel hinj
  intro hliteral
  letI : FiniteDimensional ℂ (LinearMap.range
      (closedUpperInnerQuotientLeakage A B hinner :
        UpperHardyL2 →ₗ[ℂ] LowerHardyL2)) := hliteral
  apply hcore
  exact FiniteDimensional.of_injective
    (closedUpperInnerCoreRangeToQuotientLeakageRange A B hinner).toLinearMap
    (closedUpperInnerCoreRangeToQuotientLeakageRange_injective A B hinner)

end GaloisForLFunctions.HTGeometry
