import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Lifting along an independent coordinate and recovering by integration

Let `ν` be a probability measure.  Appending an independent coordinate distributed by `ν` gives
the insertion `J : L²(μ; K) → L²(μ ⊗ ν; K)`, `(J f)(x, v) = f x`.  It is a linear isometry, its
adjoint is the conditional expectation

`(P g)(x) = ∫ g(x, v) dν(v)`,

`P J = 1`, and multiplication by a bounded function of the first coordinate commutes with `J` and
`P`.

* `coordinateLift`, `coeFn_coordinateLift`;
* `coordinateRecovery`, `coordinateRecovery_comp_lift`, **`coeFn_coordinateRecovery`**;
* `coordinateLift_comp_mul`, `mul_comp_coordinateRecovery`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Lift

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
  [SFinite μ] [IsProbabilityMeasure ν]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance factOneLeTwoCoordinateLift : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- **Insertion of an independent coordinate**: `(J f)(x, v) = f x`. -/
def coordinateLift : Lp K 2 μ →ₗᵢ[ℂ] Lp K 2 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst measurePreserving_fst

omit [SFinite μ] [CompleteSpace K] in
theorem coeFn_coordinateLift (f : Lp K 2 μ) :
    (coordinateLift μ ν f : X × Y → K) =ᵐ[μ.prod ν] fun p => (f : X → K) p.1 :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_fst

/-- **Recovery** `P = J*`. -/
def coordinateRecovery : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 μ :=
  ContinuousLinearMap.adjoint (coordinateLift (K := K) μ ν).toContinuousLinearMap

omit [SFinite μ] in
/-- **Exact recovery**: `P J = 1`. -/
theorem coordinateRecovery_comp_lift :
    coordinateRecovery (K := K) μ ν ∘L (coordinateLift μ ν).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

omit [SFinite μ] in
theorem coordinateRecovery_lift (f : Lp K 2 μ) :
    coordinateRecovery μ ν (coordinateLift μ ν f) = f := by
  have h := congrArg (fun T => T f) (coordinateRecovery_comp_lift (K := K) μ ν)
  simpa using h

/-- The fibre average `x ↦ ∫ g(x, v) dν(v)`. -/
def fibreAverage (g : Lp K 2 (μ.prod ν)) (x : X) : K := ∫ v, (g : X × Y → K) (x, v) ∂ν

omit [SFinite μ] [CompleteSpace K] in
theorem stronglyMeasurable_fibreAverage (g : Lp K 2 (μ.prod ν)) :
    StronglyMeasurable (fibreAverage μ ν g) :=
  (Lp.stronglyMeasurable g).integral_prod_right'

omit [SFinite μ] [CompleteSpace K] in
/-- Jensen for the fibre average: `‖∫ g(x, ·) dν‖² ≤ ∫ ‖g(x, ·)‖² dν`. -/
theorem enorm_fibreAverage_sq_le (g : Lp K 2 (μ.prod ν)) (x : X) :
    ‖fibreAverage μ ν g x‖ₑ ^ 2 ≤ ∫⁻ v, ‖(g : X × Y → K) (x, v)‖ₑ ^ 2 ∂ν := by
  have hmeas : Measurable fun v => ‖(g : X × Y → K) (x, v)‖ₑ :=
    ((Lp.stronglyMeasurable g).comp_measurable measurable_prodMk_left).enorm
  have hJ := lintegral_weighted_sq_le ν (K := fun _ => (1 : ℝ≥0∞)) measurable_const hmeas
  simp only [one_mul, lintegral_const, measure_univ] at hJ
  calc ‖fibreAverage μ ν g x‖ₑ ^ 2 ≤ (∫⁻ v, ‖(g : X × Y → K) (x, v)‖ₑ ∂ν) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by simpa using hJ

omit [SFinite μ] [CompleteSpace K] in
theorem memLp_fibreAverage (g : Lp K 2 (μ.prod ν)) : MemLp (fibreAverage μ ν g) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_fibreAverage μ ν g).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact ((stronglyMeasurable_fibreAverage μ ν g).norm.pow 2).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    have hfin : ∫⁻ p, ‖(g : X × Y → K) p‖ₑ ^ 2 ∂μ.prod ν < ⊤ := by
      have h := (Lp.memLp g).eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
      have h2 : (∫⁻ p, ‖(g : X × Y → K) p‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂μ.prod ν) ≠ ⊤ := by
        intro htop
        rw [htop] at h
        simp at h
      simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h2.lt_top
    refine lt_of_le_of_lt ?_ hfin
    rw [lintegral_prod _ ((Lp.stronglyMeasurable g).enorm.pow_const 2).aemeasurable]
    refine lintegral_mono fun x => ?_
    rw [enorm_pow, enorm_norm]
    exact enorm_fibreAverage_sq_le μ ν g x

/-- **The recovery is the fibre average**: `(P g)(x) = ∫ g(x, v) dν(v)`. -/
theorem coeFn_coordinateRecovery (g : Lp K 2 (μ.prod ν)) :
    (coordinateRecovery μ ν g : X → K) =ᵐ[μ] fibreAverage μ ν g := by
  have heq : coordinateRecovery μ ν g = (memLp_fibreAverage μ ν g).toLp _ := by
    refine ext_inner_left ℂ fun f => ?_
    rw [coordinateRecovery, ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    have hint : Integrable (fun p : X × Y => ⟪(f : X → K) p.1, (g : X × Y → K) p⟫_ℂ) (μ.prod ν) :=
      (L2.integrable_inner (𝕜 := ℂ) (coordinateLift μ ν f) g).congr (by
        filter_upwards [coeFn_coordinateLift μ ν f] with p hp
        rw [hp])
    rw [integral_congr_ae (g := fun p : X × Y => ⟪(f : X → K) p.1, (g : X × Y → K) p⟫_ℂ) (by
        filter_upwards [coeFn_coordinateLift μ ν f] with p hp
        rw [hp]), integral_prod _ hint]
    refine integral_congr_ae ?_
    have hsec : ∀ᵐ x ∂μ, Integrable (fun v => (g : X × Y → K) (x, v)) ν := by
      have hsq : Integrable (fun p => ‖(g : X × Y → K) p‖ ^ 2) (μ.prod ν) :=
        (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
      filter_upwards [hsq.prod_right_ae] with x hx
      refine ((memLp_two_iff_integrable_sq_norm ?_).mpr hx).integrable (by norm_num)
      exact ((Lp.stronglyMeasurable g).comp_measurable measurable_prodMk_left).aestronglyMeasurable
    filter_upwards [hsec, (memLp_fibreAverage μ ν g).coeFn_toLp] with x hx hx'
    rw [hx', fibreAverage]
    exact ((innerSL ℂ ((f : X → K) x)).integral_comp_comm hx)
  rw [heq]
  exact (memLp_fibreAverage μ ν g).coeFn_toLp

end Lift

section Multipliers

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
  [SFinite μ] [IsProbabilityMeasure ν]

local instance factOneLeTwoCoordinateMul : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {φ : X → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)

omit [SFinite μ] in
include hφ hC0 hC in
/-- **Lifting commutes with source multipliers**: `M_{φ∘fst} J = J M_φ`. -/
theorem coordinateLift_comp_mul :
    lpBoundedMulCLM (p := 2) (μ := μ.prod ν) (hφ.comp measurable_fst) hC0 (fun p => hC p.1) ∘L
        (coordinateLift (K := ℂ) μ ν).toContinuousLinearMap =
      (coordinateLift μ ν).toContinuousLinearMap ∘L
        lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  have h1 := lpBoundedMulCLM_coeFn (p := 2) (μ := μ.prod ν) (hφ.comp measurable_fst) hC0
    (fun p => hC p.1) (coordinateLift μ ν f)
  have h2 := coeFn_coordinateLift μ ν f
  have h3 := coeFn_coordinateLift μ ν (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f)
  have h4 := (measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae_eq_comp
    (lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f)
  filter_upwards [h1, h2, h3, h4] with p e1 e2 e3 e4
  rw [e1, e3, e2]
  exact e4.symm

include hφ hC0 hC in
/-- **Recovery commutes with source multipliers**: `P M_{φ∘fst} = M_φ P`. -/
theorem mul_comp_coordinateRecovery :
    coordinateRecovery (K := ℂ) μ ν ∘L
        lpBoundedMulCLM (p := 2) (μ := μ.prod ν) (hφ.comp measurable_fst) hC0 (fun p => hC p.1) =
      lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC ∘L coordinateRecovery μ ν := by
  refine ContinuousLinearMap.ext fun g => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  have h1 := coeFn_coordinateRecovery μ ν
    (lpBoundedMulCLM (p := 2) (μ := μ.prod ν) (hφ.comp measurable_fst) hC0 (fun p => hC p.1) g)
  have h2 := lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC (coordinateRecovery μ ν g)
  have h3 := coeFn_coordinateRecovery μ ν g
  have h4 := Measure.ae_ae_of_ae_prod (lpBoundedMulCLM_coeFn (p := 2) (μ := μ.prod ν)
    (hφ.comp measurable_fst) hC0 (fun p => hC p.1) g)
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  rw [e1, e2, e3, fibreAverage, fibreAverage, ← integral_const_mul]
  exact integral_congr_ae (e4.mono fun v hv => by simpa using hv)

end Multipliers

end GaloisForLFunctions.HTGeometry
