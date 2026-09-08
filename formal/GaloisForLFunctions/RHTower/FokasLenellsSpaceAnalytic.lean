import GaloisForLFunctions.RHTower.FokasLenellsSpaceBoundary
import GaloisForLFunctions.RHTower.FokasLenellsTimeAnalytic
import GaloisForLFunctions.RHTower.FokasLenellsCauchySemigroup

/-!
# Space differentiation through holomorphic reconstruction and Plemelj limits

Bounded Cauchy evaluation and signed Hardy propagation carry the proved L²
density derivative into actual holomorphic matrix entries and horizontal
slices. Space differentiation commutes with both strong boundary limits.
The differentiated slices stay holomorphic, decay at infinite height, and
inherit their own differentiated Hardy boundary values.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Space differentiation of the actual holomorphic reconstruction replaces its density by its derivative. -/
def directAnalyticSpaceMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cauchyExtension (boundaryComponent (directRHSpaceDensity q t x i) j) z

/-- Every off-contour reconstructed entry has the genuine spatial derivative given by the differentiated Cauchy integral. -/
theorem directAnalyticMatrix_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directAnalyticMatrix q t s (halfPlanePoint upper r a) i j)
      (directAnalyticSpaceMatrix q t x (halfPlanePoint upper r a) i j) x := by
  have hd : HasDerivAt (fun s => boundaryComponent (directRHDensity q t s i) j)
      (boundaryComponent (directRHSpaceDensity q t x i) j) x := by
    fin_cases j
    · exact (directRHDensity_space_hasDerivAt q t x i).fst
    · exact (directRHDensity_space_hasDerivAt q t x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd
  change HasDerivAt (fun s => cauchyEvaluation upper r a (boundaryComponent (directRHDensity q t s i) j))
    (cauchyEvaluation upper r a (boundaryComponent (directRHSpaceDensity q t x i) j)) x at he
  have hh := he.const_add ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  simpa only [cauchyEvaluation_apply,directAnalyticMatrix,directAnalyticSpaceMatrix] using hh

/-- The spatial derivative is still holomorphic throughout both half-planes. -/
theorem analyticOnNhd_directAnalyticSpaceMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z => directAnalyticSpaceMatrix q t x z i j) {z : ℂ | z.im ≠ 0} :=
  analyticOnNhd_cauchyExtension _

/-- The spatial derivative of every off-contour entry depends jointly continuously on space and time. -/
theorem continuous_directAnalyticSpaceMatrix_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directAnalyticSpaceMatrix q p.1 p.2 (halfPlanePoint upper r a) i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => boundaryComponent (directRHSpaceDensity q p.1 p.2 i) j) := by
    fin_cases j
    · exact (continuous_directRHSpaceDensity_parameters q i).fst
    · exact (continuous_directRHSpaceDensity_parameters q i).snd
  have hh := (cauchyEvaluation upper r a).continuous.comp hc
  change Continuous (fun p : ℝ × ℝ => cauchyEvaluation upper r a (boundaryComponent (directRHSpaceDensity q p.1 p.2 i) j)) at hh
  simpa only [cauchyEvaluation_apply,directAnalyticSpaceMatrix] using hh

theorem directAnalyticMatrix_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x => directAnalyticMatrix q t x (halfPlanePoint upper r a) i j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directAnalyticMatrix_space_hasDerivAt q t x upper r a i j).differentiableAt,?_⟩
  have he : deriv (fun x => directAnalyticMatrix q t x (halfPlanePoint upper r a) i j) =
      fun x => directAnalyticSpaceMatrix q t x (halfPlanePoint upper r a) i j :=
    funext fun x => (directAnalyticMatrix_space_hasDerivAt q t x upper r a i j).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directAnalyticSpaceMatrix_parameters q upper r a i j).comp hc
  exact hh

/-- The differentiated trace carrier includes the actual boundary at height zero. -/
def directSpaceTrace (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) : Boundary :=
  (cauchyTrace (directRHSpaceDensity q t x i).1 upper h,cauchyTrace (directRHSpaceDensity q t x i).2 upper h)

/-- Strong spatial differentiation commutes with every fixed-height Cauchy trace. -/
theorem directTrace_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    HasDerivAt (fun s => directTrace q t s i upper h) (directSpaceTrace q t x i upper h) x := by
  have hd := directRHDensity_space_hasDerivAt q t x i
  have h0 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd.fst
  have h1 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd.snd
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHDensity q t s i).1)
    (cauchyTraceOperator upper h (directRHSpaceDensity q t x i).1) x at h0
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHDensity q t s i).2)
    (cauchyTraceOperator upper h (directRHSpaceDensity q t x i).2) x at h1
  simp only [cauchyTraceOperator_apply] at h0 h1
  exact h0.prodMk h1

/-- Space, time, and height vary jointly for the differentiated trace, including the boundary height. -/
theorem continuous_directSpaceTrace_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directSpaceTrace q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHSpaceDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchyTrace_joint upper).comp hp0
  have h1 := (continuous_cauchyTrace_joint upper).comp hp1
  exact h0.prodMk h1

/-- The derivative trace at height zero is exactly the derivative of the correct Hardy boundary value. -/
theorem directSpaceTrace_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    directSpaceTrace q t x i upper 0 =
      if upper then directUpperSpaceCorrection q t x i else directLowerSpaceCorrection q t x i := by
  cases upper
  · change (cauchyTrace _ false 0,cauchyTrace _ false 0) = _
    rw [cauchyTrace_lower_zero,cauchyTrace_lower_zero]
    exact directRHSpaceDensity_lower q t x i
  · change (cauchyTrace _ true 0,cauchyTrace _ true 0) = _
    rw [cauchyTrace_upper_zero,cauchyTrace_upper_zero]
    exact directRHSpaceDensity_upper q t x i

/-- Horizontal L² slices of the differentiated holomorphic reconstruction. -/
def directAnalyticSpaceSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) : Boundary :=
  (cauchySlice (directRHSpaceDensity q t x i).1 upper a,cauchySlice (directRHSpaceDensity q t x i).2 upper a)

theorem directSpaceTrace_exp_eq_analyticSpaceSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directSpaceTrace q t x i upper (Real.exp a) = directAnalyticSpaceSlice q t x i upper a :=
  Prod.ext (cauchySlice_eq_trace _ upper a).symm (cauchySlice_eq_trace _ upper a).symm

/-- These are actual Cauchy-integral slices of the spatial derivative matrix, almost everywhere. -/
theorem directAnalyticSpaceSlice_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    (fun r => (((directAnalyticSpaceSlice q t x i upper a).1 : ℝ → ℂ) r,
      ((directAnalyticSpaceSlice q t x i upper a).2 : ℝ → ℂ) r)) =ᵐ[volume]
    (fun r => (directAnalyticSpaceMatrix q t x (halfPlanePoint upper r a) i 0,
      directAnalyticSpaceMatrix q t x (halfPlanePoint upper r a) i 1)) := by
  filter_upwards [(cauchyExtension_slice_memLp (directRHSpaceDensity q t x i).1 upper a).coeFn_toLp,
    (cauchyExtension_slice_memLp (directRHSpaceDensity q t x i).2 upper a).coeFn_toLp] with r h0 h1
  exact Prod.ext h0 h1

/-- Space differentiation commutes with the actual horizontal holomorphic slices in L². -/
theorem directAnalyticSlice_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    HasDerivAt (fun s => directAnalyticSlice q t s i upper a) (directAnalyticSpaceSlice q t x i upper a) x := by
  have hd := directTrace_space_hasDerivAt q t x i upper (Real.exp a)
  simpa only [directTrace_exp_eq_analyticSlice,directSpaceTrace_exp_eq_analyticSpaceSlice] using hd

/-- The strong boundary limit of the spatial derivative equals the spatial derivative of the boundary. -/
theorem directAnalyticSpaceSlice_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticSpaceSlice q t x i upper) atBot
      (𝓝 (if upper then directUpperSpaceCorrection q t x i else directLowerSpaceCorrection q t x i)) := by
  have hp : Continuous (fun h : ℝ => ((t,x),h)) := continuous_const.prodMk continuous_id
  have hc := (continuous_directSpaceTrace_parameters q i upper).comp hp
  have hh := (hc.tendsto 0).comp Real.tendsto_exp_atBot
  change Tendsto (fun a => directSpaceTrace q t x i upper (Real.exp a)) atBot (𝓝 (directSpaceTrace q t x i upper 0)) at hh
  simpa only [directSpaceTrace_zero,directSpaceTrace_exp_eq_analyticSpaceSlice] using hh

/-- The spatial derivative slices decay strongly at infinite height. -/
theorem directAnalyticSpaceSlice_tendsto_atTop (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticSpaceSlice q t x i upper) atTop (𝓝 0) :=
  (cauchySlice_tendsto_atTop (directRHSpaceDensity q t x i).1 upper).prodMk_nhds
    (cauchySlice_tendsto_atTop (directRHSpaceDensity q t x i).2 upper)

/-- Differentiated slices are propagated from their own differentiated Hardy boundary values. -/
theorem directAnalyticSpaceSlice_eq_boundary_propagation (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directAnalyticSpaceSlice q t x i upper a =
      let b := if upper then directUpperSpaceCorrection q t x i else directLowerSpaceCorrection q t x i
      (hardyPropagation upper (Real.exp a) b.1,hardyPropagation upper (Real.exp a) b.2) := by
  have he := directSpaceTrace_zero q t x i upper
  apply Prod.ext
  · change cauchySlice (directRHSpaceDensity q t x i).1 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.fst he)
  · change cauchySlice (directRHSpaceDensity q t x i).2 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.snd he)

/-- The interior derivative cannot have more L² energy than its corresponding boundary derivative. -/
theorem directAnalyticSpaceSlice_boundary_norm_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSpaceSlice q t x i upper a‖ ≤
      ‖if upper then directUpperSpaceCorrection q t x i else directLowerSpaceCorrection q t x i‖ := by
  rw [directAnalyticSpaceSlice_eq_boundary_propagation]
  exact max_le_max (hardyPropagation_bound upper (Real.exp a) _) (hardyPropagation_bound upper (Real.exp a) _)

/-- The actual derivative slices vary jointly in time, position, and logarithmic height. -/
theorem continuous_directAnalyticSpaceSlice_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directAnalyticSpaceSlice q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHSpaceDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchySlice_joint upper).comp hp0
  have h1 := (continuous_cauchySlice_joint upper).comp hp1
  exact h0.prodMk h1

/-- The actual horizontal holomorphic slices are C¹ in position as L² vectors. -/
theorem directAnalyticSlice_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ContDiff ℝ 1 (fun x => directAnalyticSlice q t x i upper a) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directAnalyticSlice_space_hasDerivAt q t x i upper a).differentiableAt,?_⟩
  have he : deriv (fun x => directAnalyticSlice q t x i upper a) = fun x => directAnalyticSpaceSlice q t x i upper a :=
    funext fun x => (directAnalyticSlice_space_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => ((t,x),a)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hh := (continuous_directAnalyticSpaceSlice_parameters q i upper).comp hc
  exact hh

/-- Actual spatial differentiation commutes with the strong Plemelj boundary limit. -/
theorem directAnalyticSlice_space_deriv_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => deriv (fun s => directAnalyticSlice q t s i upper a) x) atBot
      (𝓝 (deriv (fun s => if upper then directUpperCorrection q t s i else directLowerCorrection q t s i) x)) := by
  have he : (fun a => deriv (fun s => directAnalyticSlice q t s i upper a) x) =
      directAnalyticSpaceSlice q t x i upper :=
    funext fun a => (directAnalyticSlice_space_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hh := directAnalyticSpaceSlice_boundary_tendsto q t x i upper
  cases upper
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directLowerCorrection q t s i) x))
    rw [(directLowerCorrection_space_hasDerivAt q t x i).deriv]
    exact hh
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directUpperCorrection q t s i) x))
    rw [(directUpperCorrection_space_hasDerivAt q t x i).deriv]
    exact hh

end
end RHTower.FokasLenells
