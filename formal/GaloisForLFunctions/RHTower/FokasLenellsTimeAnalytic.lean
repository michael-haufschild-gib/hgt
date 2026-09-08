import GaloisForLFunctions.RHTower.FokasLenellsTimeBoundary
import GaloisForLFunctions.RHTower.FokasLenellsCauchySemigroup

/-!
# Time differentiation through holomorphic reconstruction and Plemelj limits

Bounded Cauchy evaluation and signed Hardy propagation carry the proved L²
density derivative into actual holomorphic matrix entries and horizontal
slices. Time differentiation commutes with both strong boundary limits.
The differentiated slices stay holomorphic, decay at infinite height, and
inherit their own differentiated Hardy boundary values.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Time differentiation of the actual holomorphic reconstruction replaces its density by its derivative. -/
def directAnalyticTimeMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cauchyExtension (boundaryComponent (directRHTimeDensity q t x i) j) z

/-- Every off-contour reconstructed entry has the genuine time derivative given by the differentiated Cauchy integral. -/
theorem directAnalyticMatrix_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directAnalyticMatrix q s x (halfPlanePoint upper r a) i j)
      (directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i j) t := by
  have hd : HasDerivAt (fun s => boundaryComponent (directRHDensity q s x i) j)
      (boundaryComponent (directRHTimeDensity q t x i) j) t := by
    fin_cases j
    · exact (directRHDensity_time_hasDerivAt q t x i).fst
    · exact (directRHDensity_time_hasDerivAt q t x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => cauchyEvaluation upper r a (boundaryComponent (directRHDensity q s x i) j))
    (cauchyEvaluation upper r a (boundaryComponent (directRHTimeDensity q t x i) j)) t at he
  have hh := he.const_add ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  simpa only [cauchyEvaluation_apply,directAnalyticMatrix,directAnalyticTimeMatrix] using hh

/-- The time derivative is still holomorphic throughout both half-planes. -/
theorem analyticOnNhd_directAnalyticTimeMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z => directAnalyticTimeMatrix q t x z i j) {z : ℂ | z.im ≠ 0} :=
  analyticOnNhd_cauchyExtension _

/-- The time derivative of every off-contour entry depends jointly continuously on space and time. -/
theorem continuous_directAnalyticTimeMatrix_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directAnalyticTimeMatrix q p.1 p.2 (halfPlanePoint upper r a) i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => boundaryComponent (directRHTimeDensity q p.1 p.2 i) j) := by
    fin_cases j
    · exact (continuous_directRHTimeDensity_parameters q i).fst
    · exact (continuous_directRHTimeDensity_parameters q i).snd
  have hh := (cauchyEvaluation upper r a).continuous.comp hc
  change Continuous (fun p : ℝ × ℝ => cauchyEvaluation upper r a (boundaryComponent (directRHTimeDensity q p.1 p.2 i) j)) at hh
  simpa only [cauchyEvaluation_apply,directAnalyticTimeMatrix] using hh

theorem directAnalyticMatrix_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun t => directAnalyticMatrix q t x (halfPlanePoint upper r a) i j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directAnalyticMatrix_time_hasDerivAt q t x upper r a i j).differentiableAt,?_⟩
  have he : deriv (fun t => directAnalyticMatrix q t x (halfPlanePoint upper r a) i j) =
      fun t => directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i j :=
    funext fun t => (directAnalyticMatrix_time_hasDerivAt q t x upper r a i j).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directAnalyticTimeMatrix_parameters q upper r a i j).comp hc
  exact hh

/-- The existing Cauchy trace is a bounded linear operator on its density at every height, including zero. -/
def cauchyTraceOperator (upper : Bool) (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  (if upper then (1 : ℂ) else -1) • hardyPropagation upper h

theorem cauchyTraceOperator_apply (upper : Bool) (h : ℝ) (u : SoninL2) :
    cauchyTraceOperator upper h u = cauchyTrace u upper h := rfl

/-- The differentiated trace carrier includes the actual boundary at height zero. -/
def directTimeTrace (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) : Boundary :=
  (cauchyTrace (directRHTimeDensity q t x i).1 upper h,cauchyTrace (directRHTimeDensity q t x i).2 upper h)

/-- Strong time differentiation commutes with every fixed-height Cauchy trace. -/
theorem directTrace_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    HasDerivAt (fun s => directTrace q s x i upper h) (directTimeTrace q t x i upper h) t := by
  have hd := directRHDensity_time_hasDerivAt q t x i
  have h0 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.fst
  have h1 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.snd
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHDensity q s x i).1)
    (cauchyTraceOperator upper h (directRHTimeDensity q t x i).1) t at h0
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHDensity q s x i).2)
    (cauchyTraceOperator upper h (directRHTimeDensity q t x i).2) t at h1
  simp only [cauchyTraceOperator_apply] at h0 h1
  exact h0.prodMk h1

/-- Space, time, and height vary jointly for the differentiated trace, including the boundary height. -/
theorem continuous_directTimeTrace_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directTimeTrace q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHTimeDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchyTrace_joint upper).comp hp0
  have h1 := (continuous_cauchyTrace_joint upper).comp hp1
  exact h0.prodMk h1

/-- The derivative trace at height zero is exactly the derivative of the correct Hardy boundary value. -/
theorem directTimeTrace_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    directTimeTrace q t x i upper 0 =
      if upper then directUpperTimeCorrection q t x i else directLowerTimeCorrection q t x i := by
  cases upper
  · change (cauchyTrace _ false 0,cauchyTrace _ false 0) = _
    rw [cauchyTrace_lower_zero,cauchyTrace_lower_zero]
    exact directRHTimeDensity_lower q t x i
  · change (cauchyTrace _ true 0,cauchyTrace _ true 0) = _
    rw [cauchyTrace_upper_zero,cauchyTrace_upper_zero]
    exact directRHTimeDensity_upper q t x i

/-- Horizontal L² slices of the differentiated holomorphic reconstruction. -/
def directAnalyticTimeSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) : Boundary :=
  (cauchySlice (directRHTimeDensity q t x i).1 upper a,cauchySlice (directRHTimeDensity q t x i).2 upper a)

theorem directTimeTrace_exp_eq_analyticTimeSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directTimeTrace q t x i upper (Real.exp a) = directAnalyticTimeSlice q t x i upper a :=
  Prod.ext (cauchySlice_eq_trace _ upper a).symm (cauchySlice_eq_trace _ upper a).symm

/-- These are actual Cauchy-integral slices of the time derivative matrix, almost everywhere. -/
theorem directAnalyticTimeSlice_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    (fun r => (((directAnalyticTimeSlice q t x i upper a).1 : ℝ → ℂ) r,
      ((directAnalyticTimeSlice q t x i upper a).2 : ℝ → ℂ) r)) =ᵐ[volume]
    (fun r => (directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i 0,
      directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i 1)) := by
  filter_upwards [(cauchyExtension_slice_memLp (directRHTimeDensity q t x i).1 upper a).coeFn_toLp,
    (cauchyExtension_slice_memLp (directRHTimeDensity q t x i).2 upper a).coeFn_toLp] with r h0 h1
  exact Prod.ext h0 h1

/-- Time differentiation commutes with the actual horizontal holomorphic slices in L². -/
theorem directAnalyticSlice_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    HasDerivAt (fun s => directAnalyticSlice q s x i upper a) (directAnalyticTimeSlice q t x i upper a) t := by
  have hd := directTrace_time_hasDerivAt q t x i upper (Real.exp a)
  simpa only [directTrace_exp_eq_analyticSlice,directTimeTrace_exp_eq_analyticTimeSlice] using hd

/-- The strong boundary limit of the time derivative equals the time derivative of the boundary. -/
theorem directAnalyticTimeSlice_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticTimeSlice q t x i upper) atBot
      (𝓝 (if upper then directUpperTimeCorrection q t x i else directLowerTimeCorrection q t x i)) := by
  have hp : Continuous (fun h : ℝ => ((t,x),h)) := continuous_const.prodMk continuous_id
  have hc := (continuous_directTimeTrace_parameters q i upper).comp hp
  have hh := (hc.tendsto 0).comp Real.tendsto_exp_atBot
  change Tendsto (fun a => directTimeTrace q t x i upper (Real.exp a)) atBot (𝓝 (directTimeTrace q t x i upper 0)) at hh
  simpa only [directTimeTrace_zero,directTimeTrace_exp_eq_analyticTimeSlice] using hh

/-- The time derivative slices decay strongly at infinite height. -/
theorem directAnalyticTimeSlice_tendsto_atTop (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticTimeSlice q t x i upper) atTop (𝓝 0) :=
  (cauchySlice_tendsto_atTop (directRHTimeDensity q t x i).1 upper).prodMk_nhds
    (cauchySlice_tendsto_atTop (directRHTimeDensity q t x i).2 upper)

/-- Differentiated slices are propagated from their own differentiated Hardy boundary values. -/
theorem directAnalyticTimeSlice_eq_boundary_propagation (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directAnalyticTimeSlice q t x i upper a =
      let b := if upper then directUpperTimeCorrection q t x i else directLowerTimeCorrection q t x i
      (hardyPropagation upper (Real.exp a) b.1,hardyPropagation upper (Real.exp a) b.2) := by
  have he := directTimeTrace_zero q t x i upper
  apply Prod.ext
  · change cauchySlice (directRHTimeDensity q t x i).1 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.fst he)
  · change cauchySlice (directRHTimeDensity q t x i).2 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.snd he)

/-- The interior derivative cannot have more L² energy than its corresponding boundary derivative. -/
theorem directAnalyticTimeSlice_boundary_norm_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticTimeSlice q t x i upper a‖ ≤
      ‖if upper then directUpperTimeCorrection q t x i else directLowerTimeCorrection q t x i‖ := by
  rw [directAnalyticTimeSlice_eq_boundary_propagation]
  exact max_le_max (hardyPropagation_bound upper (Real.exp a) _) (hardyPropagation_bound upper (Real.exp a) _)

/-- The actual derivative slices vary jointly in time, position, and logarithmic height. -/
theorem continuous_directAnalyticTimeSlice_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directAnalyticTimeSlice q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHTimeDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchySlice_joint upper).comp hp0
  have h1 := (continuous_cauchySlice_joint upper).comp hp1
  exact h0.prodMk h1

/-- The actual horizontal holomorphic slices are C¹ in time as L² vectors. -/
theorem directAnalyticSlice_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ContDiff ℝ 1 (fun t => directAnalyticSlice q t x i upper a) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directAnalyticSlice_time_hasDerivAt q t x i upper a).differentiableAt,?_⟩
  have he : deriv (fun t => directAnalyticSlice q t x i upper a) = fun t => directAnalyticTimeSlice q t x i upper a :=
    funext fun t => (directAnalyticSlice_time_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => ((t,x),a)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hh := (continuous_directAnalyticTimeSlice_parameters q i upper).comp hc
  exact hh

/-- Actual time differentiation commutes with the strong Plemelj boundary limit. -/
theorem directAnalyticSlice_time_deriv_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => deriv (fun s => directAnalyticSlice q s x i upper a) t) atBot
      (𝓝 (deriv (fun s => if upper then directUpperCorrection q s x i else directLowerCorrection q s x i) t)) := by
  have he : (fun a => deriv (fun s => directAnalyticSlice q s x i upper a) t) =
      directAnalyticTimeSlice q t x i upper :=
    funext fun a => (directAnalyticSlice_time_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hh := directAnalyticTimeSlice_boundary_tendsto q t x i upper
  cases upper
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directLowerCorrection q s x i) t))
    rw [(directLowerCorrection_time_hasDerivAt q t x i).deriv]
    exact hh
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directUpperCorrection q s x i) t))
    rw [(directUpperCorrection_time_hasDerivAt q t x i).deriv]
    exact hh

end
end RHTower.FokasLenells
