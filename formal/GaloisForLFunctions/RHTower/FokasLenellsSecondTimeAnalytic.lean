import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeBoundary
import GaloisForLFunctions.RHTower.FokasLenellsTimeAnalytic

/-!
# Second time differentiation commutes with holomorphic reconstruction

The actual compatible RH density supplies a second derivative of every
off-contour matrix entry and horizontal L2 slice. Its strong boundary
limit is the second derivative of the actual Hardy boundary value.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def compatibleAnalyticSecondTimeMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cauchyExtension (boundaryComponent (compatibleRHSecondTimeDensity q t x i) j) z

/-- The first derivative of the actual reconstructed matrix has a genuine second time derivative off the contour. -/
theorem directAnalyticTimeMatrix_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directAnalyticTimeMatrix (oddInitialPart q) s x (halfPlanePoint upper r a) i j)
      (compatibleAnalyticSecondTimeMatrix q t x (halfPlanePoint upper r a) i j) t := by
  have hd : HasDerivAt (fun s => boundaryComponent (directRHTimeDensity (oddInitialPart q) s x i) j)
      (boundaryComponent (compatibleRHSecondTimeDensity q t x i) j) t := by
    fin_cases j
    · exact (directRHTimeDensity_oddInitialPart_hasDerivAt q t x i).fst
    · exact (directRHTimeDensity_oddInitialPart_hasDerivAt q t x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => cauchyEvaluation upper r a (boundaryComponent (directRHTimeDensity (oddInitialPart q) s x i) j))
    (cauchyEvaluation upper r a (boundaryComponent (compatibleRHSecondTimeDensity q t x i) j)) t at he
  simpa only [cauchyEvaluation_apply,directAnalyticTimeMatrix,compatibleAnalyticSecondTimeMatrix] using he

/-- The second time derivative remains holomorphic in both open half-planes. -/
theorem analyticOnNhd_compatibleAnalyticSecondTimeMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z => compatibleAnalyticSecondTimeMatrix q t x z i j) {z : ℂ | z.im ≠ 0} :=
  analyticOnNhd_cauchyExtension _

theorem continuous_compatibleAnalyticSecondTimeMatrix_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleAnalyticSecondTimeMatrix q p.1 p.2 (halfPlanePoint upper r a) i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => boundaryComponent (compatibleRHSecondTimeDensity q p.1 p.2 i) j) := by
    fin_cases j
    · exact (continuous_compatibleRHSecondTimeDensity_parameters q i).fst
    · exact (continuous_compatibleRHSecondTimeDensity_parameters q i).snd
  have hh := (cauchyEvaluation upper r a).continuous.comp hc
  change Continuous (fun p : ℝ × ℝ => cauchyEvaluation upper r a (boundaryComponent (compatibleRHSecondTimeDensity q p.1 p.2 i) j)) at hh
  simpa only [cauchyEvaluation_apply,compatibleAnalyticSecondTimeMatrix] using hh

/-- The actual normalized holomorphic RH reconstruction is globally C2 in time at every off-contour point. -/
theorem directAnalyticMatrix_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    ContDiff ℝ 2 (fun t => directAnalyticMatrix (oddInitialPart q) t x (halfPlanePoint upper r a) i j) := by
  have hc : ContDiff ℝ 2 (fun t => boundaryComponent (directRHDensity (oddInitialPart q) t x i) j) := by
    fin_cases j
    · exact (directRHDensity_oddInitialPart_time_contDiff_two q x i).fst
    · exact (directRHDensity_oddInitialPart_time_contDiff_two q x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).contDiff.comp hc
  have hh := (contDiff_const (c := ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j))).add he
  change ContDiff ℝ 2 (fun t => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j+
    cauchyEvaluation upper r a (boundaryComponent (directRHDensity (oddInitialPart q) t x i) j)) at hh
  simpa only [cauchyEvaluation_apply,directAnalyticMatrix] using hh

def compatibleSecondTimeTrace (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) : Boundary :=
  (cauchyTrace (compatibleRHSecondTimeDensity q t x i).1 upper h,cauchyTrace (compatibleRHSecondTimeDensity q t x i).2 upper h)

/-- A second strong time derivative commutes with every fixed-height Cauchy trace, including the boundary. -/
theorem directTimeTrace_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    HasDerivAt (fun s => directTimeTrace (oddInitialPart q) s x i upper h) (compatibleSecondTimeTrace q t x i upper h) t := by
  have hd := directRHTimeDensity_oddInitialPart_hasDerivAt q t x i
  have h0 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.fst
  have h1 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.snd
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHTimeDensity (oddInitialPart q) s x i).1)
    (cauchyTraceOperator upper h (compatibleRHSecondTimeDensity q t x i).1) t at h0
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHTimeDensity (oddInitialPart q) s x i).2)
    (cauchyTraceOperator upper h (compatibleRHSecondTimeDensity q t x i).2) t at h1
  simp only [cauchyTraceOperator_apply] at h0 h1
  exact h0.prodMk h1

theorem continuous_compatibleSecondTimeTrace_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => compatibleSecondTimeTrace q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_compatibleRHSecondTimeDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchyTrace_joint upper).comp hp0
  have h1 := (continuous_cauchyTrace_joint upper).comp hp1
  exact h0.prodMk h1

theorem compatibleSecondTimeTrace_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    compatibleSecondTimeTrace q t x i upper 0 =
      if upper then compatibleUpperSecondTimeCorrection q t x i else compatibleLowerSecondTimeCorrection q t x i := by
  cases upper
  · change (cauchyTrace _ false 0,cauchyTrace _ false 0) = _
    rw [cauchyTrace_lower_zero,cauchyTrace_lower_zero]
    exact compatibleRHSecondTimeDensity_lower q t x i
  · change (cauchyTrace _ true 0,cauchyTrace _ true 0) = _
    rw [cauchyTrace_upper_zero,cauchyTrace_upper_zero]
    exact compatibleRHSecondTimeDensity_upper q t x i

def compatibleAnalyticSecondTimeSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) : Boundary :=
  (cauchySlice (compatibleRHSecondTimeDensity q t x i).1 upper a,cauchySlice (compatibleRHSecondTimeDensity q t x i).2 upper a)

theorem compatibleSecondTimeTrace_exp_eq_analyticSecondTimeSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    compatibleSecondTimeTrace q t x i upper (Real.exp a) = compatibleAnalyticSecondTimeSlice q t x i upper a :=
  Prod.ext (cauchySlice_eq_trace _ upper a).symm (cauchySlice_eq_trace _ upper a).symm

/-- The Hilbert-space second derivative slices are the actual Cauchy-integral matrix entries almost everywhere. -/
theorem compatibleAnalyticSecondTimeSlice_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    (fun r => (((compatibleAnalyticSecondTimeSlice q t x i upper a).1 : ℝ → ℂ) r,
      ((compatibleAnalyticSecondTimeSlice q t x i upper a).2 : ℝ → ℂ) r)) =ᵐ[volume]
    (fun r => (compatibleAnalyticSecondTimeMatrix q t x (halfPlanePoint upper r a) i 0,
      compatibleAnalyticSecondTimeMatrix q t x (halfPlanePoint upper r a) i 1)) := by
  filter_upwards [(cauchyExtension_slice_memLp (compatibleRHSecondTimeDensity q t x i).1 upper a).coeFn_toLp,
    (cauchyExtension_slice_memLp (compatibleRHSecondTimeDensity q t x i).2 upper a).coeFn_toLp] with r h0 h1
  exact Prod.ext h0 h1

theorem directAnalyticTimeSlice_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    HasDerivAt (fun s => directAnalyticTimeSlice (oddInitialPart q) s x i upper a) (compatibleAnalyticSecondTimeSlice q t x i upper a) t := by
  have hd := directTimeTrace_oddInitialPart_hasDerivAt q t x i upper (Real.exp a)
  simpa only [directTimeTrace_exp_eq_analyticTimeSlice,compatibleSecondTimeTrace_exp_eq_analyticSecondTimeSlice] using hd

/-- The second strong time derivative of the holomorphic slice tends to the actual second derivative of its Hardy boundary. -/
theorem compatibleAnalyticSecondTimeSlice_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (compatibleAnalyticSecondTimeSlice q t x i upper) atBot
      (𝓝 (if upper then compatibleUpperSecondTimeCorrection q t x i else compatibleLowerSecondTimeCorrection q t x i)) := by
  have hp : Continuous (fun h : ℝ => ((t,x),h)) := continuous_const.prodMk continuous_id
  have hc := (continuous_compatibleSecondTimeTrace_parameters q i upper).comp hp
  have hh := (hc.tendsto 0).comp Real.tendsto_exp_atBot
  change Tendsto (fun a => compatibleSecondTimeTrace q t x i upper (Real.exp a)) atBot
    (𝓝 (compatibleSecondTimeTrace q t x i upper 0)) at hh
  simpa only [compatibleSecondTimeTrace_zero,compatibleSecondTimeTrace_exp_eq_analyticSecondTimeSlice] using hh

theorem compatibleAnalyticSecondTimeSlice_tendsto_atTop (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (compatibleAnalyticSecondTimeSlice q t x i upper) atTop (𝓝 0) :=
  (cauchySlice_tendsto_atTop (compatibleRHSecondTimeDensity q t x i).1 upper).prodMk_nhds
    (cauchySlice_tendsto_atTop (compatibleRHSecondTimeDensity q t x i).2 upper)

theorem compatibleAnalyticSecondTimeSlice_eq_boundary_propagation (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    compatibleAnalyticSecondTimeSlice q t x i upper a =
      let b := if upper then compatibleUpperSecondTimeCorrection q t x i else compatibleLowerSecondTimeCorrection q t x i
      (hardyPropagation upper (Real.exp a) b.1,hardyPropagation upper (Real.exp a) b.2) := by
  have he := compatibleSecondTimeTrace_zero q t x i upper
  apply Prod.ext
  · change cauchySlice (compatibleRHSecondTimeDensity q t x i).1 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.fst he)
  · change cauchySlice (compatibleRHSecondTimeDensity q t x i).2 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.snd he)

/-- The actual second derivative has no more L2 energy in the interior than on its Hardy boundary. -/
theorem compatibleAnalyticSecondTimeSlice_boundary_norm_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖compatibleAnalyticSecondTimeSlice q t x i upper a‖ ≤
      ‖if upper then compatibleUpperSecondTimeCorrection q t x i else compatibleLowerSecondTimeCorrection q t x i‖ := by
  rw [compatibleAnalyticSecondTimeSlice_eq_boundary_propagation]
  exact max_le_max (hardyPropagation_bound upper (Real.exp a) _) (hardyPropagation_bound upper (Real.exp a) _)

theorem continuous_compatibleAnalyticSecondTimeSlice_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => compatibleAnalyticSecondTimeSlice q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_compatibleRHSecondTimeDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchySlice_joint upper).comp hp0
  have h1 := (continuous_cauchySlice_joint upper).comp hp1
  exact h0.prodMk h1

/-- The actual horizontal holomorphic slices are globally C2 in time as Hilbert-space vectors. -/
theorem directAnalyticSlice_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ContDiff ℝ 2 (fun t => directAnalyticSlice (oddInitialPart q) t x i upper a) := by
  have hc := directRHDensity_oddInitialPart_time_contDiff_two q x i
  have h0 := ((cauchyTraceOperator upper (Real.exp a)).restrictScalars ℝ).contDiff.comp hc.fst
  have h1 := ((cauchyTraceOperator upper (Real.exp a)).restrictScalars ℝ).contDiff.comp hc.snd
  have hh := h0.prodMk h1
  change ContDiff ℝ 2 (fun t => (cauchyTraceOperator upper (Real.exp a) (directRHDensity (oddInitialPart q) t x i).1,
    cauchyTraceOperator upper (Real.exp a) (directRHDensity (oddInitialPart q) t x i).2)) at hh
  simpa only [cauchyTraceOperator_apply,← cauchySlice_eq_trace,directAnalyticSlice] using hh

/-- Second time differentiation commutes with the strong Plemelj boundary limit. -/
theorem directAnalyticSlice_second_time_deriv_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => deriv (deriv (fun s => directAnalyticSlice (oddInitialPart q) s x i upper a)) t) atBot
      (𝓝 (deriv (deriv (fun s => if upper then directUpperCorrection (oddInitialPart q) s x i
        else directLowerCorrection (oddInitialPart q) s x i)) t)) := by
  have he : (fun a => deriv (deriv (fun s => directAnalyticSlice (oddInitialPart q) s x i upper a)) t) =
      compatibleAnalyticSecondTimeSlice q t x i upper := by
    funext a
    have h1 : deriv (fun s => directAnalyticSlice (oddInitialPart q) s x i upper a) =
        fun s => directAnalyticTimeSlice (oddInitialPart q) s x i upper a :=
      funext fun s => (directAnalyticSlice_time_hasDerivAt _ s x i upper a).deriv
    rw [h1]
    exact (directAnalyticTimeSlice_oddInitialPart_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hh := compatibleAnalyticSecondTimeSlice_boundary_tendsto q t x i upper
  cases upper
  · change Tendsto _ atBot (𝓝 (deriv (deriv (fun s => directLowerCorrection (oddInitialPart q) s x i)) t))
    have h1 : deriv (fun s => directLowerCorrection (oddInitialPart q) s x i) =
        fun s => directLowerTimeCorrection (oddInitialPart q) s x i :=
      funext fun s => (directLowerCorrection_time_hasDerivAt _ s x i).deriv
    rw [h1,(directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i).deriv]
    exact hh
  · change Tendsto _ atBot (𝓝 (deriv (deriv (fun s => directUpperCorrection (oddInitialPart q) s x i)) t))
    have h1 : deriv (fun s => directUpperCorrection (oddInitialPart q) s x i) =
        fun s => directUpperTimeCorrection (oddInitialPart q) s x i :=
      funext fun s => (directUpperCorrection_time_hasDerivAt _ s x i).deriv
    rw [h1,(directUpperTimeCorrection_oddInitialPart_hasDerivAt q t x i).deriv]
    exact hh

end
end RHTower.FokasLenells
