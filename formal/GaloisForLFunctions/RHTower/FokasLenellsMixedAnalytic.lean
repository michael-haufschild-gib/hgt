import GaloisForLFunctions.RHTower.FokasLenellsMixedBoundary
import GaloisForLFunctions.RHTower.FokasLenellsSpaceAnalytic

/-!
# Mixed differentiation and actual holomorphic boundary reconstruction

Both physical differentiation orders give the same Cauchy integral of the
mixed reconstruction density. Its horizontal slices converge strongly to
both mixed Hardy boundary values. This transports the paper's phase identity
through the actual inverse and holomorphic reconstruction.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Mixed differentiation of the actual holomorphic reconstruction replaces its density by its derivative. -/
def directAnalyticMixedMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => cauchyExtension (boundaryComponent (directRHMixedDensity q t x i) j) z

/-- Every off-contour reconstructed entry has the genuine spatial derivative given by the differentiated Cauchy integral. -/
theorem directAnalyticTimeMatrix_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directAnalyticTimeMatrix q t s (halfPlanePoint upper r a) i j)
      (directAnalyticMixedMatrix q t x (halfPlanePoint upper r a) i j) x := by
  have hd : HasDerivAt (fun s => boundaryComponent (directRHTimeDensity q t s i) j)
      (boundaryComponent (directRHMixedDensity q t x i) j) x := by
    fin_cases j
    · exact (directRHTimeDensity_space_hasDerivAt q t x i).fst
    · exact (directRHTimeDensity_space_hasDerivAt q t x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd
  change HasDerivAt (fun s => cauchyEvaluation upper r a (boundaryComponent (directRHTimeDensity q t s i) j))
    (cauchyEvaluation upper r a (boundaryComponent (directRHMixedDensity q t x i) j)) x at he
  simpa only [cauchyEvaluation_apply,directAnalyticTimeMatrix,directAnalyticMixedMatrix] using he

/-- The mixed derivative is still holomorphic throughout both half-planes. -/
theorem analyticOnNhd_directAnalyticMixedMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z => directAnalyticMixedMatrix q t x z i j) {z : ℂ | z.im ≠ 0} :=
  analyticOnNhd_cauchyExtension _

/-- The mixed derivative of every off-contour entry depends jointly continuously on space and time. -/
theorem continuous_directAnalyticMixedMatrix_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directAnalyticMixedMatrix q p.1 p.2 (halfPlanePoint upper r a) i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => boundaryComponent (directRHMixedDensity q p.1 p.2 i) j) := by
    fin_cases j
    · exact (continuous_directRHMixedDensity_parameters q i).fst
    · exact (continuous_directRHMixedDensity_parameters q i).snd
  have hh := (cauchyEvaluation upper r a).continuous.comp hc
  change Continuous (fun p : ℝ × ℝ => cauchyEvaluation upper r a (boundaryComponent (directRHMixedDensity q p.1 p.2 i) j)) at hh
  simpa only [cauchyEvaluation_apply,directAnalyticMixedMatrix] using hh

theorem directAnalyticTimeMatrix_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x => directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directAnalyticTimeMatrix_space_hasDerivAt q t x upper r a i j).differentiableAt,?_⟩
  have he : deriv (fun x => directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i j) =
      fun x => directAnalyticMixedMatrix q t x (halfPlanePoint upper r a) i j :=
    funext fun x => (directAnalyticTimeMatrix_space_hasDerivAt q t x upper r a i j).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directAnalyticMixedMatrix_parameters q upper r a i j).comp hc
  exact hh

/-- The differentiated trace carrier includes the actual boundary at height zero. -/
def directMixedTrace (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) : Boundary :=
  (cauchyTrace (directRHMixedDensity q t x i).1 upper h,cauchyTrace (directRHMixedDensity q t x i).2 upper h)

/-- Strong spatial differentiation commutes with every fixed-height Cauchy trace. -/
theorem directTimeTrace_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    HasDerivAt (fun s => directTimeTrace q t s i upper h) (directMixedTrace q t x i upper h) x := by
  have hd := directRHTimeDensity_space_hasDerivAt q t x i
  have h0 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd.fst
  have h1 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd.snd
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHTimeDensity q t s i).1)
    (cauchyTraceOperator upper h (directRHMixedDensity q t x i).1) x at h0
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHTimeDensity q t s i).2)
    (cauchyTraceOperator upper h (directRHMixedDensity q t x i).2) x at h1
  simp only [cauchyTraceOperator_apply] at h0 h1
  exact h0.prodMk h1

/-- Space, time, and height vary jointly for the differentiated trace, including the boundary height. -/
theorem continuous_directMixedTrace_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directMixedTrace q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHMixedDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchyTrace_joint upper).comp hp0
  have h1 := (continuous_cauchyTrace_joint upper).comp hp1
  exact h0.prodMk h1

/-- The derivative trace at height zero is exactly the derivative of the correct Hardy boundary value. -/
theorem directMixedTrace_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    directMixedTrace q t x i upper 0 =
      if upper then directUpperMixedCorrection q t x i else directLowerMixedCorrection q t x i := by
  cases upper
  · change (cauchyTrace _ false 0,cauchyTrace _ false 0) = _
    rw [cauchyTrace_lower_zero,cauchyTrace_lower_zero]
    exact directRHMixedDensity_lower q t x i
  · change (cauchyTrace _ true 0,cauchyTrace _ true 0) = _
    rw [cauchyTrace_upper_zero,cauchyTrace_upper_zero]
    exact directRHMixedDensity_upper q t x i

/-- Horizontal L² slices of the differentiated holomorphic reconstruction. -/
def directAnalyticMixedSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) : Boundary :=
  (cauchySlice (directRHMixedDensity q t x i).1 upper a,cauchySlice (directRHMixedDensity q t x i).2 upper a)

theorem directMixedTrace_exp_eq_analyticMixedSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directMixedTrace q t x i upper (Real.exp a) = directAnalyticMixedSlice q t x i upper a :=
  Prod.ext (cauchySlice_eq_trace _ upper a).symm (cauchySlice_eq_trace _ upper a).symm

/-- These are actual Cauchy-integral slices of the mixed derivative matrix, almost everywhere. -/
theorem directAnalyticMixedSlice_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    (fun r => (((directAnalyticMixedSlice q t x i upper a).1 : ℝ → ℂ) r,
      ((directAnalyticMixedSlice q t x i upper a).2 : ℝ → ℂ) r)) =ᵐ[volume]
    (fun r => (directAnalyticMixedMatrix q t x (halfPlanePoint upper r a) i 0,
      directAnalyticMixedMatrix q t x (halfPlanePoint upper r a) i 1)) := by
  filter_upwards [(cauchyExtension_slice_memLp (directRHMixedDensity q t x i).1 upper a).coeFn_toLp,
    (cauchyExtension_slice_memLp (directRHMixedDensity q t x i).2 upper a).coeFn_toLp] with r h0 h1
  exact Prod.ext h0 h1

/-- Mixed differentiation commutes with the actual horizontal holomorphic slices in L². -/
theorem directAnalyticTimeSlice_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    HasDerivAt (fun s => directAnalyticTimeSlice q t s i upper a) (directAnalyticMixedSlice q t x i upper a) x := by
  have hd := directTimeTrace_space_hasDerivAt q t x i upper (Real.exp a)
  simpa only [directTimeTrace_exp_eq_analyticTimeSlice,directMixedTrace_exp_eq_analyticMixedSlice] using hd

/-- The strong boundary limit of the mixed derivative equals the mixed derivative of the boundary. -/
theorem directAnalyticMixedSlice_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticMixedSlice q t x i upper) atBot
      (𝓝 (if upper then directUpperMixedCorrection q t x i else directLowerMixedCorrection q t x i)) := by
  have hp : Continuous (fun h : ℝ => ((t,x),h)) := continuous_const.prodMk continuous_id
  have hc := (continuous_directMixedTrace_parameters q i upper).comp hp
  have hh := (hc.tendsto 0).comp Real.tendsto_exp_atBot
  change Tendsto (fun a => directMixedTrace q t x i upper (Real.exp a)) atBot (𝓝 (directMixedTrace q t x i upper 0)) at hh
  simpa only [directMixedTrace_zero,directMixedTrace_exp_eq_analyticMixedSlice] using hh

/-- The mixed derivative slices decay strongly at infinite height. -/
theorem directAnalyticMixedSlice_tendsto_atTop (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (directAnalyticMixedSlice q t x i upper) atTop (𝓝 0) :=
  (cauchySlice_tendsto_atTop (directRHMixedDensity q t x i).1 upper).prodMk_nhds
    (cauchySlice_tendsto_atTop (directRHMixedDensity q t x i).2 upper)

/-- Differentiated slices are propagated from their own differentiated Hardy boundary values. -/
theorem directAnalyticMixedSlice_eq_boundary_propagation (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directAnalyticMixedSlice q t x i upper a =
      let b := if upper then directUpperMixedCorrection q t x i else directLowerMixedCorrection q t x i
      (hardyPropagation upper (Real.exp a) b.1,hardyPropagation upper (Real.exp a) b.2) := by
  have he := directMixedTrace_zero q t x i upper
  apply Prod.ext
  · change cauchySlice (directRHMixedDensity q t x i).1 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.fst he)
  · change cauchySlice (directRHMixedDensity q t x i).2 upper a = _
    rw [cauchySlice_eq_trace,cauchyTrace_eq_propagated_boundary]
    exact congrArg (hardyPropagation upper (Real.exp a)) (congrArg Prod.snd he)

/-- The interior derivative cannot have more L² energy than its corresponding boundary derivative. -/
theorem directAnalyticMixedSlice_boundary_norm_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticMixedSlice q t x i upper a‖ ≤
      ‖if upper then directUpperMixedCorrection q t x i else directLowerMixedCorrection q t x i‖ := by
  rw [directAnalyticMixedSlice_eq_boundary_propagation]
  exact max_le_max (hardyPropagation_bound upper (Real.exp a) _) (hardyPropagation_bound upper (Real.exp a) _)

/-- The actual derivative slices vary jointly in time, position, and logarithmic height. -/
theorem continuous_directAnalyticMixedSlice_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directAnalyticMixedSlice q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHMixedDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hp0 := continuous_snd.prodMk hd.fst
  have hp1 := continuous_snd.prodMk hd.snd
  have h0 := (continuous_cauchySlice_joint upper).comp hp0
  have h1 := (continuous_cauchySlice_joint upper).comp hp1
  exact h0.prodMk h1

/-- The actual horizontal holomorphic slices are C¹ in position as L² vectors. -/
theorem directAnalyticTimeSlice_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ContDiff ℝ 1 (fun x => directAnalyticTimeSlice q t x i upper a) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directAnalyticTimeSlice_space_hasDerivAt q t x i upper a).differentiableAt,?_⟩
  have he : deriv (fun x => directAnalyticTimeSlice q t x i upper a) = fun x => directAnalyticMixedSlice q t x i upper a :=
    funext fun x => (directAnalyticTimeSlice_space_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => ((t,x),a)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hh := (continuous_directAnalyticMixedSlice_parameters q i upper).comp hc
  exact hh

/-- Actual spatial differentiation commutes with the strong Plemelj boundary limit. -/
theorem directAnalyticTimeSlice_space_deriv_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => deriv (fun s => directAnalyticTimeSlice q t s i upper a) x) atBot
      (𝓝 (deriv (fun s => if upper then directUpperTimeCorrection q t s i else directLowerTimeCorrection q t s i) x)) := by
  have he : (fun a => deriv (fun s => directAnalyticTimeSlice q t s i upper a) x) =
      directAnalyticMixedSlice q t x i upper :=
    funext fun a => (directAnalyticTimeSlice_space_hasDerivAt q t x i upper a).deriv
  rw [he]
  have hh := directAnalyticMixedSlice_boundary_tendsto q t x i upper
  cases upper
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directLowerTimeCorrection q t s i) x))
    rw [(directLowerTimeCorrection_space_hasDerivAt q t x i).deriv]
    exact hh
  · change Tendsto _ atBot (𝓝 (deriv (fun s => directUpperTimeCorrection q t s i) x))
    rw [(directUpperTimeCorrection_space_hasDerivAt q t x i).deriv]
    exact hh

theorem directAnalyticSpaceMatrix_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directAnalyticSpaceMatrix q s x (halfPlanePoint upper r a) i j)
      (directAnalyticMixedMatrix q t x (halfPlanePoint upper r a) i j) t := by
  have hd : HasDerivAt (fun s => boundaryComponent (directRHSpaceDensity q s x i) j)
      (boundaryComponent (directRHMixedDensity q t x i) j) t := by
    fin_cases j
    · exact (directRHSpaceDensity_time_hasDerivAt q t x i).fst
    · exact (directRHSpaceDensity_time_hasDerivAt q t x i).snd
  have he := ((cauchyEvaluation upper r a).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => cauchyEvaluation upper r a (boundaryComponent (directRHSpaceDensity q s x i) j))
    (cauchyEvaluation upper r a (boundaryComponent (directRHMixedDensity q t x i) j)) t at he
  simpa only [cauchyEvaluation_apply,directAnalyticSpaceMatrix,directAnalyticMixedMatrix] using he

theorem directSpaceTrace_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    HasDerivAt (fun s => directSpaceTrace q s x i upper h) (directMixedTrace q t x i upper h) t := by
  have hd := directRHSpaceDensity_time_hasDerivAt q t x i
  have h0 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.fst
  have h1 := ((cauchyTraceOperator upper h).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd.snd
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHSpaceDensity q s x i).1)
    (cauchyTraceOperator upper h (directRHMixedDensity q t x i).1) t at h0
  change HasDerivAt (fun s => cauchyTraceOperator upper h (directRHSpaceDensity q s x i).2)
    (cauchyTraceOperator upper h (directRHMixedDensity q t x i).2) t at h1
  simp only [cauchyTraceOperator_apply] at h0 h1
  exact h0.prodMk h1

theorem directAnalyticSpaceSlice_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    HasDerivAt (fun s => directAnalyticSpaceSlice q s x i upper a) (directAnalyticMixedSlice q t x i upper a) t := by
  have hd := directSpaceTrace_time_hasDerivAt q t x i upper (Real.exp a)
  simpa only [directSpaceTrace_exp_eq_analyticSpaceSlice,directMixedTrace_exp_eq_analyticMixedSlice] using hd

/-- The actual reconstruction has commuting mixed derivatives. -/
theorem directAnalyticMatrix_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    deriv (fun y => deriv (fun s => directAnalyticMatrix q s y (halfPlanePoint upper r a) i j) t) x =
      deriv (fun s => deriv (fun y => directAnalyticMatrix q s y (halfPlanePoint upper r a) i j) x) t := by
  have ht : (fun y => deriv (fun s => directAnalyticMatrix q s y (halfPlanePoint upper r a) i j) t) = fun y => directAnalyticTimeMatrix q t y (halfPlanePoint upper r a) i j :=
    funext fun y => (directAnalyticMatrix_time_hasDerivAt q t y upper r a i j).deriv
  have hx : (fun s => deriv (fun y => directAnalyticMatrix q s y (halfPlanePoint upper r a) i j) x) = fun s => directAnalyticSpaceMatrix q s x (halfPlanePoint upper r a) i j :=
    funext fun s => (directAnalyticMatrix_space_hasDerivAt q s x upper r a i j).deriv
  rw [ht,hx,(directAnalyticTimeMatrix_space_hasDerivAt q t x upper r a i j).deriv,
    (directAnalyticSpaceMatrix_time_hasDerivAt q t x upper r a i j).deriv]

/-- The actual reconstruction has commuting mixed derivatives. -/
theorem directAnalyticSlice_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    deriv (fun y => deriv (fun s => directAnalyticSlice q s y i upper a) t) x =
      deriv (fun s => deriv (fun y => directAnalyticSlice q s y i upper a) x) t := by
  have ht : (fun y => deriv (fun s => directAnalyticSlice q s y i upper a) t) = fun y => directAnalyticTimeSlice q t y i upper a :=
    funext fun y => (directAnalyticSlice_time_hasDerivAt q t y i upper a).deriv
  have hx : (fun s => deriv (fun y => directAnalyticSlice q s y i upper a) x) = fun s => directAnalyticSpaceSlice q s x i upper a :=
    funext fun s => (directAnalyticSlice_space_hasDerivAt q s x i upper a).deriv
  rw [ht,hx,(directAnalyticTimeSlice_space_hasDerivAt q t x i upper a).deriv,
    (directAnalyticSpaceSlice_time_hasDerivAt q t x i upper a).deriv]

/-- The actual reconstruction has commuting mixed derivatives. -/
theorem directTrace_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    deriv (fun y => deriv (fun s => directTrace q s y i upper h) t) x =
      deriv (fun s => deriv (fun y => directTrace q s y i upper h) x) t := by
  have ht : (fun y => deriv (fun s => directTrace q s y i upper h) t) = fun y => directTimeTrace q t y i upper h :=
    funext fun y => (directTrace_time_hasDerivAt q t y i upper h).deriv
  have hx : (fun s => deriv (fun y => directTrace q s y i upper h) x) = fun s => directSpaceTrace q s x i upper h :=
    funext fun s => (directTrace_space_hasDerivAt q s x i upper h).deriv
  rw [ht,hx,(directTimeTrace_space_hasDerivAt q t x i upper h).deriv,
    (directSpaceTrace_time_hasDerivAt q t x i upper h).deriv]

/-- Both physical derivatives commute with the actual strong Plemelj boundary limit. -/
theorem directAnalyticSlice_mixed_deriv_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) :
    Tendsto (fun a => deriv (fun y => deriv (fun s => directAnalyticSlice q s y i upper a) t) x) atBot
      (𝓝 (deriv (fun y => deriv (fun s =>
        if upper then directUpperCorrection q s y i else directLowerCorrection q s y i) t) x)) := by
  have hi : (fun a => deriv (fun y => deriv (fun s => directAnalyticSlice q s y i upper a) t) x) =
      fun a => deriv (fun y => directAnalyticTimeSlice q t y i upper a) x := by
    funext a
    congr 1
    funext y
    exact (directAnalyticSlice_time_hasDerivAt q t y i upper a).deriv
  have hb : (fun y => deriv (fun s => if upper then directUpperCorrection q s y i else directLowerCorrection q s y i) t) =
      fun y => if upper then directUpperTimeCorrection q t y i else directLowerTimeCorrection q t y i := by
    cases upper
    · exact funext fun y => (directLowerCorrection_time_hasDerivAt q t y i).deriv
    · exact funext fun y => (directUpperCorrection_time_hasDerivAt q t y i).deriv
  rw [hi,hb]
  exact directAnalyticTimeSlice_space_deriv_boundary_tendsto q t x i upper

end
end RHTower.FokasLenells
