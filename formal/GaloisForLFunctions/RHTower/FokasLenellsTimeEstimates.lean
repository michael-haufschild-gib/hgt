import GaloisForLFunctions.RHTower.FokasLenellsTimeAnalytic

/-!
# Uniform time stability of the actual RH reconstruction

A common differentiated jump envelope and the proved inverse bound control
both Hardy boundary derivatives, the reconstruction density derivative,
and all horizontal holomorphic derivative slices. This yields global time
Lipschitz estimates uniform in height and position, differentiated
normalization under arbitrary parameter drift, and joint Plemelj limits.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- A finite L² size for both differentiated scattering channels. -/
def directJumpTimeSize (q : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(directJumpTimeEnvelope_memLp q).toLp (directJumpTimeEnvelope q)‖

/-- The actual jump derivative has one L² bound for every time and position. -/
theorem directJumpTimeEntry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    ‖directJumpTimeEntry q t x i j‖ ≤ directJumpTimeSize q := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(directJumpTimeMatrix_entry_memLp q t x i j).coeFn_toLp,
    (directJumpTimeEnvelope_memLp q).coeFn_toLp] with z hj he
  change (directJumpTimeEntry q t x i j : ℝ → ℂ) z = directJumpTimeMatrix q t x z i j at hj
  rw [hj,he,Real.norm_eq_abs,abs_of_nonneg]
  · exact directJumpTimeMatrix_entry_bound q t x z i j
  · exact mul_nonneg (by positivity) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem directJumpTimeRow_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directJumpTimeRow q t x i‖ ≤ directJumpTimeSize q :=
  max_le (directJumpTimeEntry_uniform_bound q t x i 0) (directJumpTimeEntry_uniform_bound q t x i 1)

/-- One explicit potential-dependent size controls the complete differentiated RH problem. -/
def directRHTimeSize (q : SchwartzMap ℝ ℂ) : ℝ :=
  (9/5 : ℝ)*(directJumpTimeSize q+(9/10 : ℝ)*regularReflectionFrequencyBudget q*directJumpSize q)

theorem directRHTimeSize_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ directRHTimeSize q := by
  unfold directRHTimeSize directJumpTimeSize directJumpSize
  have := regularReflectionFrequencyBudget_nonneg q
  positivity

/-- The actual lower derivative has a uniform bound independent of time and position. -/
theorem directLowerTimeCorrection_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directLowerTimeCorrection q t x i‖ ≤ directRHTimeSize q := by
  have hf : ‖directRHTimeForcing q t x i‖ ≤ directJumpTimeSize q :=
    (boundaryCauchy_bound _).trans (directJumpTimeRow_uniform_bound q t x i)
  have hl := (directRH_uniform_L2_bounds q t x i).2.1
  have h0 : 0 ≤ (1/2 : ℝ)*regularReflectionFrequencyBudget q :=
    mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)
  have hc := (directCauchyTimeOperator_bound q t x (directLowerCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hl h0)
  calc
    _ ≤ (9/5 : ℝ)*‖directRHTimeForcing q t x i+directCauchyTimeOperator q t x (directLowerCorrection q t x i)‖ :=
      directSolution_bound q t x _
    _ ≤ (9/5 : ℝ)*(‖directRHTimeForcing q t x i‖+‖directCauchyTimeOperator q t x (directLowerCorrection q t x i)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (9/5 : ℝ)*(directJumpTimeSize q+((1/2 : ℝ)*regularReflectionFrequencyBudget q)*((9/5 : ℝ)*directJumpSize q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hf hc) (by positivity)
    _ = _ := by unfold directRHTimeSize; ring

/-- The differentiated density obeys the same uniform constant as the lower derivative. -/
theorem directRHTimeDensity_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directRHTimeDensity q t x i‖ ≤ directRHTimeSize q := by
  have hl := directLowerTimeCorrection_uniform_bound q t x i
  have hbase := (directRH_uniform_L2_bounds q t x i).2.1
  have h0 : 0 ≤ (1/2 : ℝ)*regularReflectionFrequencyBudget q :=
    mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)
  have h1 := (directJumpPerturbation_bound q t x (directLowerTimeCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hl (by positivity))
  have h2 := (directJumpTimeOperator_bound q t x (directLowerCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hbase h0)
  calc
    _ ≤ ‖directJumpTimeRow q t x i‖+
        (‖directJumpPerturbation q t x (directLowerTimeCorrection q t x i)‖+
          ‖directJumpTimeOperator q t x (directLowerCorrection q t x i)‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ directJumpTimeSize q+((4/9 : ℝ)*directRHTimeSize q+
        ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*((9/5 : ℝ)*directJumpSize q)) :=
      add_le_add (directJumpTimeRow_uniform_bound q t x i) (add_le_add h1 h2)
    _ = _ := by unfold directRHTimeSize; ring

/-- Cauchy contraction controls the differentiated trace at every height. -/
theorem directTimeTrace_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    ‖directTimeTrace q t x i upper h‖ ≤ directRHTimeSize q :=
  (max_le_max (cauchyTrace_bound _ upper h) (cauchyTrace_bound _ upper h)).trans
    (directRHTimeDensity_uniform_bound q t x i)

/-- The upper derivative has the same bound, using its Hardy projection rather than a triangle loss. -/
theorem directUpperTimeCorrection_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directUpperTimeCorrection q t x i‖ ≤ directRHTimeSize q := by
  have hh := directTimeTrace_uniform_bound q t x i true 0
  simpa only [directTimeTrace_zero,↓reduceIte] using hh

/-- All actual holomorphic time-derivative slices have one height-independent bound. -/
theorem directAnalyticTimeSlice_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticTimeSlice q t x i upper a‖ ≤ directRHTimeSize q := by
  rw [← directTimeTrace_exp_eq_analyticTimeSlice]
  exact directTimeTrace_uniform_bound q t x i upper (Real.exp a)

/-- Uniform control of every off-contour time derivative entry. -/
theorem directAnalyticTimeMatrix_entry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticTimeMatrix q t x (halfPlanePoint upper r a) i j‖ ≤
      (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHTimeSize q :=
  (cauchyExtension_bound _ upper r a).trans (mul_le_mul_of_nonneg_left
    ((boundaryComponent_bound _ j).trans (directRHTimeDensity_uniform_bound q t x i)) (by positivity))

/-- Time variation of the lower boundary is globally Lipschitz with one uniform constant. -/
theorem directLowerCorrection_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (i : Fin 2) :
    ‖directLowerCorrection q t x i-directLowerCorrection q s x i‖ ≤ directRHTimeSize q*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directLowerCorrection_time_hasDerivAt q r x i).hasDerivWithinAt)
    (fun r _ => directLowerTimeCorrection_uniform_bound q r x i) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- The same global time-Lipschitz estimate holds for the upper boundary. -/
theorem directUpperCorrection_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (i : Fin 2) :
    ‖directUpperCorrection q t x i-directUpperCorrection q s x i‖ ≤ directRHTimeSize q*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directUpperCorrection_time_hasDerivAt q r x i).hasDerivWithinAt)
    (fun r _ => directUpperTimeCorrection_uniform_bound q r x i) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- The actual reconstruction density is globally Lipschitz in time. -/
theorem directRHDensity_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (i : Fin 2) :
    ‖directRHDensity q t x i-directRHDensity q s x i‖ ≤ directRHTimeSize q*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directRHDensity_time_hasDerivAt q r x i).hasDerivWithinAt)
    (fun r _ => directRHTimeDensity_uniform_bound q r x i) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- Actual holomorphic slices have a time-Lipschitz estimate uniform over every height. -/
theorem directAnalyticSlice_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a-directAnalyticSlice q s x i upper a‖ ≤ directRHTimeSize q*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directAnalyticSlice_time_hasDerivAt q r x i upper a).hasDerivWithinAt)
    (fun r _ => directAnalyticTimeSlice_uniform_bound q r x i upper a) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- The same time-Lipschitz bound covers traces at every height, including the boundary itself. -/
theorem directTrace_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    ‖directTrace q t x i upper h-directTrace q s x i upper h‖ ≤ directRHTimeSize q*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directTrace_time_hasDerivAt q r x i upper h).hasDerivWithinAt)
    (fun r _ => directTimeTrace_uniform_bound q r x i upper h) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- Pointwise time stability of the actual analytic matrix, uniform along each horizontal line. -/
theorem directAnalyticMatrix_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticMatrix q t x (halfPlanePoint upper r a) i j-
      directAnalyticMatrix q s x (halfPlanePoint upper r a) i j‖ ≤
      ((2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHTimeSize q)*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_ : v ∈ (Set.univ : Set ℝ)) => (directAnalyticMatrix_time_hasDerivAt q v x upper r a i j).hasDerivWithinAt)
    (fun v _ => directAnalyticTimeMatrix_entry_uniform_bound q v x i j upper r a) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- Differentiated normalization survives arbitrary simultaneous drift in time, space, and horizontal coordinate. -/
theorem directAnalyticTimeMatrix_tendsto_vertical_infinity_arbitrary_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (t x r : ℝ → ℝ) (i j : Fin 2) :
    Tendsto (fun a => directAnalyticTimeMatrix q (t a) (x a) (halfPlanePoint upper (r a) a) i j) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => Real.pi/Real.exp a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,← Real.exp_neg,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul Real.pi
  have hs : Tendsto (fun a : ℝ => (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHTimeSize q) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
      (((Real.continuous_sqrt.tendsto 0).comp ht).const_mul ((2*Real.pi)⁻¹)).mul_const (directRHTimeSize q)
  exact squeeze_zero_norm (fun a => directAnalyticTimeMatrix_entry_uniform_bound q (t a) (x a) i j upper (r a) a) hs

/-- Differentiated Plemelj convergence remains valid when both physical parameters vary simultaneously. -/
theorem directAnalyticTimeSlice_joint_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => directAnalyticTimeSlice q p.1.1 p.1.2 i upper p.2)
      ((𝓝 (t,x)) ×ˢ atBot)
      (𝓝 (if upper then directUpperTimeCorrection q t x i else directLowerTimeCorrection q t x i)) := by
  have hf : Tendsto (fun p : (ℝ × ℝ) × ℝ => (p.1,Real.exp p.2))
      ((𝓝 (t,x)) ×ˢ atBot) (𝓝 ((t,x),0)) :=
    tendsto_fst.prodMk_nhds (Real.tendsto_exp_atBot.comp tendsto_snd)
  have hh := ((continuous_directTimeTrace_parameters q i upper).tendsto ((t,x),0)).comp hf
  change Tendsto (fun p : (ℝ × ℝ) × ℝ => directTimeTrace q p.1.1 p.1.2 i upper (Real.exp p.2))
    ((𝓝 (t,x)) ×ˢ atBot) (𝓝 (directTimeTrace q t x i upper 0)) at hh
  simpa only [directTimeTrace_exp_eq_analyticTimeSlice,directTimeTrace_zero] using hh

end
end RHTower.FokasLenells
