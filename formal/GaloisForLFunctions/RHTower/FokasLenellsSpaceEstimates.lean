import GaloisForLFunctions.RHTower.FokasLenellsSpaceAnalytic

/-!
# Uniform spatial stability of the actual RH reconstruction

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
def directJumpSpaceSize (q : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(directJumpSpaceEnvelope_memLp q).toLp (directJumpSpaceEnvelope q)‖

/-- The actual jump derivative has one L² bound for every time and position. -/
theorem directJumpSpaceEntry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    ‖directJumpSpaceEntry q t x i j‖ ≤ directJumpSpaceSize q := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(directJumpSpaceMatrix_entry_memLp q t x i j).coeFn_toLp,
    (directJumpSpaceEnvelope_memLp q).coeFn_toLp] with z hj he
  change (directJumpSpaceEntry q t x i j : ℝ → ℂ) z = directJumpSpaceMatrix q t x z i j at hj
  rw [hj,he,Real.norm_eq_abs,abs_of_nonneg]
  · exact directJumpSpaceMatrix_entry_bound q t x z i j
  · exact mul_nonneg (by positivity) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem directJumpSpaceRow_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directJumpSpaceRow q t x i‖ ≤ directJumpSpaceSize q :=
  max_le (directJumpSpaceEntry_uniform_bound q t x i 0) (directJumpSpaceEntry_uniform_bound q t x i 1)

/-- One explicit potential-dependent size controls the complete differentiated RH problem. -/
def directRHSpaceSize (q : SchwartzMap ℝ ℂ) : ℝ :=
  (9/5 : ℝ)*(directJumpSpaceSize q+(9/5 : ℝ)*directSpaceOperatorBudget q*directJumpSize q)

theorem directRHSpaceSize_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ directRHSpaceSize q := by
  unfold directRHSpaceSize directJumpSpaceSize directJumpSize
  have := directSpaceOperatorBudget_nonneg q
  positivity

/-- The actual lower derivative has a uniform bound independent of time and position. -/
theorem directLowerSpaceCorrection_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directLowerSpaceCorrection q t x i‖ ≤ directRHSpaceSize q := by
  have hf : ‖directRHSpaceForcing q t x i‖ ≤ directJumpSpaceSize q :=
    (boundaryCauchy_bound _).trans (directJumpSpaceRow_uniform_bound q t x i)
  have hl := (directRH_uniform_L2_bounds q t x i).2.1
  have h0 : 0 ≤ directSpaceOperatorBudget q :=
    directSpaceOperatorBudget_nonneg q
  have hc := (directCauchySpaceOperator_bound q t x (directLowerCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hl h0)
  calc
    _ ≤ (9/5 : ℝ)*‖directRHSpaceForcing q t x i+directCauchySpaceOperator q t x (directLowerCorrection q t x i)‖ :=
      directSolution_bound q t x _
    _ ≤ (9/5 : ℝ)*(‖directRHSpaceForcing q t x i‖+‖directCauchySpaceOperator q t x (directLowerCorrection q t x i)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (9/5 : ℝ)*(directJumpSpaceSize q+(directSpaceOperatorBudget q)*((9/5 : ℝ)*directJumpSize q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hf hc) (by positivity)
    _ = _ := by unfold directRHSpaceSize; ring

/-- The differentiated density obeys the same uniform constant as the lower derivative. -/
theorem directRHSpaceDensity_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directRHSpaceDensity q t x i‖ ≤ directRHSpaceSize q := by
  have hl := directLowerSpaceCorrection_uniform_bound q t x i
  have hbase := (directRH_uniform_L2_bounds q t x i).2.1
  have h0 : 0 ≤ directSpaceOperatorBudget q :=
    directSpaceOperatorBudget_nonneg q
  have h1 := (directJumpPerturbation_bound q t x (directLowerSpaceCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hl (by positivity))
  have h2 := (directJumpSpaceOperator_bound q t x (directLowerCorrection q t x i)).trans
    (mul_le_mul_of_nonneg_left hbase h0)
  calc
    _ ≤ ‖directJumpSpaceRow q t x i‖+
        (‖directJumpPerturbation q t x (directLowerSpaceCorrection q t x i)‖+
          ‖directJumpSpaceOperator q t x (directLowerCorrection q t x i)‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ directJumpSpaceSize q+((4/9 : ℝ)*directRHSpaceSize q+
        (directSpaceOperatorBudget q)*((9/5 : ℝ)*directJumpSize q)) :=
      add_le_add (directJumpSpaceRow_uniform_bound q t x i) (add_le_add h1 h2)
    _ = _ := by unfold directRHSpaceSize; ring

/-- Cauchy contraction controls the differentiated trace at every height. -/
theorem directSpaceTrace_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    ‖directSpaceTrace q t x i upper h‖ ≤ directRHSpaceSize q :=
  (max_le_max (cauchyTrace_bound _ upper h) (cauchyTrace_bound _ upper h)).trans
    (directRHSpaceDensity_uniform_bound q t x i)

/-- The upper derivative has the same bound, using its Hardy projection rather than a triangle loss. -/
theorem directUpperSpaceCorrection_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directUpperSpaceCorrection q t x i‖ ≤ directRHSpaceSize q := by
  have hh := directSpaceTrace_uniform_bound q t x i true 0
  simpa only [directSpaceTrace_zero,↓reduceIte] using hh

/-- All actual holomorphic time-derivative slices have one height-independent bound. -/
theorem directAnalyticSpaceSlice_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSpaceSlice q t x i upper a‖ ≤ directRHSpaceSize q := by
  rw [← directSpaceTrace_exp_eq_analyticSpaceSlice]
  exact directSpaceTrace_uniform_bound q t x i upper (Real.exp a)

/-- Uniform control of every off-contour spatial derivative entry. -/
theorem directAnalyticSpaceMatrix_entry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticSpaceMatrix q t x (halfPlanePoint upper r a) i j‖ ≤
      (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHSpaceSize q :=
  (cauchyExtension_bound _ upper r a).trans (mul_le_mul_of_nonneg_left
    ((boundaryComponent_bound _ j).trans (directRHSpaceDensity_uniform_bound q t x i)) (by positivity))

/-- Space variation of the lower boundary is globally Lipschitz with one uniform constant. -/
theorem directLowerCorrection_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (i : Fin 2) :
    ‖directLowerCorrection q t x i-directLowerCorrection q t y i‖ ≤ directRHSpaceSize q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directLowerCorrection_space_hasDerivAt q t r i).hasDerivWithinAt)
    (fun r _ => directLowerSpaceCorrection_uniform_bound q t r i) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- The same global spatial Lipschitz estimate holds for the upper boundary. -/
theorem directUpperCorrection_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (i : Fin 2) :
    ‖directUpperCorrection q t x i-directUpperCorrection q t y i‖ ≤ directRHSpaceSize q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directUpperCorrection_space_hasDerivAt q t r i).hasDerivWithinAt)
    (fun r _ => directUpperSpaceCorrection_uniform_bound q t r i) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- The actual reconstruction density is globally Lipschitz in position. -/
theorem directRHDensity_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (i : Fin 2) :
    ‖directRHDensity q t x i-directRHDensity q t y i‖ ≤ directRHSpaceSize q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directRHDensity_space_hasDerivAt q t r i).hasDerivWithinAt)
    (fun r _ => directRHSpaceDensity_uniform_bound q t r i) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- Actual holomorphic slices have a spatial Lipschitz estimate uniform over every height. -/
theorem directAnalyticSlice_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a-directAnalyticSlice q t y i upper a‖ ≤ directRHSpaceSize q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directAnalyticSlice_space_hasDerivAt q t r i upper a).hasDerivWithinAt)
    (fun r _ => directAnalyticSpaceSlice_uniform_bound q t r i upper a) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- The same spatial Lipschitz bound covers traces at every height, including the boundary itself. -/
theorem directTrace_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) :
    ‖directTrace q t x i upper h-directTrace q t y i upper h‖ ≤ directRHSpaceSize q*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directTrace_space_hasDerivAt q t r i upper h).hasDerivWithinAt)
    (fun r _ => directSpaceTrace_uniform_bound q t r i upper h) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- Pointwise spatial stability of the actual analytic matrix, uniform along each horizontal line. -/
theorem directAnalyticMatrix_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticMatrix q t x (halfPlanePoint upper r a) i j-
      directAnalyticMatrix q t y (halfPlanePoint upper r a) i j‖ ≤
      ((2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHSpaceSize q)*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_ : v ∈ (Set.univ : Set ℝ)) => (directAnalyticMatrix_space_hasDerivAt q t v upper r a i j).hasDerivWithinAt)
    (fun v _ => directAnalyticSpaceMatrix_entry_uniform_bound q t v i j upper r a) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- Differentiated normalization survives arbitrary simultaneous drift in time, space, and horizontal coordinate. -/
theorem directAnalyticSpaceMatrix_tendsto_vertical_infinity_arbitrary_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (t x r : ℝ → ℝ) (i j : Fin 2) :
    Tendsto (fun a => directAnalyticSpaceMatrix q (t a) (x a) (halfPlanePoint upper (r a) a) i j) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => Real.pi/Real.exp a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,← Real.exp_neg,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul Real.pi
  have hs : Tendsto (fun a : ℝ => (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*directRHSpaceSize q) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
      (((Real.continuous_sqrt.tendsto 0).comp ht).const_mul ((2*Real.pi)⁻¹)).mul_const (directRHSpaceSize q)
  exact squeeze_zero_norm (fun a => directAnalyticSpaceMatrix_entry_uniform_bound q (t a) (x a) i j upper (r a) a) hs

/-- Differentiated Plemelj convergence remains valid when both physical parameters vary simultaneously. -/
theorem directAnalyticSpaceSlice_joint_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => directAnalyticSpaceSlice q p.1.1 p.1.2 i upper p.2)
      ((𝓝 (t,x)) ×ˢ atBot)
      (𝓝 (if upper then directUpperSpaceCorrection q t x i else directLowerSpaceCorrection q t x i)) := by
  have hf : Tendsto (fun p : (ℝ × ℝ) × ℝ => (p.1,Real.exp p.2))
      ((𝓝 (t,x)) ×ˢ atBot) (𝓝 ((t,x),0)) :=
    tendsto_fst.prodMk_nhds (Real.tendsto_exp_atBot.comp tendsto_snd)
  have hh := ((continuous_directSpaceTrace_parameters q i upper).tendsto ((t,x),0)).comp hf
  change Tendsto (fun p : (ℝ × ℝ) × ℝ => directSpaceTrace q p.1.1 p.1.2 i upper (Real.exp p.2))
    ((𝓝 (t,x)) ×ˢ atBot) (𝓝 (directSpaceTrace q t x i upper 0)) at hh
  simpa only [directSpaceTrace_exp_eq_analyticSpaceSlice,directSpaceTrace_zero] using hh

end
end RHTower.FokasLenells
