import GaloisForLFunctions.RHTower.FokasLenellsCauchyModulation
import GaloisForLFunctions.RHTower.FokasLenellsOperatorNormInverse
import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeDifferentiability

/-!
# The exact compatibility gate for Cauchy and inverse operator norms

Cauchy compression preserves every multiplier norm, so its upper block
retains the full origin obstruction. Thus compatibility is necessary and
sufficient for differentiating the Cauchy operator and its actual inverse
in operator norm. Strong differentiation remains valid on every vector.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private def upperBlock (T : Boundary →L[ℂ] Boundary) : SoninL2 →L[ℂ] SoninL2 :=
  (ContinuousLinearMap.snd ℂ SoninL2 SoninL2).comp (T.comp (ContinuousLinearMap.inl ℂ SoninL2 SoninL2))

private theorem upperBlock_norm_le (T : Boundary →L[ℂ] Boundary) : ‖upperBlock T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro u
  change ‖(T (u,0)).2‖ ≤ _
  exact (norm_snd_le (T (u,0))).trans (by simpa only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg u)] using T.le_opNorm (u,0))

private theorem upperBlock_cauchy_slope_error (q : SchwartzMap ℝ ℂ) (t s x : ℝ) :
    upperBlock (slope (fun r => directCauchyOperator q r x) t s-directCauchyTimeOperator q t x) =
      negativeCauchy.comp (slope (fun r => directMultiplier q r x true) t s-directTimeMultiplier q t x true) := by
  apply ContinuousLinearMap.ext
  intro u
  change (s-t)⁻¹ • (negativeCauchy (directMultiplier q s x true u-
      directMultiplier q s x false (directMultiplier q s x true 0))-
    negativeCauchy (directMultiplier q t x true u-directMultiplier q t x false (directMultiplier q t x true 0)))-
    negativeCauchy (directTimeMultiplier q t x true u) =
    negativeCauchy ((s-t)⁻¹ • (directMultiplier q s x true u-directMultiplier q t x true u)-directTimeMultiplier q t x true u)
  simp only [map_zero,sub_zero]
  have hs : negativeCauchy ((s-t)⁻¹ • (directMultiplier q s x true u-directMultiplier q t x true u)) =
      (s-t)⁻¹ • negativeCauchy (directMultiplier q s x true u-directMultiplier q t x true u) :=
    (negativeCauchy.restrictScalars ℝ).map_smul _ _
  rw [map_sub,hs,map_sub]

/-- The actual Cauchy operator retains the entire nonzero-moment difference-quotient obstruction. -/
theorem directCauchyOperator_time_slope_error_lower_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) :
    (1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖ ≤
      ‖slope (fun r => directCauchyOperator q r x) t s-directCauchyTimeOperator q t x‖ := by
  calc
    _ ≤ ‖slope (fun r => directMultiplier q r x true) t s-directTimeMultiplier q t x true‖ :=
      directMultiplier_upper_time_slope_error_lower_bound q t s x
    _ = ‖negativeCauchy.comp (slope (fun r => directMultiplier q r x true) t s-directTimeMultiplier q t x true)‖ :=
      (norm_negativeCauchy_comp_directTimeSlopeError q t s x true).symm
    _ = ‖upperBlock (slope (fun r => directCauchyOperator q r x) t s-directCauchyTimeOperator q t x)‖ :=
      congrArg norm (upperBlock_cauchy_slope_error q t s x).symm
    _ ≤ _ := upperBlock_norm_le _

private theorem cauchy_operator_derivative_candidate (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (V : Boundary →L[ℂ] Boundary) (hV : HasDerivAt (fun s => directCauchyOperator q s x) V t) :
    V = directCauchyTimeOperator q t x := by
  apply ContinuousLinearMap.ext
  intro u
  have hd := ((ContinuousLinearMap.apply ℂ Boundary u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hV
  exact hd.unique (directCauchyOperator_time_hasDerivAt q t x u)

private theorem cauchy_operator_derivative_requires_compatibility (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (V : Boundary →L[ℂ] Boundary) (hV : HasDerivAt (fun s => directCauchyOperator q s x) V t) :
    compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [cauchy_operator_derivative_candidate q t x V hV] at hV
  have hlim := (hV.tendsto_slope.sub_const (directCauchyTimeOperator q t x)).norm
  simp only [sub_self,norm_zero] at hlim
  have hle : (1/2 : ℝ)*‖compatibilityMoment (globalSmallScatteringPotential q)‖ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun s => directCauchyOperator_time_slope_error_lower_bound q t s x)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (compatibilityMoment (globalSmallScatteringPotential q))]

/-- The Cauchy operator alone has an operator-norm time derivative exactly at nonlinear compatibility. -/
theorem directCauchyOperator_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => directCauchyOperator q s x) (directCauchyTimeOperator q t x) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨cauchy_operator_derivative_requires_compatibility q t x _,fun hm => ((directJumpCauchy_operator_hasDerivAt_iff q t x).2 hm).2⟩

theorem directCauchyOperator_operator_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => directCauchyOperator q s x) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨fun h => cauchy_operator_derivative_requires_compatibility q t x _ h.hasDerivAt,
    fun hm => ((directCauchyOperator_operator_hasDerivAt_iff q t x).2 hm).differentiableAt⟩

/-- The full Cauchy family is C1 in operator norm if and only if the actual scaled profile is compatible. -/
theorem directCauchyOperator_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => directCauchyOperator q t x) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨fun h => (directCauchyOperator_operator_differentiableAt_iff q 0 x).1 ((h.differentiable (by simp)) 0),
    fun hm => ((directJumpCauchy_operator_contDiff_iff q x).2 hm).2⟩

/-- The actual inverse has an operator-norm derivative exactly under the same necessary and sufficient moment condition. -/
theorem directResolventInverse_operator_differentiableAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => ((directResolventUnit q s x)⁻¹).val) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directResolventInverse_operator_differentiableAt_iff_cauchy,directCauchyOperator_operator_differentiableAt_iff]

theorem directResolventInverse_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => ((directResolventUnit q s x)⁻¹).val) (directResolventTimeOperator q t x) t ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 :=
  ⟨fun h => (directResolventInverse_operator_differentiableAt_iff q t x).1 h.differentiableAt,
    fun hm => ((directJumpResolvent_operator_hasDerivAt_iff q t x).2 hm).2⟩

/-- The inverse alone is globally C1 in operator norm exactly on the full compatibility locus. -/
theorem directResolventInverse_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => ((directResolventUnit q t x)⁻¹).val) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directResolventInverse_operator_contDiff_iff_cauchy,directCauchyOperator_operator_contDiff_iff]

/-- Gaussian Cauchy families differentiate strongly on every vector but never in operator norm. -/
theorem directCauchyOperator_Gaussian_strong_not_operator_derivative (a t x : ℝ) :
    (∀ u : Boundary, HasDerivAt (fun s => directCauchyOperator (compatibilityGaussian a) s x u)
      (directCauchyTimeOperator (compatibilityGaussian a) t x u) t) ∧
    ¬ DifferentiableAt ℝ (fun s => directCauchyOperator (compatibilityGaussian a) s x) t := by
  refine ⟨fun u => directCauchyOperator_time_hasDerivAt _ t x u,?_⟩
  rw [directCauchyOperator_operator_differentiableAt_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- The same strong-versus-operator-norm separation holds for the actual Gaussian Cauchy inverse. -/
theorem directResolventInverse_Gaussian_strong_not_operator_derivative (a t x : ℝ) :
    (∀ d : Boundary, HasDerivAt (fun s => directSolution (compatibilityGaussian a) s x d)
      (directTimeSolution (compatibilityGaussian a) t x d) t) ∧
    ¬ DifferentiableAt ℝ (fun s => ((directResolventUnit (compatibilityGaussian a) s x)⁻¹).val) t := by
  refine ⟨fun d => directSolution_time_hasDerivAt _ t x d,?_⟩
  rw [directResolventInverse_operator_differentiableAt_iff]
  exact compatibilityMoment_globalSmallGaussian_ne_zero a

/-- The paper's actual full-line second inverse weight is exactly the Cauchy operator-norm differentiability condition. -/
theorem directCauchyOperator_operator_differentiableAt_iff_second_weight (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => directCauchyOperator q s x) t ↔
      MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) true) 2 volume := by
  rw [directCauchyOperator_operator_differentiableAt_iff,regularSecondInverseReflection_upper_globalSmall_memLp_iff]

/-- One extra strong L2 derivative of the upper scattering curve is exactly one operator-norm derivative of the actual inverse. -/
theorem directResolventInverse_operator_differentiableAt_iff_upper_L2_C2 (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => ((directResolventUnit q s x)⁻¹).val) t ↔
      ContDiff ℝ 2 (fun s => directSymbolL2 q s x true) := by
  rw [directResolventInverse_operator_differentiableAt_iff,directSymbolL2_upper_time_contDiff_two_iff]

end
end RHTower.FokasLenells
