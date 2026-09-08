import GaloisForLFunctions.RHTower.FokasLenellsTimeMultiplier

/-!
# Strong time differentiation of the actual Cauchy inverse

The resolvent difference identity and joint strong continuity yield the
inverse derivative R C′ R on every forcing vector. This proves C¹ time
regularity and a uniform operator-norm Lipschitz estimate without assuming
operator-norm differentiability of the multiplier family.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual inverse satisfies the resolvent difference identity without a smallness premise. -/
theorem directSolution_resolvent_difference (q : SchwartzMap ℝ ℂ) (s y t x : ℝ) (d : Boundary) :
    directSolution q s y d-directSolution q t x d = directSolution q s y
      (directCauchyOperator q s y (directSolution q t x d)-directCauchyOperator q t x (directSolution q t x d)) := by
  apply (directSolution_existsUnique q s y _).unique ?_ (directSolution_equation q s y _)
  calc
    _ = (directSolution q s y d-directCauchyOperator q s y (directSolution q s y d))-
        (directSolution q t x d-directCauchyOperator q t x (directSolution q t x d))+
        (directCauchyOperator q s y (directSolution q t x d)-directCauchyOperator q t x (directSolution q t x d)) := by
      rw [map_sub]
      abel
    _ = _ := by rw [directSolution_equation,directSolution_equation]; abel

/-- Resolvent differentiation reduces exactly to a fixed-vector Cauchy-operator slope. -/
theorem directSolution_time_slope (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (d : Boundary) :
    slope (fun r => directSolution q r x d) t s =
      directSolution q s x (slope (fun r => directCauchyOperator q r x (directSolution q t x d)) t s) := by
  simp only [slope_def_module]
  rw [directSolution_resolvent_difference q s x t x d]
  exact (map_smul (((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ) _ _).symm

/-- The actual strong derivative of the inverse applied to arbitrary fixed forcing. -/
def directTimeSolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) : Boundary :=
  directSolution q t x (directCauchyTimeOperator q t x (directSolution q t x d))

/-- The familiar inverse derivative formula holds strongly, with every inverse constructed internally. -/
theorem directSolution_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    HasDerivAt (fun s => directSolution q s x d) (directTimeSolution q t x d) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hd := (directCauchyOperator_time_hasDerivAt q t x (directSolution q t x d)).tendsto_slope
  have hs : Tendsto (fun s : ℝ => s) (𝓝[≠] t) (𝓝 t) := nhdsWithin_le_nhds
  have hp := (hs.prodMk_nhds (tendsto_const_nhds (x := x))).prodMk_nhds hd
  have hh := ((continuous_directSolution_joint q).tendsto
    ((t,x),directCauchyTimeOperator q t x (directSolution q t x d))).comp hp
  exact hh.congr' (Eventually.of_forall fun s => (directSolution_time_slope q t s x d).symm)

/-- The inverse derivative varies jointly with time, position, and forcing. -/
theorem continuous_directTimeSolution_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directTimeSolution q p.1.1 p.1.2 p.2) := by
  have h1 := continuous_fst.prodMk (continuous_directSolution_joint q)
  have h2 := (continuous_directCauchyTimeOperator_joint q).comp h1
  have h3 := continuous_fst.prodMk h2
  have h4 := (continuous_directSolution_joint q).comp h3
  exact h4

/-- Every fixed-forcing inverse orbit is C¹ in time. -/
theorem directSolution_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (d : Boundary) :
    ContDiff ℝ 1 (fun t => directSolution q t x d) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directSolution_time_hasDerivAt q t x d).differentiableAt,?_⟩
  have he : deriv (fun t => directSolution q t x d) = fun t => directTimeSolution q t x d :=
    funext fun t => (directSolution_time_hasDerivAt q t x d).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => ((t,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hh := (continuous_directTimeSolution_joint q).comp hc
  exact hh

/-- The derivative itself solves a closed Cauchy equation. -/
theorem directTimeSolution_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    directTimeSolution q t x d-directCauchyOperator q t x (directTimeSolution q t x d) =
      directCauchyTimeOperator q t x (directSolution q t x d) :=
  directSolution_equation q t x _

/-- Two uniformly bounded inverses surround the bounded differentiated jump. -/
theorem directTimeSolution_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ‖directTimeSolution q t x d‖ ≤ ((81/50 : ℝ)*regularReflectionFrequencyBudget q)*‖d‖ := by
  have h0 : 0 ≤ (1/2 : ℝ)*regularReflectionFrequencyBudget q :=
    mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)
  calc
    _ ≤ (9/5 : ℝ)*‖directCauchyTimeOperator q t x (directSolution q t x d)‖ := directSolution_bound q t x _
    _ ≤ (9/5 : ℝ)*(((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖directSolution q t x d‖) :=
      mul_le_mul_of_nonneg_left (directCauchyTimeOperator_bound q t x _) (by positivity)
    _ ≤ (9/5 : ℝ)*(((1/2 : ℝ)*regularReflectionFrequencyBudget q)*((9/5 : ℝ)*‖d‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (directSolution_bound q t x d) h0) (by positivity)
    _ = _ := by ring

/-- The actual inverse is uniformly Lipschitz in time on every forcing vector. -/
theorem directSolution_time_bound (q : SchwartzMap ℝ ℂ) (t s x : ℝ) (d : Boundary) :
    ‖directSolution q t x d-directSolution q s x d‖ ≤
      (((81/50 : ℝ)*regularReflectionFrequencyBudget q)*‖d‖)*|t-s| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directSolution_time_hasDerivAt q r x d).hasDerivWithinAt)
    (fun r _ => directTimeSolution_bound q r x d) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using hh

/-- The constructed resolvent inverse is Lipschitz in operator norm. -/
theorem norm_directResolventInverse_time_sub_le (q : SchwartzMap ℝ ℂ) (t s x : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val-((directResolventUnit q s x)⁻¹).val‖ ≤
      ((81/50 : ℝ)*regularReflectionFrequencyBudget q)*|t-s| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (abs_nonneg _)
  · intro d
    change ‖directSolution q t x d-directSolution q s x d‖ ≤ _
    have hh := directSolution_time_bound q t s x d
    simpa only [mul_right_comm] using hh

end
end RHTower.FokasLenells
