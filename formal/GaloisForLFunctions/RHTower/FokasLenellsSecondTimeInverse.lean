import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeMultiplier
import GaloisForLFunctions.RHTower.FokasLenellsTimeInverse
import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelDerivative

/-!
# A second time derivative for the actual Cauchy inverse

The bounded compatible second generator passes through the already
constructed inverse. Strong product rules give R'' = R C'' R + 2 R C' R C' R
on every fixed forcing vector, with joint continuity and a closed equation.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem cauchy_time_moving_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (y : ℝ → Boundary) (y' : Boundary) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => directCauchyTimeOperator (oddInitialPart q) s x (y s))
      (directCauchyTimeOperator (oddInitialPart q) t x y'+compatibleCauchySecondTimeOperator q t x (y t)) t := by
  have hb : ∀ s, ‖(directCauchyTimeOperator (oddInitialPart q) s x).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget (oddInitialPart q) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg _)) (directCauchyTimeOperator_bound _ s x)
  have hc : ∀ d, Continuous (fun s => (directCauchyTimeOperator (oddInitialPart q) s x).restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((s,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directCauchyTimeOperator_joint (oddInitialPart q)).comp hp
    exact hh
  exact hasDerivAt_strong_apply hb hc hy (directCauchyTimeOperator_oddInitialPart_hasDerivAt q t x (y t))

private theorem inverse_moving_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (y : ℝ → Boundary) (y' : Boundary) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => directSolution q s x (y s))
      (directSolution q t x y'+directTimeSolution q t x (y t)) t := by
  have hb : ∀ s, ‖((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q s x)
  have hc : ∀ d, Continuous (fun s => ((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((s,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  exact hasDerivAt_strong_apply hb hc hy (directSolution_time_hasDerivAt q t x (y t))

/-- The second inverse derivative with both product-rule contributions retained. -/
def compatibleSecondTimeSolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) : Boundary :=
  directSolution (oddInitialPart q) t x
    (compatibleCauchySecondTimeOperator q t x (directSolution (oddInitialPart q) t x d)+
      directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d)+
      directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d))

/-- The existing first inverse derivative has this strong derivative on every forcing vector. -/
theorem directTimeSolution_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    HasDerivAt (fun s => directTimeSolution (oddInitialPart q) s x d)
      (compatibleSecondTimeSolution q t x d) t := by
  have h1 := cauchy_time_moving_hasDerivAt q t x (fun s => directSolution (oddInitialPart q) s x d)
    _ (directSolution_time_hasDerivAt _ t x d)
  have h2 := inverse_moving_hasDerivAt (oddInitialPart q) t x
    (fun s => directCauchyTimeOperator (oddInitialPart q) s x (directSolution (oddInitialPart q) s x d)) _ h1
  have he : directSolution (oddInitialPart q) t x
      (directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d)+
        compatibleCauchySecondTimeOperator q t x (directSolution (oddInitialPart q) t x d))+
      directTimeSolution (oddInitialPart q) t x
        (directCauchyTimeOperator (oddInitialPart q) t x (directSolution (oddInitialPart q) t x d)) =
      compatibleSecondTimeSolution q t x d := by
    change ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _+
      ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _ =
      ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _
    rw [← map_add]
    congr 1
    change _ + directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d) = _
    abel
  rw [he] at h2
  exact h2

theorem continuous_compatibleSecondTimeSolution_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => compatibleSecondTimeSolution q p.1.1 p.1.2 p.2) := by
  have h1 := (continuous_compatibleCauchySecondTimeOperator_joint q).comp
    (continuous_fst.prodMk (continuous_directSolution_joint (oddInitialPart q)))
  have h2 := (continuous_directCauchyTimeOperator_joint (oddInitialPart q)).comp
    (continuous_fst.prodMk (continuous_directTimeSolution_joint (oddInitialPart q)))
  have hh := (continuous_directSolution_joint (oddInitialPart q)).comp
    (continuous_fst.prodMk ((h1.add h2).add h2))
  exact hh

/-- Every fixed-forcing orbit of the constructed compatible Cauchy inverse is globally C2 in time. -/
theorem directSolution_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (d : Boundary) :
    ContDiff ℝ 2 (fun t => directSolution (oddInitialPart q) t x d) := by
  have he : deriv (fun t => directSolution (oddInitialPart q) t x d) =
      fun t => directTimeSolution (oddInitialPart q) t x d :=
    funext fun t => (directSolution_time_hasDerivAt _ t x d).deriv
  change ContDiff ℝ (1+1) (fun t => directSolution (oddInitialPart q) t x d)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (directSolution_time_hasDerivAt _ t x d).differentiableAt,by simp,?_⟩
  rw [he]
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directTimeSolution_oddInitialPart_hasDerivAt q t x d).differentiableAt,?_⟩
  have he2 : deriv (fun t => directTimeSolution (oddInitialPart q) t x d) =
      fun t => compatibleSecondTimeSolution q t x d :=
    funext fun t => (directTimeSolution_oddInitialPart_hasDerivAt q t x d).deriv
  rw [he2]
  have hc : Continuous (fun t : ℝ => ((t,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hh := (continuous_compatibleSecondTimeSolution_joint q).comp hc
  exact hh

/-- Differentiating twice gives a closed, uniquely invertible Cauchy equation with its actual source. -/
theorem compatibleSecondTimeSolution_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    compatibleSecondTimeSolution q t x d-
      directCauchyOperator (oddInitialPart q) t x (compatibleSecondTimeSolution q t x d) =
      compatibleCauchySecondTimeOperator q t x (directSolution (oddInitialPart q) t x d)+
        directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d)+
        directCauchyTimeOperator (oddInitialPart q) t x (directTimeSolution (oddInitialPart q) t x d) :=
  directSolution_equation _ t x _

end
end RHTower.FokasLenells
