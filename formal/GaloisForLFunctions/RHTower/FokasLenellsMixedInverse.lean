import GaloisForLFunctions.RHTower.FokasLenellsMixedOperator
import GaloisForLFunctions.RHTower.FokasLenellsSpaceInverse
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonDuhamelDerivative

/-!
# Commuting mixed derivatives of the actual Cauchy inverse

The paper's inverse mechanism and the corpus's strong operator product rule
give a second derivative without differentiability in operator norm. The
explicit three-term resolvent formula contains both orders of the first
generators and the off-diagonal mixed generator.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def directMixedSolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) : Boundary :=
  directSolution q t x (directCauchyMixedOperator q t x (directSolution q t x d)+
    directCauchyTimeOperator q t x (directSpaceSolution q t x d)+
    directCauchySpaceOperator q t x (directTimeSolution q t x d))

/-- Differentiation of R Cₜ R in space gives all three mixed inverse contributions. -/
theorem directTimeSolution_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    HasDerivAt (fun y => directTimeSolution q t y d) (directMixedSolution q t x d) x := by
  have hb : ∀ y, ‖(directCauchyTimeOperator q t y).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget q := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
      (directCauchyTimeOperator_bound q t y)
  have hc : ∀ u, Continuous (fun y => (directCauchyTimeOperator q t y).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directCauchyTimeOperator_joint q).comp hp
    exact hh
  have hi := hasDerivAt_strong_apply hb hc (directSolution_space_hasDerivAt q t x d)
    (directCauchyTimeOperator_space_hasDerivAt q t x (directSolution q t x d))
  have hrb : ∀ y, ‖((directResolventUnit q t y)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q t y)
  have hrc : ∀ u, Continuous (fun y => ((directResolventUnit q t y)⁻¹).val.restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hrb hrc hi
    (directSolution_space_hasDerivAt q t x (directCauchyTimeOperator q t x (directSolution q t x d)))
  convert! hd using 1
  simp only [directMixedSolution,directTimeSolution,directSpaceSolution,directSolution,ContinuousLinearMap.coe_restrictScalars',map_add]
  abel

/-- Differentiating in the reverse order gives the same explicit mixed inverse. -/
theorem directSpaceSolution_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    HasDerivAt (fun s => directSpaceSolution q s x d) (directMixedSolution q t x d) t := by
  have hb : ∀ s, ‖(directCauchySpaceOperator q s x).restrictScalars ℝ‖ ≤ directSpaceOperatorBudget q := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (directSpaceOperatorBudget_nonneg q)
      (directCauchySpaceOperator_bound q s x)
  have hc : ∀ u, Continuous (fun s => (directCauchySpaceOperator q s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) :=
      (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directCauchySpaceOperator_joint q).comp hp
    exact hh
  have hi := hasDerivAt_strong_apply hb hc (directSolution_time_hasDerivAt q t x d)
    (directCauchySpaceOperator_time_hasDerivAt q t x (directSolution q t x d))
  have hrb : ∀ s, ‖((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q s x)
  have hrc : ∀ u, Continuous (fun s => ((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) :=
      (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hrb hrc hi
    (directSolution_time_hasDerivAt q t x (directCauchySpaceOperator q t x (directSolution q t x d)))
  convert! hd using 1
  simp only [directMixedSolution,directTimeSolution,directSpaceSolution,directSolution,ContinuousLinearMap.coe_restrictScalars',map_add]
  abel

theorem continuous_directMixedSolution_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directMixedSolution q p.1.1 p.1.2 p.2) := by
  have h0 := (continuous_directCauchyMixedOperator_joint q).comp
    (continuous_fst.prodMk (continuous_directSolution_joint q))
  have h1 := (continuous_directCauchyTimeOperator_joint q).comp
    (continuous_fst.prodMk (continuous_directSpaceSolution_joint q))
  have h2 := (continuous_directCauchySpaceOperator_joint q).comp
    (continuous_fst.prodMk (continuous_directTimeSolution_joint q))
  exact (continuous_directSolution_joint q).comp (continuous_fst.prodMk ((h0.add h1).add h2))

/-- The mixed derivative solves a dependency-closed differentiated Cauchy equation. -/
theorem directMixedSolution_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    directMixedSolution q t x d-directCauchyOperator q t x (directMixedSolution q t x d) =
      directCauchyMixedOperator q t x (directSolution q t x d)+
        directCauchyTimeOperator q t x (directSpaceSolution q t x d)+
        directCauchySpaceOperator q t x (directTimeSolution q t x d) :=
  directSolution_equation q t x _

theorem directSolution_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    deriv (fun y => deriv (fun s => directSolution q s y d) t) x =
      deriv (fun s => deriv (fun y => directSolution q s y d) x) t := by
  have ht : (fun y => deriv (fun s => directSolution q s y d) t) = fun y => directTimeSolution q t y d :=
    funext fun y => (directSolution_time_hasDerivAt q t y d).deriv
  have hx : (fun s => deriv (fun y => directSolution q s y d) x) = fun s => directSpaceSolution q s x d :=
    funext fun s => (directSolution_space_hasDerivAt q s x d).deriv
  rw [ht,hx,(directTimeSolution_space_hasDerivAt q t x d).deriv,
    (directSpaceSolution_time_hasDerivAt q t x d).deriv]

/-- A uniform mixed inverse bound with explicit constants and no spectral cutoff. -/
theorem directMixedSolution_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ‖directMixedSolution q t x d‖ ≤
      ((27/25 : ℝ)+(729/125 : ℝ)*directSpaceOperatorBudget q*regularReflectionFrequencyBudget q)*‖d‖ := by
  have hs := directSpaceOperatorBudget_nonneg q
  have hf := regularReflectionFrequencyBudget_nonneg q
  have h0 := directCauchyMixedOperator_bound q t x (directSolution q t x d)
  have h1 := directCauchyTimeOperator_bound q t x (directSpaceSolution q t x d)
  have h2 := directCauchySpaceOperator_bound q t x (directTimeSolution q t x d)
  have hr := directSolution_bound q t x d
  have hx := directSpaceSolution_bound q t x d
  have ht := directTimeSolution_bound q t x d
  have hn := norm_add_le (directCauchyMixedOperator q t x (directSolution q t x d))
    (directCauchyTimeOperator q t x (directSpaceSolution q t x d))
  have hm := norm_add_le
    (directCauchyMixedOperator q t x (directSolution q t x d)+directCauchyTimeOperator q t x (directSpaceSolution q t x d))
    (directCauchySpaceOperator q t x (directTimeSolution q t x d))
  have hh := directSolution_bound q t x
    (directCauchyMixedOperator q t x (directSolution q t x d)+directCauchyTimeOperator q t x (directSpaceSolution q t x d)+
      directCauchySpaceOperator q t x (directTimeSolution q t x d))
  change ‖directMixedSolution q t x d‖ ≤ _ at hh
  nlinarith [mul_le_mul_of_nonneg_left hx hf,mul_le_mul_of_nonneg_left ht hs]

end
end RHTower.FokasLenells
