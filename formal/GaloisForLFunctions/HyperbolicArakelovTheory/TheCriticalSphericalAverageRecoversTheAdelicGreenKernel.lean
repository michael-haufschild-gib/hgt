import GaloisForLFunctions.HyperbolicArakelovTheory.TheHyperbolicGreenKernelOfTheWeightedAdelicCarrier
import GaloisForLFunctions.HyperbolicArakelovTheory.TheArchimedeanCompensationIsSpherical
import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedGreenKernelOnTheFullAdelicProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Critical spherical averaging recovers the full adelic Green kernel

The spherical average at parameter `1/2` of the mixed hyperbolic kernel is
exactly the least nonnegative Green kernel of the all-prime weighted
adjacency. The average is integrable at every pair of vertices, including
the diagonal.

Below the critical parameter, a radial Wronskian gives a norm-convergent
operator resolvent. Its positive occupation series converges entrywise to
the established minimal Green kernel. Monotone convergence then proves
finiteness of the critical spherical integral, where the operator-norm
exponential bound alone no longer gives an integrable majorant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical ENNReal BigOperators InnerProductSpace
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic SurfaceOfSpecZ
/-- For positive `ν`, the spherical weight after cancellation of hyperbolic volume. -/
def sphericalWeight (ν r : ℝ) : ℝ := Real.sinh (ν * r) / ν

private theorem sphericalWeight_zero (ν : ℝ) : sphericalWeight ν 0 = 0 := by
  simp only [sphericalWeight, mul_zero, Real.sinh_zero, zero_div]

private theorem continuous_sphericalWeight (ν : ℝ) : Continuous (sphericalWeight ν) :=
  (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const ν

private theorem hasDerivAt_sphericalWeight {ν : ℝ} (hν : ν ≠ 0) (r : ℝ) :
    HasDerivAt (sphericalWeight ν) (Real.cosh (ν * r)) r := by
  unfold sphericalWeight
  apply (((Real.hasDerivAt_sinh (ν * r)).comp r
    ((hasDerivAt_id r).const_mul ν)).div_const ν).congr_deriv
  simp only [mul_one, mul_div_cancel_right₀ _ hν]

private theorem sphericalWeight_nonneg {ν r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r) :
    0 ≤ sphericalWeight ν r :=
  div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hν hr)) hν

private theorem sinh_le_exp (x : ℝ) : Real.sinh x ≤ Real.exp x := by
  rw [Real.sinh_eq]
  linarith only [Real.exp_pos x, Real.exp_pos (-x)]

private theorem cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -x ≤ x by linarith only [hx])
  linarith only [h]

private theorem sphericalWeight_le {ν : ℝ} (hν : 0 < ν) (r : ℝ) :
    sphericalWeight ν r ≤ ν⁻¹ * Real.exp (ν * r) := by
  rw [sphericalWeight, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_left (sinh_le_exp _) (inv_nonneg.mpr hν.le)

private theorem continuous_evolution : Continuous hyperbolicEvolution :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hyperbolicEvolution r).continuousAt

/-- The operator spherical integral, norm-convergent for `0 < ν < 1/2`. -/
def sphericalGreenTransform (ν : ℝ) : ChargeOperator :=
  ∫ r in Ioi (0 : ℝ), sphericalWeight ν r • hyperbolicEvolution r

private theorem spherical_integrand_bound {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    ‖sphericalWeight ν r • hyperbolicEvolution r‖ ≤
      ν⁻¹ * Real.exp (-((1 / 2 - ν) * r)) := by
  rw [norm_smul, Real.norm_of_nonneg (sphericalWeight_nonneg hν.le hr)]
  calc
    _ ≤ (ν⁻¹ * Real.exp (ν * r)) * Real.exp (-r / 2) :=
      mul_le_mul (sphericalWeight_le hν r) (hyperbolicEvolution_norm_le hr)
        (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hν.le) (Real.exp_pos _).le)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The full weighted charge space admits the spherical average below the critical edge. -/
theorem integrable_sphericalGreenTransform {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    IntegrableOn (fun r => sphericalWeight ν r • hyperbolicEvolution r) (Ioi (0 : ℝ)) := by
  have hmaj := (exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hν1)).const_mul ν⁻¹
  apply hmaj.mono'
  · exact ((continuous_sphericalWeight ν).smul continuous_evolution).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [neg_mul] using spherical_integrand_bound hν0 hr.le

/-- The literal shifted all-prime precision seen by a complementary spherical mode. -/
def sphericalPrecision (ν : ℝ) : ChargeOperator :=
  (edge + 1 / 4 - ν ^ 2) • 1 - adjacencyOperator

private def sphericalCompanion (ν r : ℝ) : ChargeOperator :=
  Real.cosh (ν * r) • hyperbolicEvolution r +
    sphericalWeight ν r • (hyperbolicRoot * hyperbolicEvolution r)

private theorem continuous_sphericalCompanion (ν : ℝ) : Continuous (sphericalCompanion ν) :=
  ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).smul
    continuous_evolution).add ((continuous_sphericalWeight ν).smul
      (continuous_const.mul continuous_evolution))

private theorem hasDerivAt_root_evolution (r : ℝ) :
    HasDerivAt (fun t => hyperbolicRoot * hyperbolicEvolution t)
      (-(hyperbolicPrecision * hyperbolicEvolution r)) r := by
  apply ((hasDerivAt_hyperbolicEvolution r).const_mul hyperbolicRoot).congr_deriv
  rw [← mul_assoc, mul_neg, hyperbolicRoot_squared, neg_mul]
  rfl

private theorem hasDerivAt_sphericalCompanion {ν : ℝ} (hν : ν ≠ 0) (r : ℝ) :
    HasDerivAt (sphericalCompanion ν)
      (-(sphericalPrecision ν * (sphericalWeight ν r • hyperbolicEvolution r))) r := by
  have hc : HasDerivAt (fun t => Real.cosh (ν * t))
      (ν ^ 2 * sphericalWeight ν r) r := by
    apply ((Real.hasDerivAt_cosh (ν * r)).comp r
      ((hasDerivAt_id r).const_mul ν)).congr_deriv
    unfold sphericalWeight
    field_simp [hν]
  apply ((hc.smul (hasDerivAt_hyperbolicEvolution r)).add
    ((hasDerivAt_sphericalWeight hν r).smul (hasDerivAt_root_evolution r))).congr_deriv
  rw [sphericalPrecision, hyperbolicPrecision]
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, one_mul, neg_mul]
  module

private theorem sphericalCompanion_zero (ν : ℝ) : sphericalCompanion ν 0 = 1 := by
  simp only [sphericalCompanion, mul_zero, Real.cosh_zero, hyperbolicEvolution_zero,
    sphericalWeight_zero, one_smul, zero_smul, add_zero]

private theorem sphericalCompanion_bound {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) :
    ‖sphericalCompanion ν r‖ ≤
      (1 + ν⁻¹ * ‖hyperbolicRoot‖) * Real.exp (-((1 / 2 - ν) * r)) := by
  have hc : ‖Real.cosh (ν * r) • hyperbolicEvolution r‖ ≤
      Real.exp (-((1 / 2 - ν) * r)) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.cosh_pos _).le]
    calc
      _ ≤ Real.exp (ν * r) * Real.exp (-r / 2) :=
        mul_le_mul (cosh_le_exp (mul_nonneg hν.le hr)) (hyperbolicEvolution_norm_le hr)
          (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : ‖sphericalWeight ν r • (hyperbolicRoot * hyperbolicEvolution r)‖ ≤
      ‖hyperbolicRoot‖ * (ν⁻¹ * Real.exp (-((1 / 2 - ν) * r))) := by
    rw [← mul_smul_comm]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (spherical_integrand_bound hν hr) (norm_nonneg _))
  exact (norm_add_le _ _).trans (by nlinarith only [hc, hs])

private theorem tendsto_sphericalCompanion {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    Tendsto (sphericalCompanion ν) atTop (𝓝 0) := by
  have hexp : Tendsto (fun r : ℝ => Real.exp (-((1 / 2 - ν) * r))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (sub_pos.mpr hν1) tendsto_id))
  have h := hexp.const_mul (1 + ν⁻¹ * ‖hyperbolicRoot‖)
  rw [mul_zero] at h
  apply squeeze_zero_norm' _ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact sphericalCompanion_bound hν0 hr

/-- Integrating the radial Wronskian gives an actual all-prime resolvent identity. -/
theorem sphericalPrecision_mul_transform {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    sphericalPrecision ν * sphericalGreenTransform ν = 1 := by
  have hi := integrable_sphericalGreenTransform hν0 hν1
  have hderiv := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuous_sphericalCompanion ν).continuousWithinAt)
    (fun r _ => hasDerivAt_sphericalCompanion hν0.ne' r)
    ((hi.const_mul (sphericalPrecision ν)).neg) (tendsto_sphericalCompanion hν0 hν1)
  have hmul := (ContinuousLinearMap.mul ℝ ChargeOperator (sphericalPrecision ν)).integral_comp_comm hi
  change (∫ r in Ioi (0 : ℝ), sphericalPrecision ν *
    (sphericalWeight ν r • hyperbolicEvolution r)) =
      sphericalPrecision ν * sphericalGreenTransform ν at hmul
  rw [sphericalCompanion_zero, integral_neg, hmul] at hderiv
  change -(sphericalPrecision ν * sphericalGreenTransform ν) = 0 - 1 at hderiv
  linear_combination (norm := module) -hderiv

private def walkOperator : ChargeOperator := edge⁻¹ • adjacencyOperator
private def walkSeed (x : FiniteVertices) : ChargeSpace := edge⁻¹ • lp.single 2 x (1 : ℝ)
private def walkState (x : FiniteVertices) (n : ℕ) : ChargeSpace :=
  (walkOperator ^ n) (walkSeed x)
private def walkPolynomial (x : FiniteVertices) (N : ℕ) : ChargeSpace :=
  ∑ n ∈ Finset.range N, walkState x n

/-- The contribution of one occupation depth to the actual critical Green column. -/
def occupationTerm (x y : FiniteVertices) (n : ℕ) : ℝ := walkState x n y

private theorem delta_nonneg (x y : FiniteVertices) :
    0 ≤ (lp.single 2 x (1 : ℝ) : ChargeSpace) y := by
  by_cases h : y = x
  · subst y
    rw [lp.single_apply_self]
    norm_num
  · simpa only [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 h]
      using (le_refl (0 : ℝ))

private theorem walkOperator_nonneg (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ walkOperator f y :=
  mul_nonneg (inv_nonneg.mpr edge_pos.le) (adjacencyOperator_nonneg f hf y)

private theorem walkState_succ (x : FiniteVertices) (n : ℕ) :
    walkState x (n + 1) = walkOperator (walkState x n) := by
  rw [walkState, pow_succ', mul_apply_eq_comp]
  rfl

private theorem occupationTerm_nonneg (x y : FiniteVertices) (n : ℕ) :
    0 ≤ occupationTerm x y n := by
  change 0 ≤ walkState x n y
  induction n generalizing y with
  | zero => exact mul_nonneg (inv_nonneg.mpr edge_pos.le) (delta_nonneg x y)
  | succ n ih =>
      rw [walkState_succ]
      exact walkOperator_nonneg _ ih y

private theorem walkPolynomial_succ (x : FiniteVertices) (N : ℕ) :
    walkPolynomial x (N + 1) = walkSeed x + walkOperator (walkPolynomial x N) := by
  rw [walkPolynomial, Finset.sum_range_succ']
  simp only [walkState_succ, ← map_sum]
  change walkOperator (walkPolynomial x N) + walkSeed x = _
  exact add_comm _ _

private theorem walkSeed_apply (x y : FiniteVertices) :
    walkSeed x y = pointMass x y / edge := by
  by_cases h : y = x
  · subst y
    change edge⁻¹ * (lp.single 2 x (1 : ℝ) : ChargeSpace) x = _
    rw [lp.single_apply_self]
    simp [pointMass]
  · change edge⁻¹ * (lp.single 2 x (1 : ℝ) : ChargeSpace) y = _
    rw [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 h]
    simp only [pointMass, if_neg (Ne.symm h), mul_zero, zero_div]

private theorem walkOperator_apply (f : ChargeSpace) (y : FiniteVertices) :
    walkOperator f y = adjacency f y / edge := by
  change edge⁻¹ * adjacencyOperator f y = _
  rw [adjacencyOperator_apply, div_eq_mul_inv, mul_comm]

private theorem walkPolynomial_apply (x y : FiniteVertices) (N : ℕ) :
    walkPolynomial x N y = occupationPartial x N y := by
  induction N generalizing y with
  | zero => simp only [walkPolynomial, Finset.range_zero, Finset.sum_empty, occupationPartial]; rfl
  | succ N ih =>
      rw [walkPolynomial_succ]
      change walkSeed x y + walkOperator (walkPolynomial x N) y = _
      rw [walkSeed_apply, walkOperator_apply]
      have he : (walkPolynomial x N : FiniteVertices → ℝ) = occupationPartial x N := funext ih
      calc
        _ = pointMass x y / edge + adjacency (occupationPartial x N) y / edge :=
          congrArg (fun z : ℝ => pointMass x y / edge + z / edge)
            (congrArg (fun f : FiniteVertices → ℝ => adjacency f y) he)
        _ = occupationPartial x (N + 1) y := by rw [occupationPartial]; ring

private theorem sum_occupationTerm (x y : FiniteVertices) (N : ℕ) :
    ∑ n ∈ Finset.range N, occupationTerm x y n = occupationPartial x N y := by
  let ev : ChargeSpace →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y
  calc
    _ = ev (∑ n ∈ Finset.range N, walkState x n) :=
      (map_sum ev (fun n => walkState x n) (Finset.range N)).symm
    _ = occupationPartial x N y := walkPolynomial_apply x y N

/-- The critical occupation series is summable pointwise, including its diagonal. -/
theorem hasSum_occupationTerm (x y : FiniteVertices) :
    HasSum (occupationTerm x y) (green x y) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (occupationTerm_nonneg x y) _).mpr
  simpa only [sum_occupationTerm] using tendsto_partial x y

private theorem walkOperator_norm_le : ‖walkOperator‖ ≤ 1 := by
  rw [walkOperator, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr edge_pos.le)]
  calc
    _ ≤ edge⁻¹ * edge := mul_le_mul_of_nonneg_left adjacencyOperator_norm_le
      (inv_nonneg.mpr edge_pos.le)
    _ = 1 := inv_mul_cancel₀ edge_pos.ne'

private theorem dampedWalk_norm_lt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖q • walkOperator‖ < 1 := by
  rw [norm_smul, Real.norm_of_nonneg hq0]
  exact (mul_le_mul_of_nonneg_left walkOperator_norm_le hq0).trans_lt (by simpa using hq1)

private def abelGreenOperator (q : ℝ) : ChargeOperator :=
  (q / edge) • ∑' n : ℕ, (q • walkOperator) ^ n

private theorem abelGreenOperator_entry {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x y : FiniteVertices) :
    abelGreenOperator q (lp.single 2 x (1 : ℝ)) y =
      ∑' n : ℕ, q ^ (n + 1) * occupationTerm x y n := by
  let ev : ChargeOperator →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
      (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 x (1 : ℝ)))
  have hs := summable_geometric_of_norm_lt_one (dampedWalk_norm_lt hq0 hq1)
  change (q / edge) * ev (∑' n : ℕ, (q • walkOperator) ^ n) = _
  rw [ev.map_tsum hs, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [smul_pow]
  change (q / edge) * (q ^ n * (walkOperator ^ n) (lp.single 2 x (1 : ℝ)) y) =
    q ^ (n + 1) * ((walkOperator ^ n) (edge⁻¹ • lp.single 2 x (1 : ℝ))) y
  rw [map_smul, pow_succ]
  change _ = q ^ n * q * (edge⁻¹ * (walkOperator ^ n) (lp.single 2 x (1 : ℝ)) y)
  ring

private def sphericalScale (ν : ℝ) : ℝ := edge + 1 / 4 - ν ^ 2
private def sphericalDamping (ν : ℝ) : ℝ := edge / sphericalScale ν

private theorem sphericalScale_gt_edge {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    edge < sphericalScale ν := by
  unfold sphericalScale
  nlinarith only [hν0, hν1]

private theorem sphericalDamping_bounds {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    0 ≤ sphericalDamping ν ∧ sphericalDamping ν < 1 := by
  have hc : 0 < sphericalScale ν := edge_pos.trans (sphericalScale_gt_edge hν0 hν1)
  exact ⟨(div_pos edge_pos hc).le, (div_lt_one hc).mpr (sphericalScale_gt_edge hν0 hν1)⟩

private theorem sphericalPrecision_factor {ν : ℝ} (hc : sphericalScale ν ≠ 0) :
    sphericalPrecision ν = sphericalScale ν • (1 - sphericalDamping ν • walkOperator) := by
  rw [sphericalPrecision, sphericalDamping, walkOperator, smul_sub, smul_smul, smul_smul]
  have hscale : sphericalScale ν * (edge / sphericalScale ν) * edge⁻¹ = 1 := by
    field_simp [hc, edge_pos.ne']
  rw [hscale, one_smul]
  rfl

private theorem sphericalPrecision_abel_inverse {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2) :
    sphericalPrecision ν * abelGreenOperator (sphericalDamping ν) = 1 ∧
      abelGreenOperator (sphericalDamping ν) * sphericalPrecision ν = 1 := by
  obtain ⟨hq0, hq1⟩ := sphericalDamping_bounds hν0 hν1
  have hc := (edge_pos.trans (sphericalScale_gt_edge hν0 hν1)).ne'
  have hs : sphericalScale ν * (sphericalDamping ν / edge) = 1 := by
    rw [sphericalDamping]
    field_simp [hc, edge_pos.ne']
  have hn := dampedWalk_norm_lt hq0 hq1
  constructor
  · rw [sphericalPrecision_factor hc, abelGreenOperator, smul_mul_assoc, mul_smul_comm,
      mul_neg_geom_series _ hn, smul_smul, hs, one_smul]
  · rw [sphericalPrecision_factor hc, abelGreenOperator, smul_mul_assoc, mul_smul_comm,
      geom_series_mul_neg _ hn, smul_smul]
    rw [mul_comm (sphericalDamping ν / edge), hs, one_smul]

/-- The actual spherical resolvent has a positive occupation expansion at every vertex. -/
private theorem sphericalGreenTransform_entry {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2)
    (x y : FiniteVertices) :
    sphericalGreenTransform ν (lp.single 2 x (1 : ℝ)) y =
      ∑' n : ℕ, sphericalDamping ν ^ (n + 1) * occupationTerm x y n := by
  have he : sphericalGreenTransform ν = abelGreenOperator (sphericalDamping ν) := by
    calc
      _ = (abelGreenOperator (sphericalDamping ν) * sphericalPrecision ν) * sphericalGreenTransform ν := by
        rw [(sphericalPrecision_abel_inverse hν0 hν1).2, one_mul]
      _ = _ := by rw [mul_assoc, sphericalPrecision_mul_transform hν0 hν1, mul_one]
  rw [he]
  exact abelGreenOperator_entry (sphericalDamping_bounds hν0 hν1).1
    (sphericalDamping_bounds hν0 hν1).2 x y

private theorem sphericalWeight_integral {ν : ℝ} (hν : 0 < ν) (r : ℝ) :
    (∫ t in (0 : ℝ)..r, Real.cosh (ν * t)) = sphericalWeight ν r := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_sphericalWeight hν.ne' t)
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 r)
  simpa only [sphericalWeight_zero, sub_zero] using h

private theorem sphericalWeight_mono {ν κ r : ℝ} (hν : 0 < ν) (hκ : ν ≤ κ)
    (hr : 0 ≤ r) : sphericalWeight ν r ≤ sphericalWeight κ r := by
  rw [← sphericalWeight_integral hν, ← sphericalWeight_integral (hν.trans_le hκ)]
  apply intervalIntegral.integral_mono_on hr
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 r)
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 r)
  intro t ht
  apply Real.cosh_le_cosh.mpr
  change |ν * t| ≤ |κ * t|
  rw [abs_of_nonneg (mul_nonneg hν.le ht.1),
    abs_of_nonneg (mul_nonneg (hν.trans_le hκ).le ht.1)]
  exact mul_le_mul_of_nonneg_right hκ ht.1

private def entryEvaluation (x y : FiniteVertices) : ChargeOperator →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
    (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 x (1 : ℝ)))

/-- The radial density of a spherical average, after cancellation of hyperbolic volume. -/
def sphericalGreenDensity (ν : ℝ) (x y : FiniteVertices) (r : ℝ) : ℝ :=
  sphericalWeight ν r * (hyperbolicEvolution r (lp.single 2 x (1 : ℝ))) y

private theorem sphericalGreenDensity_evaluation (ν r : ℝ) (x y : FiniteVertices) :
    sphericalGreenDensity ν x y r =
      entryEvaluation x y (sphericalWeight ν r • hyperbolicEvolution r) := rfl

private theorem continuous_sphericalGreenDensity (ν : ℝ) (x y : FiniteVertices) :
    Continuous (sphericalGreenDensity ν x y) :=
  (continuous_sphericalWeight ν).mul ((entryEvaluation x y).continuous.comp continuous_evolution)

private theorem sphericalGreenDensity_nonneg {ν r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (x y : FiniteVertices) : 0 ≤ sphericalGreenDensity ν x y r :=
  mul_nonneg (sphericalWeight_nonneg hν hr)
    (hyperbolicEvolution_nonneg hr _ (delta_nonneg x) y)

private theorem integrable_sphericalGreenDensity {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2)
    (x y : FiniteVertices) : IntegrableOn (sphericalGreenDensity ν x y) (Ioi (0 : ℝ)) :=
  (entryEvaluation x y).integrable_comp (integrable_sphericalGreenTransform hν0 hν1)

private theorem integral_sphericalGreenDensity {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1 / 2)
    (x y : FiniteVertices) :
    (∫ r in Ioi (0 : ℝ), sphericalGreenDensity ν x y r) =
      ∑' n : ℕ, sphericalDamping ν ^ (n + 1) * occupationTerm x y n := by
  simp_rw [sphericalGreenDensity_evaluation]
  rw [(entryEvaluation x y).integral_comp_comm (integrable_sphericalGreenTransform hν0 hν1)]
  exact sphericalGreenTransform_entry hν0 hν1 x y

private def sphericalApproach (n : ℕ) : ℝ := (1 - (1 / 2 : ℝ) ^ (n + 1)) / 2

private theorem sphericalApproach_bounds (n : ℕ) :
    0 < sphericalApproach n ∧ sphericalApproach n < 1 / 2 := by
  have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hlt : (1 / 2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  unfold sphericalApproach
  constructor <;> linarith only [hp, hlt]

private theorem sphericalApproach_mono : Monotone sphericalApproach := by
  apply monotone_nat_of_le_succ
  intro n
  unfold sphericalApproach
  rw [pow_succ (1 / 2 : ℝ) (n + 1)]
  have hp := pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (n + 1)
  linarith only [hp]

private theorem tendsto_sphericalApproach : Tendsto sphericalApproach atTop (𝓝 (1 / 2)) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x := (1 : ℝ)).sub hp).div_const (2 : ℝ)
  rw [sub_zero] at h
  exact h

private theorem tendsto_sphericalDamping :
    Tendsto (fun n => sphericalDamping (sphericalApproach n)) atTop (𝓝 1) := by
  have hc : Tendsto (fun n => sphericalScale (sphericalApproach n)) atTop (𝓝 edge) := by
    have h := (tendsto_const_nhds (x := edge + (1 / 4 : ℝ))).sub (tendsto_sphericalApproach.pow 2)
    convert h using 1 <;> norm_num [sphericalScale]
  have h := (tendsto_const_nhds (x := edge)).div hc edge_pos.ne'
  rw [div_self edge_pos.ne'] at h
  exact h

private theorem tendsto_integral_sphericalGreenDensity (x y : FiniteVertices) :
    Tendsto (fun n => ∫ r in Ioi (0 : ℝ), sphericalGreenDensity (sphericalApproach n) x y r)
      atTop (𝓝 (green x y)) := by
  have hsum := hasSum_occupationTerm x y
  have ht : Tendsto
      (fun n => ∑' k : ℕ, sphericalDamping (sphericalApproach n) ^ (k + 1) * occupationTerm x y k)
      atTop (𝓝 (∑' k : ℕ, occupationTerm x y k)) := by
    apply tendsto_tsum_of_dominated_convergence hsum.summable
    · intro k
      simpa only [one_pow, one_mul] using
        (tendsto_sphericalDamping.pow (k + 1)).mul_const (occupationTerm x y k)
    · exact Eventually.of_forall fun n k => by
        obtain ⟨hq0, hq1⟩ := sphericalDamping_bounds
          (sphericalApproach_bounds n).1 (sphericalApproach_bounds n).2
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hq0 _) (occupationTerm_nonneg x y k))]
        exact mul_le_of_le_one_left (occupationTerm_nonneg x y k)
          (pow_le_one₀ hq0 hq1.le)
  rw [hsum.tsum_eq] at ht
  refine ht.congr' (Eventually.of_forall fun n => ?_)
  exact (integral_sphericalGreenDensity (sphericalApproach_bounds n).1
    (sphericalApproach_bounds n).2 x y).symm

private theorem tendsto_sphericalGreenDensity (x y : FiniteVertices) (r : ℝ) :
    Tendsto (fun n => sphericalGreenDensity (sphericalApproach n) x y r) atTop
      (𝓝 (sphericalGreenDensity (1 / 2) x y r)) := by
  have hw := (Real.continuous_sinh.continuousAt.tendsto.comp
    (tendsto_sphericalApproach.mul_const r)).div tendsto_sphericalApproach (by norm_num)
  exact hw.mul_const _

private theorem critical_lintegral (x y : FiniteVertices) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (sphericalGreenDensity (1 / 2) x y r)) =
      ENNReal.ofReal (green x y) := by
  have hmon := lintegral_tendsto_of_tendsto_of_monotone
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun n r => ENNReal.ofReal (sphericalGreenDensity (sphericalApproach n) x y r))
    (F := fun r => ENNReal.ofReal (sphericalGreenDensity (1 / 2) x y r))
    (fun n => (ENNReal.continuous_ofReal.comp
      (continuous_sphericalGreenDensity (sphericalApproach n) x y)).aemeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      intro n m hnm
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (sphericalWeight_mono (sphericalApproach_bounds n).1 (sphericalApproach_mono hnm) hr.le)
        (hyperbolicEvolution_nonneg hr.le _ (delta_nonneg x) y))
    (Eventually.of_forall fun r => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_sphericalGreenDensity x y r))
  have he (n : ℕ) :
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (sphericalGreenDensity (sphericalApproach n) x y r)) =
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ), sphericalGreenDensity (sphericalApproach n) x y r) := by
    apply (ofReal_integral_eq_lintegral_ofReal
      (integrable_sphericalGreenDensity (sphericalApproach_bounds n).1
        (sphericalApproach_bounds n).2 x y) _).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact sphericalGreenDensity_nonneg (sphericalApproach_bounds n).1.le hr.le x y
  simp_rw [he] at hmon
  exact tendsto_nhds_unique hmon (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_integral_sphericalGreenDensity x y))

/-- The critical spherical density is integrable at every pair of finite adelic vertices. -/
theorem integrable_critical_sphericalGreenDensity (x y : FiniteVertices) :
    IntegrableOn (sphericalGreenDensity (1 / 2) x y) (Ioi (0 : ℝ)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (continuous_sphericalGreenDensity (1 / 2) x y).aestronglyMeasurable _).mp
  · rw [critical_lintegral]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact sphericalGreenDensity_nonneg (by norm_num) hr.le x y

/-- At the complementary edge, the mixed hyperbolic kernel averages to the minimal
all-prime Green kernel. Finiteness is entrywise, including the diagonal. -/
theorem integral_critical_sphericalGreenDensity (x y : FiniteVertices) :
    (∫ r in Ioi (0 : ℝ), sphericalGreenDensity (1 / 2) x y r) = green x y := by
  have he := ofReal_integral_eq_lintegral_ofReal (integrable_critical_sphericalGreenDensity x y)
    (show 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] sphericalGreenDensity (1 / 2) x y from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact sphericalGreenDensity_nonneg (by norm_num) hr.le x y)
  rw [critical_lintegral] at he
  have hn : 0 ≤ ∫ r in Ioi (0 : ℝ), sphericalGreenDensity (1 / 2) x y r := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact sphericalGreenDensity_nonneg (by norm_num) hr.le x y
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal (green_nonneg x y)] using ht

private theorem spherical_volume_density {r : ℝ} (hr : 0 < r) (x y : FiniteVertices) :
    (4 * Real.pi * Real.sinh r ^ 2 * sphericalFn (1 / 2) r) * mixedGreenEntry r x y =
      sphericalGreenDensity (1 / 2) x y r := by
  have hs : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr).ne'
  change (4 * Real.pi * Real.sinh r ^ 2 * sphericalFn (1 / 2) r) *
    (hyperbolicGreen 1 r * (hyperbolicEvolution r (lp.single 2 x (1 : ℝ))) y) = _
  unfold sphericalGreenDensity sphericalWeight sphericalFn hyperbolicGreen
  simp only [sub_self, neg_zero, zero_mul, Real.exp_zero]
  field_simp [hs, Real.pi_ne_zero]

/-- The actual hyperbolic volume and critical spherical function give an integrable
average of the mixed Green kernel, with every finite place retained. -/
theorem integrable_critical_spherical_average (x y : FiniteVertices) :
    IntegrableOn (fun r =>
      (4 * Real.pi * Real.sinh r ^ 2 * sphericalFn (1 / 2) r) * mixedGreenEntry r x y)
      (Ioi (0 : ℝ)) := by
  apply (integrable_critical_sphericalGreenDensity x y).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (spherical_volume_density hr x y).symm

/-- The critical spherical average of the mixed hyperbolic kernel is exactly the
least nonnegative Green kernel of the full weighted adelic adjacency. -/
theorem critical_spherical_average_eq_green (x y : FiniteVertices) :
    (∫ r in Ioi (0 : ℝ),
      (4 * Real.pi * Real.sinh r ^ 2 * sphericalFn (1 / 2) r) * mixedGreenEntry r x y) =
      green x y := by
  calc
    _ = ∫ r in Ioi (0 : ℝ), sphericalGreenDensity (1 / 2) x y r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact spherical_volume_density hr x y
    _ = green x y := integral_critical_sphericalGreenDensity x y

#print axioms sphericalPrecision_mul_transform
#print axioms hasSum_occupationTerm
#print axioms critical_spherical_average_eq_green
#print axioms integrable_critical_spherical_average
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
