import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicPhysicalCutoffs
import GaloisForLFunctions.HTGeometry.HardyBoundary.WeightedL2MomentContinuity

/-!
# Physical and positive Fourier energy under expanding cutoffs

The cutoffs converge strongly in L². Physical domination passes the first
moment; vanishing jump energy of the residual multiplier passes the
positive Fourier logarithmic moment.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
open CanonicalSystemOfTheWindowTower

/-- The residual multiplier complementary to the compact physical cutoff. -/
def softLogarithmicCutoffErrorVector (n : ℕ) (v : SoninL2) : SoninL2 :=
  logarithmicCutoffMultiplier
    (continuous_const.sub (continuous_softLogarithmicCutoff n)).measurable
    zero_le_one (softLogarithmicCutoff_error_abs_le n) v

theorem softLogarithmicCutoffErrorVector_eq (n : ℕ) (v : SoninL2) :
    softLogarithmicCutoffErrorVector n v = v - softLogarithmicCutoffVector n v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub v (softLogarithmicCutoffVector n v),
    logarithmicCutoffMultiplier_coeFn
      (continuous_const.sub (continuous_softLogarithmicCutoff n)).measurable
        zero_le_one (softLogarithmicCutoff_error_abs_le n) v,
    logarithmicCutoffMultiplier_coeFn (continuous_softLogarithmicCutoff n).measurable
      zero_le_one (softLogarithmicCutoff_abs_le n) v] with u hs he hc
  change softLogarithmicCutoffErrorVector n v u =
    ((1 - softLogarithmicCutoff n u : ℝ) : ℂ) * v u at he
  change softLogarithmicCutoffVector n v u =
    (softLogarithmicCutoff n u : ℂ) * v u at hc
  rw [hs]
  dsimp only [Pi.sub_apply]
  rw [he, hc, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem tendsto_softLogarithmicCutoffErrorVector (v : SoninL2) :
    Tendsto (fun n => softLogarithmicCutoffErrorVector n v) atTop (𝓝 0) := by
  apply tendsto_logarithmicCutoff_zero
    (fun n => (continuous_const.sub (continuous_softLogarithmicCutoff n)).measurable)
    softLogarithmicCutoff_error_abs_le
  intro u
  simpa only [sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_softLogarithmicCutoff u)

/-- Expanding cutoffs converge strongly to every L² profile. -/
theorem tendsto_softLogarithmicCutoffVector (v : SoninL2) :
    Tendsto (fun n => softLogarithmicCutoffVector n v) atTop (𝓝 v) := by
  have h := (tendsto_const_nhds (x := v)).sub (tendsto_softLogarithmicCutoffErrorVector v)
  have he (n : ℕ) : v - softLogarithmicCutoffErrorVector n v =
      softLogarithmicCutoffVector n v := by
    rw [softLogarithmicCutoffErrorVector_eq]
    abel
  simpa only [he, sub_zero] using h

private theorem softLogarithmicCutoff_sq_le_one (n : ℕ) (u : ℝ) :
    softLogarithmicCutoff n u ^ 2 ≤ 1 := by
  simpa only [one_pow] using pow_le_pow_left₀ (softLogarithmicCutoff_nonneg n u)
    (le_of_abs_le (softLogarithmicCutoff_abs_le n u)) 2

theorem softLogarithmicCutoffVector_firstMoment (n : ℕ) (v : SoninL2) :
    (∫ u : ℝ, |u| * ‖softLogarithmicCutoffVector n v u‖ ^ 2) =
      ∫ u : ℝ, |u| * softLogarithmicCutoff n u ^ 2 * ‖v u‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [logarithmicCutoffMultiplier_coeFn
    (continuous_softLogarithmicCutoff n).measurable zero_le_one
      (softLogarithmicCutoff_abs_le n) v] with u hu
  change softLogarithmicCutoffVector n v u = (softLogarithmicCutoff n u : ℂ) * v u at hu
  rw [hu, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem ClosedSoftLogarithmicHalfLineDomain.cutoff_firstMoment_le {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) (n : ℕ) :
    (∫ u : ℝ, |u| * ‖softLogarithmicCutoffVector n v u‖ ^ 2) ≤
      ∫ u : ℝ, |u| * ‖v u‖ ^ 2 := by
  rw [softLogarithmicCutoffVector_firstMoment]
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun u => mul_nonneg (mul_nonneg (abs_nonneg u) (sq_nonneg _))
      (sq_nonneg _)) hv.moment
  exact Eventually.of_forall fun u => by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (softLogarithmicCutoff_sq_le_one n u) (abs_nonneg u))
      (sq_nonneg ‖v u‖)

/-- Dominated convergence preserves the physical first moment under expanding cutoffs. -/
theorem ClosedSoftLogarithmicHalfLineDomain.cutoff_firstMoment_tendsto {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    Tendsto (fun n => ∫ u : ℝ, |u| * ‖softLogarithmicCutoffVector n v u‖ ^ 2) atTop
      (𝓝 (∫ u : ℝ, |u| * ‖v u‖ ^ 2)) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun u : ℝ =>
      |u| * softLogarithmicCutoff n u ^ 2 * ‖v u‖ ^ 2) :=
    ((measurable_abs.mul ((continuous_softLogarithmicCutoff n).measurable.pow_const 2)).mul
      ((Lp.stronglyMeasurable v).measurable.norm.pow_const 2)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ u : ℝ,
      ‖|u| * softLogarithmicCutoff n u ^ 2 * ‖v u‖ ^ 2‖ ≤ |u| * ‖v u‖ ^ 2 := by
    apply Eventually.of_forall
    intro u
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg u) (sq_nonneg _)) (sq_nonneg _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (softLogarithmicCutoff_sq_le_one n u) (abs_nonneg u))
      (sq_nonneg ‖v u‖)
  have hp : ∀ᵐ u : ℝ, Tendsto (fun n =>
      |u| * softLogarithmicCutoff n u ^ 2 * ‖v u‖ ^ 2) atTop (𝓝 (|u| * ‖v u‖ ^ 2)) := by
    apply Eventually.of_forall
    intro u
    simpa only [one_pow, mul_one] using
      (((tendsto_softLogarithmicCutoff u).pow 2).const_mul |u|).mul_const (‖v u‖ ^ 2)
  have h := tendsto_integral_of_dominated_convergence _ hm hv.moment hb hp
  simpa only [softLogarithmicCutoffVector_firstMoment] using h

/-- The jump commutator estimate gives convergence of positive Fourier logarithmic energy. -/
theorem ClosedSoftLogarithmicHalfLineDomain.cutoff_positiveEnergy_tendsto {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    Tendsto (fun n => ∫ ξ : ℝ, max (Real.log |ξ|) 0 *
      ‖fourierUnitary (softLogarithmicCutoffVector n v) ξ‖ ^ 2) atTop
      (𝓝 (∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2)) := by
  have herror : Tendsto (fun n => ∫ ξ : ℝ, max (Real.log |ξ|) 0 *
      ‖fourierUnitary (softLogarithmicCutoffErrorVector n v) ξ‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_logarithmicCutoff_positiveEnergy_zero
      (fun n => (continuous_const.sub (continuous_softLogarithmicCutoff n)).measurable)
      softLogarithmicCutoff_error_abs_le softLogarithmicCutoff_error_lipschitz
      (fun u => by
        simpa only [sub_self] using
          (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_softLogarithmicCutoff u))
      hv.hasReferenceEnergy
  have he (n : ℕ) : (∫ ξ : ℝ, max (Real.log |ξ|) 0 *
      ‖fourierUnitary (softLogarithmicCutoffVector n v) ξ - fourierUnitary v ξ‖ ^ 2) =
      ∫ ξ : ℝ, max (Real.log |ξ|) 0 *
        ‖fourierUnitary (softLogarithmicCutoffErrorVector n v) ξ‖ ^ 2 := by
    have hmap : fourierUnitary (softLogarithmicCutoffErrorVector n v) =
        fourierUnitary v - fourierUnitary (softLogarithmicCutoffVector n v) := by
      rw [softLogarithmicCutoffErrorVector_eq, map_sub]
    apply integral_congr_ae
    have hcoeff := Lp.coeFn_sub (fourierUnitary v)
      (fourierUnitary (softLogarithmicCutoffVector n v))
    rw [← hmap] at hcoeff
    filter_upwards [hcoeff] with ξ hξ
    rw [hξ]
    dsimp only [Pi.sub_apply]
    exact congrArg (fun r : ℝ => max (Real.log |ξ|) 0 * r ^ 2)
      (norm_sub_rev _ _)
  apply HTGeometry.tendsto_weighted_norm_sq_of_difference
    (by fun_prop : Measurable (fun ξ : ℝ => max (Real.log |ξ|) 0))
    (fun _ => le_max_right _ _)
    (fun n => ((hv.cutoff_trial n).toClosed (hv.cutoff_representative n)).integrable_positiveLogarithm)
    hv.integrable_positiveLogarithm
  simpa only [he] using herror

#print axioms tendsto_softLogarithmicCutoffVector
#print axioms ClosedSoftLogarithmicHalfLineDomain.cutoff_firstMoment_le
#print axioms ClosedSoftLogarithmicHalfLineDomain.cutoff_firstMoment_tendsto
#print axioms ClosedSoftLogarithmicHalfLineDomain.cutoff_positiveEnergy_tendsto
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

