import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.LittlewoodXi
import GaloisForLFunctions.RHTower.ModulusSlopeField
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Xi radial Jensen mass and central-curvature saturation

Jensen's circle-average formula is integrated against the exact radial kernel `4 / r^3`.
Tonelli and a multiplicity-exact regrouping identify the resulting source-defined mass with
the Hermitian reciprocal-square mass of the complete Xi divisor.  Combining this value relation
with the established global reflection-defect identity proves that the reverse scalar inequality
against the prime--Gamma central curvature is equivalent to the Riemann hypothesis.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem integrableOn_log_sub_div_cube {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (Real.log x - Real.log a) / x ^ 3) (Ioi a) := by
  have hpow : IntegrableOn (fun x : ℝ => (1 / a) * x ^ (-2 : ℝ)) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha).const_mul (1 / a)
  refine hpow.mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := ha.trans hx
    exact (((Real.continuousAt_log hxpos.ne').sub continuousAt_const).div
      (continuousAt_id.pow 3) (pow_ne_zero 3 hxpos.ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := ha.trans hx
    have hlognonneg : 0 ≤ Real.log x - Real.log a := by
      exact sub_nonneg.mpr (Real.log_le_log ha hx.le)
    have hlogle : Real.log x - Real.log a ≤ x / a := by
      rw [← Real.log_div hxpos.ne' ha.ne']
      have hratio : 0 < x / a := div_pos hxpos ha
      have h := Real.log_le_sub_one_of_pos hratio
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlognonneg (pow_nonneg hxpos.le 3))]
    calc
      (Real.log x - Real.log a) / x ^ 3 ≤ (x / a) / x ^ 3 := by
        exact div_le_div_of_nonneg_right hlogle (pow_nonneg hxpos.le 3)
      _ = 1 / a * (x ^ 2)⁻¹ := by
        field_simp [hxpos.ne', ha.ne']
      _ = 1 / a * (x ^ (2 : ℝ))⁻¹ := by
        exact congrArg (fun y : ℝ => 1 / a * y⁻¹) (Real.rpow_natCast x 2).symm
      _ = 1 / a * x ^ (-2 : ℝ) := by rw [Real.rpow_neg (le_of_lt hxpos)]

theorem integral_Ioi_log_div_cube {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ in Ioi a, Real.log (x / a) / x ^ 3 = 1 / (4 * a ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    -(1 / 2 : ℝ) * (Real.log x - Real.log a) / x ^ 2 - (1 / 4 : ℝ) / x ^ 2
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt F ((Real.log x - Real.log a) / x ^ 3) x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx
    dsimp [F]
    have hlog := (Real.hasDerivAt_log hxpos.ne').sub_const (Real.log a)
    have hsq := hasDerivAt_pow 2 x
    have hfirst := (hlog.const_mul (-(1 / 2 : ℝ))).div hsq (pow_ne_zero 2 hxpos.ne')
    have hsecond := (hasDerivAt_const x (1 / 4 : ℝ)).div hsq (pow_ne_zero 2 hxpos.ne')
    convert hfirst.sub hsecond using 1 <;> field_simp <;> ring
  have hint := integrableOn_log_sub_div_cube ha
  have htend : Tendsto F atTop (nhds 0) := by
    have hrpow : (fun x : ℝ => x ^ (2 : ℝ)) =ᶠ[atTop] fun x => x ^ (2 : ℕ) :=
      Filter.Eventually.of_forall fun x => Real.rpow_natCast x 2
    have hpowtop : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).congr' hrpow
    have hlog : Tendsto (fun x : ℝ => (Real.log x - Real.log a) / x ^ 2) atTop (nhds 0) := by
      have hbaseR := (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
      have hbase : Tendsto (fun x : ℝ => Real.log x / x ^ (2 : ℕ)) atTop (nhds 0) :=
        hbaseR.congr' (Filter.Eventually.of_forall fun x =>
          congrArg (fun y : ℝ => Real.log x / y) (Real.rpow_natCast x 2))
      have hconst : Tendsto (fun x : ℝ => Real.log a / x ^ 2) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hpowtop.inv_tendsto_atTop.const_mul (Real.log a)
      simpa [sub_div] using hbase.sub hconst
    have hsq : Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
      simpa [one_div] using hpowtop.inv_tendsto_atTop
    have hcomb := (hlog.const_mul (-(1 / 2 : ℝ))).add (hsq.const_mul (-(1 / 4 : ℝ)))
    convert hcomb using 1
    · funext x
      dsimp [F]
      ring
    · ring
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  have hrewrite : (∫ x : ℝ in Ioi a, Real.log (x / a) / x ^ 3) =
      ∫ x : ℝ in Ioi a, (Real.log x - Real.log a) / x ^ 3 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.log_div (ha.trans hx).ne' ha.ne']
  rw [hrewrite, hmain]
  dsimp [F]
  simp only [sub_self, mul_zero, zero_div, neg_zero, zero_sub]
  field_simp

open Complex
open scoped ENNReal

private theorem xiDivisorSupport_countable_for_radialJensen :
    (Set.univ : Set XiDivisorSupport).Countable := by
  have hlocal : LocallyFiniteSupport
      (fun z : ℂ => MeromorphicOn.divisor xi Set.univ z) := by
    intro z
    exact (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain'
      z (Set.mem_univ z)
  apply hlocal.locallyFinite_support.countable_univ
  intro rho
  exact ⟨(rho : ℂ), rfl⟩

noncomputable local instance : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp xiDivisorSupport_countable_for_radialJensen

noncomputable local instance : Countable XiZeroCopy := inferInstance

def xiRadialJensenKernel (q : XiZeroCopy) (r : ℝ) : ℝ≥0∞ :=
  if ‖xiSpectralPoint q‖ ≤ r then
    ENNReal.ofReal (Real.log (r / ‖xiSpectralPoint q‖) / r ^ 3)
  else 0

theorem aemeasurable_xiRadialJensenKernel (q : XiZeroCopy) :
    AEMeasurable (xiRadialJensenKernel q) := by
  apply Measurable.aemeasurable
  unfold xiRadialJensenKernel
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · apply ENNReal.measurable_ofReal.comp
    fun_prop
  · exact measurable_const

theorem lintegral_xiRadialJensenKernel (q : XiZeroCopy) :
    ∫⁻ r : ℝ in Ioi 0, xiRadialJensenKernel q r =
      ENNReal.ofReal (1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by
  have ha : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  let f : ℝ → ℝ := fun r => Real.log (r / ‖xiSpectralPoint q‖) / r ^ 3
  have hint : IntegrableOn f (Ioi ‖xiSpectralPoint q‖) := by
    have h := integrableOn_log_sub_div_cube ha
    apply h.congr_fun
    · intro r hr
      dsimp [f]
      rw [Real.log_div (ha.trans hr).ne' ha.ne']
    · exact measurableSet_Ioi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi ‖xiSpectralPoint q‖)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp [f]
    have hrpos : 0 < r := ha.trans hr
    exact div_nonneg (Real.log_nonneg (by
      rw [one_le_div ha]
      exact hr.le)) (pow_nonneg hrpos.le 3)
  calc
    (∫⁻ r : ℝ in Ioi 0, xiRadialJensenKernel q r) =
        ∫⁻ r : ℝ in Ioi ‖xiSpectralPoint q‖, ENNReal.ofReal (f r) := by
      rw [← lintegral_indicator measurableSet_Ioi,
        ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro r
      by_cases hlt : ‖xiSpectralPoint q‖ < r
      · have hr0 : r ∈ Ioi (0 : ℝ) := ha.trans hlt
        have hra : r ∈ Ioi ‖xiSpectralPoint q‖ := hlt
        rw [Set.indicator_of_mem hr0, Set.indicator_of_mem hra]
        simp [xiRadialJensenKernel, hlt.le, f]
      · have hnot : r ∉ Ioi ‖xiSpectralPoint q‖ := hlt
        rw [Set.indicator_of_notMem hnot]
        by_cases hle : ‖xiSpectralPoint q‖ ≤ r
        · have heq : r = ‖xiSpectralPoint q‖ := le_antisymm (not_lt.mp hlt) hle
          subst r
          simp [xiRadialJensenKernel, ha.le]
        · simp [xiRadialJensenKernel, hle]
    _ = ENNReal.ofReal (∫ r : ℝ in Ioi ‖xiSpectralPoint q‖, f r) := by
      exact (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by
      rw [show (∫ r : ℝ in Ioi ‖xiSpectralPoint q‖, f r) =
          1 / (4 * ‖xiSpectralPoint q‖ ^ 2) by
        simpa [f] using integral_Ioi_log_div_cube ha]

def xiRadialJensenDivisorMass : ℝ≥0∞ :=
  4 * ∫⁻ r : ℝ in Ioi 0, ∑' q : XiZeroCopy, xiRadialJensenKernel q r

theorem xiRadialJensenDivisorMass_eq_hermitianMass :
    xiRadialJensenDivisorMass = ENNReal.ofReal xiReciprocalHermitianMass := by
  rw [xiRadialJensenDivisorMass]
  rw [lintegral_tsum (fun q =>
    (aemeasurable_xiRadialJensenKernel q).mono_measure (Measure.restrict_le_self))]
  simp_rw [lintegral_xiRadialJensenKernel]
  have hsum : Summable (fun q : XiZeroCopy => 1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) := by
    have h := summable_norm_xiSpectralPoint_inv_sq.mul_left (1 / 4 : ℝ)
    apply h.congr
    intro q
    rw [norm_inv, one_div, inv_pow]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by positivity) hsum]
  rw [show (∑' q : XiZeroCopy, 1 / (4 * ‖xiSpectralPoint q‖ ^ 2)) =
      (1 / 4 : ℝ) * xiReciprocalHermitianMass by
    rw [xiReciprocalHermitianMass, ← tsum_mul_left]
    apply tsum_congr
    intro q
    rw [xiReciprocalCoordinate, norm_inv, one_div, inv_pow]
    ring]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 4)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, div_eq_mul_inv]
  rw [one_mul]
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Centered source-only radial Jensen excess. -/
def xiCenteredRadialJensenExcess (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => Real.log ‖xi z‖) (1 / 2 : ℂ) r -
    Real.log ‖xi (1 / 2 : ℂ)‖

def xiRadialJensenSupportTerm (r : ℝ) (rho : XiDivisorSupport) : ℝ :=
  (((MeromorphicOn.divisor xi Set.univ) (rho : ℂ) : ℝ)) *
    if ‖(rho : ℂ) - 1 / 2‖ ≤ r then
      Real.log (r / ‖(rho : ℂ) - 1 / 2‖) / r ^ 3
    else 0

def xiRadialJensenSupportProfile (r : ℝ) : ℝ :=
  ∑' rho : XiDivisorSupport, xiRadialJensenSupportTerm r rho

private theorem finite_xiDivisorSupport_centered_norm_le {r : ℝ} (hr : 0 < r) :
    {rho : XiDivisorSupport | ‖(rho : ℂ) - 1 / 2‖ ≤ r}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  apply (xi_zeros_finite_ball (1 / 2 : ℂ) (r + 1)).subset
  rintro z ⟨rho, hrho, rfl⟩
  refine ⟨?_, xi_eq_zero_of_mem_divisor_support rho⟩
  rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev]
  linarith

private theorem xiRadialJensenSupportTerm_hasFiniteSupport {r : ℝ} (hr : 0 < r) :
    Function.HasFiniteSupport (xiRadialJensenSupportTerm r) := by
  apply (finite_xiDivisorSupport_centered_norm_le hr).subset
  intro rho hne
  by_contra hnot
  simp [xiRadialJensenSupportTerm, hnot] at hne

theorem xiCenteredRadialJensenExcess_div_cube_eq_supportProfile
    {r : ℝ} (hr : 0 < r) :
    xiCenteredRadialJensenExcess r / r ^ 3 = xiRadialJensenSupportProfile r := by
  classical
  have hhalf : xi (1 / 2 : ℂ) ≠ 0 := by
    simpa only [XiC, zero_mul, add_zero] using XiC_zero_ne
  have hJ := xi_circleAverage_log_norm (c := (1 / 2 : ℂ)) (R := r) hr.ne' hhalf
  rw [abs_of_pos hr] at hJ
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor xi Set.univ u
  let Db : ℂ → ℤ := fun u => MeromorphicOn.divisor xi
    (Metric.closedBall (1 / 2 : ℂ) r) u
  let g : ℂ → ℝ := fun u =>
    (D u : ℝ) * (if ‖u - 1 / 2‖ ≤ r then
      Real.log (r / ‖u - 1 / 2‖) / r ^ 3 else 0)
  let b : ℂ → ℝ := fun u =>
    (Db u : ℝ) * Real.log (r * ‖(1 / 2 : ℂ) - u‖⁻¹)
  have hgb : ∀ u : ℂ, g u = b u / r ^ 3 := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (1 / 2 : ℂ) r
    · have hnorm : ‖u - 1 / 2‖ ≤ r := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, norm_sub_rev] using hu
      have hD := xi_divisor_closedBall_eq_order_toNat hu
      have hDu : MeromorphicOn.divisor xi Set.univ u = ((analyticOrderAt xi u).toNat : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply xi_analyticOnNhd_univ
            (Set.mem_univ u),
          ← ENat.coe_toNat (xi_orderAt_ne_top u)]
        simp
      simp only [g, b, D, Db, hnorm, if_pos, hD, hDu]
      have harg : r / ‖u - 1 / 2‖ = r * ‖(1 / 2 : ℂ) - u‖⁻¹ := by
        rw [norm_sub_rev, div_eq_mul_inv]
      rw [harg]
      ring
    · have hnorm : ¬ ‖u - 1 / 2‖ ≤ r := by
        simpa [Metric.mem_closedBall, Complex.dist_eq, norm_sub_rev] using hu
      have hDb := xi_divisor_closedBall_eq_zero_of_notMem hu
      dsimp [g, b]
      rw [if_neg hnorm, hDb]
      simp
  have hgfin : Function.HasFiniteSupport g := by
    apply (xi_zeros_finite_ball (1 / 2 : ℂ) (r + 1)).subset
    intro u hgu
    have hgne : g u ≠ 0 := Function.mem_support.mp hgu
    have hnorm : ‖u - 1 / 2‖ ≤ r := by
      by_contra hnot
      apply hgne
      dsimp [g]
      rw [if_neg hnot, mul_zero]
    have hDu : D u ≠ 0 := by
      intro hzero
      apply hgne
      dsimp [g]
      rw [hzero, Int.cast_zero, zero_mul]
    have hz : xi u = 0 :=
      xi_eq_zero_of_mem_divisor_support ⟨u, by simpa [D, Function.mem_support] using hDu⟩
    refine ⟨?_, hz⟩
    rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev]
    linarith
  have hsupport :
      (∑' rho : XiDivisorSupport, xiRadialJensenSupportTerm r rho) = ∑' u : ℂ, g u := by
    rw [tsum_subtype]
    apply tsum_congr
    intro u
    by_cases hu : u ∈ Function.support D
    · simp [Set.indicator_of_mem hu, xiRadialJensenSupportTerm, g, D]
    · have hDu : D u = 0 := by simpa [Function.mem_support] using hu
      simp [Set.indicator_of_notMem hu, g, D, hDu]
  rw [xiRadialJensenSupportProfile, hsupport, tsum_eq_finsum hgfin]
  rw [show (∑ᶠ u : ℂ, g u) = ∑ᶠ u : ℂ, b u / r ^ 3 by
    apply finsum_congr
    exact hgb]
  simp_rw [div_eq_mul_inv]
  rw [← finsum_mul]
  change xiCenteredRadialJensenExcess r / r ^ 3 =
    (∑ᶠ u : ℂ, (Db u : ℝ) * Real.log (r * ‖(1 / 2 : ℂ) - u‖⁻¹)) / r ^ 3
  rw [xiCenteredRadialJensenExcess, hJ]
  ring

def xiRadialJensenRealKernel (q : XiZeroCopy) (r : ℝ) : ℝ :=
  if ‖xiSpectralPoint q‖ ≤ r then
    Real.log (r / ‖xiSpectralPoint q‖) / r ^ 3
  else 0

theorem xiRadialJensenRealKernel_nonneg {r : ℝ} (hr : 0 < r) (q : XiZeroCopy) :
    0 ≤ xiRadialJensenRealKernel q r := by
  unfold xiRadialJensenRealKernel
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by
      rw [one_le_div (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))]
      exact h)) (pow_nonneg hr.le 3)
  · exact le_rfl

theorem summable_xiRadialJensenRealKernel {r : ℝ} (hr : 0 < r) :
    Summable (fun q : XiZeroCopy => xiRadialJensenRealKernel q r) := by
  rw [summable_sigma_of_nonneg (fun q => xiRadialJensenRealKernel_nonneg hr q)]
  constructor
  · intro rho
    exact (hasSum_fintype _).summable
  · apply (xiRadialJensenSupportTerm_hasFiniteSupport hr).summable.congr
    intro rho
    rw [tsum_fintype]
    simp only [xiRadialJensenRealKernel, norm_xiSpectralPoint,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (rho : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support rho)
    have hcast :
        (((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)).toNat : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast]
    rfl

theorem xiRadialJensenSupportProfile_eq_tsum_realKernel {r : ℝ} (hr : 0 < r) :
    xiRadialJensenSupportProfile r =
      ∑' q : XiZeroCopy, xiRadialJensenRealKernel q r := by
  rw [(summable_xiRadialJensenRealKernel hr).tsum_sigma,
    xiRadialJensenSupportProfile]
  apply tsum_congr
  intro rho
  rw [tsum_fintype]
  simp only [xiRadialJensenRealKernel, norm_xiSpectralPoint,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (rho : ℂ) :=
    le_of_lt (xi_divisor_pos_on_support rho)
  have hcast :
      (((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)).toNat : ℝ) =
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast]
  rfl

theorem tsum_xiRadialJensenKernel_eq_ofReal_supportProfile {r : ℝ} (hr : 0 < r) :
    (∑' q : XiZeroCopy, xiRadialJensenKernel q r) =
      ENNReal.ofReal (xiRadialJensenSupportProfile r) := by
  have hsum := summable_xiRadialJensenRealKernel hr
  rw [xiRadialJensenSupportProfile_eq_tsum_realKernel hr]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun q => xiRadialJensenRealKernel_nonneg hr q) hsum]
  apply tsum_congr
  intro q
  rfl

def xiCenteredRadialJensenMassENNReal : ℝ≥0∞ :=
  4 * ∫⁻ r : ℝ in Ioi 0,
    ENNReal.ofReal (xiCenteredRadialJensenExcess r / r ^ 3)

theorem xiCenteredRadialJensenMassENNReal_eq_divisorMass :
    xiCenteredRadialJensenMassENNReal = xiRadialJensenDivisorMass := by
  rw [xiCenteredRadialJensenMassENNReal, xiRadialJensenDivisorMass]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [xiCenteredRadialJensenExcess_div_cube_eq_supportProfile hr,
    ← tsum_xiRadialJensenKernel_eq_ofReal_supportProfile hr]

def xiCenteredRadialJensenMass : ℝ :=
  xiCenteredRadialJensenMassENNReal.toReal

theorem xiCenteredRadialJensenMass_eq_hermitianMass :
    xiCenteredRadialJensenMass = xiReciprocalHermitianMass := by
  rw [xiCenteredRadialJensenMass,
    xiCenteredRadialJensenMassENNReal_eq_divisorMass,
    xiRadialJensenDivisorMass_eq_hermitianMass]
  rw [ENNReal.toReal_ofReal]
  exact tsum_nonneg fun q => sq_nonneg ‖xiReciprocalCoordinate q‖

/-- **Radial Jensen mass criterion for RH.**  An upper bound on the centered radial
Jensen mass by the exact prime--Gamma central curvature forces every Xi zero onto the
critical line. -/
theorem riemannHypothesis_of_xiCenteredRadialJensenMass_le_centralCurvature
    (h : xiCenteredRadialJensenMass ≤ primeArchCentralCurvature) :
    RiemannHypothesis := by
  rw [xiCenteredRadialJensenMass_eq_hermitianMass] at h
  exact xiReciprocalHermitianMass_eq_primeArchCentralCurvature_iff_rh.mp
    (le_antisymm h primeArchCentralCurvature_le_xiReciprocalHermitianMass)

theorem xiCenteredRadialJensenMass_eq_centralCurvature_iff_rh :
    xiCenteredRadialJensenMass = primeArchCentralCurvature ↔ RiemannHypothesis := by
  rw [xiCenteredRadialJensenMass_eq_hermitianMass]
  exact xiReciprocalHermitianMass_eq_primeArchCentralCurvature_iff_rh

theorem xiCenteredRadialJensenMass_le_centralCurvature_iff_rh :
    xiCenteredRadialJensenMass ≤ primeArchCentralCurvature ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiCenteredRadialJensenMass_le_centralCurvature
  · intro hRH
    exact (xiCenteredRadialJensenMass_eq_centralCurvature_iff_rh.mpr hRH).le

end

end RHTower
