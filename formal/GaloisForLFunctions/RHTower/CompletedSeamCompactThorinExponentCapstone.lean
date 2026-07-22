import GaloisForLFunctions.RHTower.CompletedSeamCompactMarkovGermCapstone
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Compact Thorin exponents feed the completed-seam RH capstone

This module closes the exact calculus seam between a source-produced compact Thorin exponent and
the compact Markov germ criterion for RH.  The normalized logarithm of the Cassini source has
derivative equal near the origin to the completed-seam moment germ.  A local representation of
that logarithm by a finite positive compactly supported Thorin measure differentiates to the
required Markov transform, so the existing all-degree moment capstone proves RH.

The remaining producer problem is deliberately upstream: construct the compact positive measure
and prove the local exponent identity.  This interface does not assume moment positivity, a
Markov representation, or RH.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- Continuous extension at zero of the logarithmic Thorin kernel
\(x^{-1}\log(1-xz)^{-1}\). -/
def compactThorinLogKernel (x : ℝ) (z : ℂ) : ℂ :=
  if x = 0 then z else -Complex.log (1 - (x : ℂ) * z) / (x : ℂ)

private theorem norm_one_sub_real_mul_ge_half_for_thorin
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    (1 : ℝ) / 2 ≤ ‖1 - (x : ℂ) * z‖ := by
  have hxnorm : ‖(x : ℂ)‖ ≤ B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have hprod : ‖(x : ℂ) * z‖ < (1 : ℝ) / 2 := by
    rw [norm_mul]
    calc
      ‖(x : ℂ)‖ * ‖z‖ ≤ B * ‖z‖ := by gcongr
      _ < B * (1 / (2 * B)) := mul_lt_mul_of_pos_left hz hB
      _ = (1 : ℝ) / 2 := by field_simp
  have htri : (1 : ℝ) ≤ ‖1 - (x : ℂ) * z‖ + ‖(x : ℂ) * z‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - (x : ℂ) * z) + (x : ℂ) * z‖ := by ring_nf
      _ ≤ ‖1 - (x : ℂ) * z‖ + ‖(x : ℂ) * z‖ := norm_add_le _ _
  linarith

private theorem norm_inv_one_sub_real_mul_le_two_for_thorin
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    ‖(1 - (x : ℂ) * z)⁻¹‖ ≤ 2 := by
  rw [norm_inv]
  calc
    ‖1 - (x : ℂ) * z‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by norm_num) (norm_one_sub_real_mul_ge_half_for_thorin hB hx hz)
    _ = 2 := by norm_num

private theorem norm_real_mul_lt_half
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    ‖(x : ℂ) * z‖ < (1 : ℝ) / 2 := by
  rw [norm_mul]
  have hxnorm : ‖(x : ℂ)‖ ≤ B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  calc
    ‖(x : ℂ)‖ * ‖z‖ ≤ B * ‖z‖ := by gcongr
    _ < B * (1 / (2 * B)) := mul_lt_mul_of_pos_left hz hB
    _ = (1 : ℝ) / 2 := by field_simp

/-- The compact Thorin logarithmic kernel differentiates to the Markov kernel. -/
theorem hasDerivAt_compactThorinLogKernel
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    HasDerivAt (compactThorinLogKernel x)
      ((1 - (x : ℂ) * z)⁻¹) z := by
  by_cases hx0 : x = 0
  · subst x
    have hk : compactThorinLogKernel 0 = fun w : ℂ => w := by
      funext w
      simp [compactThorinLogKernel]
    rw [hk]
    simpa using hasDerivAt_id z
  · change HasDerivAt (fun w : ℂ => if x = 0 then w else
      -Complex.log (1 - (x : ℂ) * w) / (x : ℂ)) _ z
    simp only [if_neg hx0]
    have hu := norm_real_mul_lt_half hB hx hz
    have hslit : 1 - (x : ℂ) * z ∈ Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one (z := -((x : ℂ) * z))
          (by simpa using hu.trans (by norm_num))
    have hbase : HasDerivAt (fun w : ℂ => 1 - (x : ℂ) * w) (-(x : ℂ)) z := by
      simpa using (hasDerivAt_const z (1 : ℂ)).sub
        ((hasDerivAt_id z).const_mul (x : ℂ))
    have h := (hbase.clog hslit).neg.div_const (x : ℂ)
    convert h using 1
    have hden : 1 - (x : ℂ) * z ≠ 0 := Complex.slitPlane_ne_zero hslit
    field_simp [hx0, hden]

theorem norm_compactThorinLogKernel
    {B x : ℝ} (hB : 0 < B) (hx : |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    ‖compactThorinLogKernel x z‖ ≤ 2 * ‖z‖ := by
  by_cases hx0 : x = 0
  · subst x
    simp [compactThorinLogKernel]
    nlinarith [norm_nonneg z]
  · rw [compactThorinLogKernel, if_neg hx0]
    let u : ℂ := (x : ℂ) * z
    have huHalf : ‖u‖ < (1 : ℝ) / 2 := by
      simpa only [u] using norm_real_mul_lt_half hB hx hz
    have huOne : ‖u‖ < 1 := huHalf.trans (by norm_num)
    have hslit : 1 - u ∈ Complex.slitPlane := by
      simpa only [sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one (z := -u) (by simpa using huOne)
    have herr := Complex.norm_log_one_sub_inv_sub_self_le huOne
    have hdenpos : 0 < 2 * (1 - ‖u‖) := by linarith
    have hfrac : ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 ≤ ‖u‖ := by
      rw [inv_eq_one_div, mul_one_div, div_div]
      rw [mul_comm (1 - ‖u‖) 2]
      apply (div_le_iff₀ hdenpos).2
      nlinarith [norm_nonneg u]
    have hloginv : ‖Complex.log (1 - u)⁻¹‖ ≤ 2 * ‖u‖ := by
      calc
        ‖Complex.log (1 - u)⁻¹‖ ≤
            ‖Complex.log (1 - u)⁻¹ - u‖ + ‖u‖ := by
          simpa only [sub_add_cancel] using
            norm_add_le (Complex.log (1 - u)⁻¹ - u) u
        _ ≤ (‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2) + ‖u‖ := by gcongr
        _ ≤ 2 * ‖u‖ := by linarith
    have hlogeq : -Complex.log (1 - u) = Complex.log (1 - u)⁻¹ := by
      rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)]
    rw [show 1 - (x : ℂ) * z = 1 - u by rfl, hlogeq, norm_div]
    have hxnorm : ‖(x : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ofReal_ne_zero.mpr hx0)
    rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hxnorm))]
    calc
      ‖Complex.log (1 - u)⁻¹‖ ≤ 2 * ‖u‖ := hloginv
      _ = 2 * ‖z‖ * ‖(x : ℂ)‖ := by
        dsimp only [u]
        rw [norm_mul]
        ring

/-- Logarithmic Thorin exponent associated with a measure on real spectral parameters. -/
def compactThorinExponent (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, compactThorinLogKernel x z ∂μ

theorem integrable_compactThorinLogKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    {z : ℂ} (hz : ‖z‖ < 1 / (2 * B)) :
    Integrable (fun x : ℝ => compactThorinLogKernel x z) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => compactThorinLogKernel x z) μ := by
    apply Measurable.aestronglyMeasurable
    rw [show (fun x : ℝ => compactThorinLogKernel x z) =
        fun x : ℝ => if x = 0 then z else
          -Complex.log (1 - (x : ℂ) * z) / (x : ℂ) by rfl]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  refine Integrable.of_bound hmeas (2 * ‖z‖) ?_
  filter_upwards [hbound] with x hx
  exact norm_compactThorinLogKernel hB hx hz

private theorem norm_lt_thorin_radius_of_mem_ball
    {B : ℝ} {z₀ z : ℂ}
    (hz : z ∈ Metric.ball z₀ (1 / (2 * B) - ‖z₀‖)) :
    ‖z‖ < 1 / (2 * B) := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  calc
    ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
    _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
    _ < 1 / (2 * B) := by linarith

/-- Differentiation under a compact Thorin integral produces its Markov transform. -/
theorem hasDerivAt_compactThorinExponent
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {B : ℝ} (hB : 0 < B) (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < 1 / (2 * B)) :
    HasDerivAt (compactThorinExponent μ) (compactMarkovTransform μ z₀) z₀ := by
  set s : Set ℂ := Metric.ball z₀ (1 / (2 * B) - ‖z₀‖) with hs
  have hrpos : 0 < 1 / (2 * B) - ‖z₀‖ := sub_pos.mpr hz₀
  have hsnhds : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hmem : ∀ z ∈ s, ‖z‖ < 1 / (2 * B) := by
    intro z hz
    exact norm_lt_thorin_radius_of_mem_ball (by simpa [hs] using hz)
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun x : ℝ => compactThorinLogKernel x z) μ := by
    intro z
    apply Measurable.aestronglyMeasurable
    rw [show (fun x : ℝ => compactThorinLogKernel x z) =
        fun x : ℝ => if x = 0 then z else
          -Complex.log (1 - (x : ℂ) * z) / (x : ℂ) by rfl]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => (1 - (x : ℂ) * z₀)⁻¹) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmajor : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ s,
      ‖(1 - (x : ℂ) * z)⁻¹‖ ≤ (2 : ℝ) := by
    filter_upwards [hbound] with x hx z hz
    exact norm_inv_one_sub_real_mul_le_two_for_thorin hB hx (hmem z hz)
  have hdiff : ∀ᵐ x : ℝ ∂μ, ∀ z ∈ s,
      HasDerivAt (compactThorinLogKernel x)
        ((1 - (x : ℂ) * z)⁻¹) z := by
    filter_upwards [hbound] with x hx z hz
    exact hasDerivAt_compactThorinLogKernel hB hx (hmem z hz)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (z : ℂ) (x : ℝ) => compactThorinLogKernel x z)
    (F' := fun (z : ℂ) (x : ℝ) => (1 - (x : ℂ) * z)⁻¹)
    (bound := fun _ : ℝ => (2 : ℝ))
    hsnhds (Filter.Eventually.of_forall hmeas)
    (integrable_compactThorinLogKernel μ hB hbound hz₀)
    hmeas' hmajor (integrable_const _) hdiff
  rw [show compactThorinExponent μ = fun z : ℂ => ∫ x : ℝ,
      compactThorinLogKernel x z ∂μ by rfl]
  rw [show compactMarkovTransform μ z₀ =
      ∫ x : ℝ, (1 - (x : ℂ) * z₀)⁻¹ ∂μ by
    simp [compactMarkovTransform, compactMarkovKernelMoment]]
  exact hmain.2

theorem xiSquaredSeamCassiniSource_one_ne :
    xiSquaredSeamCassiniSource 1 ≠ 0 := by
  have hvalue := xiSquaredSeamCassiniSource_one_add_sq 0
  have heq : xiSquaredSeamCassiniSource 1 = XiC 0 := by simpa using hvalue
  rw [heq]
  exact XiC_zero_ne

private theorem analyticAt_negTwoCassiniShiftLogDeriv :
    AnalyticAt ℂ (fun z : ℂ =>
      -2 * logDeriv xiSquaredSeamCassiniSource (1 + z)) 0 := by
  have hsource : AnalyticAt ℂ xiSquaredSeamCassiniSource 1 :=
    differentiable_xiSquaredSeamCassiniSource.analyticAt 1
  have hlog : AnalyticAt ℂ (logDeriv xiSquaredSeamCassiniSource) 1 := by
    rw [show logDeriv xiSquaredSeamCassiniSource = fun z =>
      deriv xiSquaredSeamCassiniSource z / xiSquaredSeamCassiniSource z by rfl]
    exact hsource.deriv.div hsource xiSquaredSeamCassiniSource_one_ne
  have hshift : AnalyticAt ℂ (fun z : ℂ =>
      logDeriv xiSquaredSeamCassiniSource (1 + z)) 0 := by
    exact hlog.comp_of_eq' (analyticAt_const.add analyticAt_id) (by norm_num)
  exact analyticAt_const.mul hshift

theorem completedSeamMomentGerm_eventuallyEq_negTwoCassiniShiftLogDeriv :
    completedSeamMomentGerm =ᶠ[𝓝 0]
      fun z : ℂ => -2 * logDeriv xiSquaredSeamCassiniSource (1 + z) := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hratioCont : ContinuousAt (fun z : ℂ => ‖z‖ * M) 0 := by fun_prop
  have hratioTendsto : Tendsto (fun z : ℂ => ‖z‖ * M) (𝓝 0) (𝓝 0) := by
    have ht := hratioCont
    change Tendsto (fun z : ℂ => ‖z‖ * M) (𝓝 0)
      (𝓝 (‖(0 : ℂ)‖ * M)) at ht
    norm_num at ht
    exact ht
  have hratio : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ * M < 1 :=
    hratioTendsto.eventually_lt_const zero_lt_one
  have hsourceCont : ContinuousAt (fun z : ℂ =>
      xiSquaredSeamCassiniSource (1 + z)) 0 := by
    exact differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.comp
      ((continuousAt_const.add continuousAt_id))
  have hsource : ∀ᶠ z : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource (1 + z) ≠ 0 := by
    apply hsourceCont.eventually_ne
    simpa using xiSquaredSeamCassiniSource_one_ne
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      completedSeamMomentGerm z =
        -2 * logDeriv xiSquaredSeamCassiniSource (1 + z) := by
    filter_upwards [hratio.filter_mono nhdsWithin_le_nhds,
      hsource.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hzratio hzsource hzmem
    have hz0 : z ≠ 0 := by simpa using hzmem
    let w : ℂ := Complex.sqrt z
    have hwsq : w ^ 2 = z := by
      exact GaloisForLFunctions.HTGeometry.complex_sqrt_sq z
    have hw0 : w ≠ 0 := by
      intro hw
      apply hz0
      rw [← hwsq, hw, zero_pow (by norm_num)]
    have hXi : XiC w ≠ 0 := by
      rw [← xiSquaredSeamCassiniSource_one_add_sq]
      simpa only [hwsq] using hzsource
    have hwnorm : ‖w‖ ^ 2 = ‖z‖ := by
      rw [← norm_pow, hwsq]
    have hwratio : ‖w‖ ^ 2 * M < 1 := by simpa only [hwnorm] using hzratio
    have hmoment := xiCentralMomentGerm_eq_reciprocalSquareResolvent
      hM hbound hwratio
    have hcassini :=
      neg_two_mul_logDeriv_xiSquaredSeamCassiniSource_one_add_sq hw0 hXi
    calc
      completedSeamMomentGerm z = completedSeamMomentGerm (w ^ 2) := by rw [hwsq]
      _ = xiCentralMomentGerm w := completedSeamMomentGerm_sq_eq_xiCentralMomentGerm w
      _ = ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm w q := hmoment
      _ = ∑' q : XiZeroCopy,
          xiSquaredSeamOneCoordinate q /
            (1 - (1 + w ^ 2) * xiSquaredSeamOneCoordinate q) := by
        apply tsum_congr
        intro q
        exact xiReciprocalSquareResolventTerm_eq_cassiniResolventTerm hXi q
      _ = -2 * logDeriv xiSquaredSeamCassiniSource (1 + w ^ 2) := hcassini.symm
      _ = -2 * logDeriv xiSquaredSeamCassiniSource (1 + z) := by rw [hwsq]
  exact (analyticAt_completedSeamMomentGerm.frequently_eq_iff_eventually_eq
    analyticAt_negTwoCassiniShiftLogDeriv).mp hnear.frequently

/-- Normalized logarithmic exponent of the completed Cassini source at its central point. -/
def completedSeamSourceLogExponent (z : ℂ) : ℂ :=
  -2 * Complex.log
    (xiSquaredSeamCassiniSource (1 + z) / xiSquaredSeamCassiniSource 1)

theorem hasDerivAt_completedSeamSourceLogExponent
    {z : ℂ}
    (hslit : xiSquaredSeamCassiniSource (1 + z) /
      xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane) :
    HasDerivAt completedSeamSourceLogExponent
      (-2 * logDeriv xiSquaredSeamCassiniSource (1 + z)) z := by
  have hshift : HasDerivAt (fun w : ℂ =>
      xiSquaredSeamCassiniSource (1 + w))
      (deriv xiSquaredSeamCassiniSource (1 + z)) z := by
    have hinner : HasDerivAt (fun w : ℂ => 1 + w) 1 z := by
      simpa using (hasDerivAt_const z (1 : ℂ)).add (hasDerivAt_id z)
    simpa using
      differentiable_xiSquaredSeamCassiniSource.differentiableAt.hasDerivAt.comp z hinner
  have hratio := hshift.div_const (xiSquaredSeamCassiniSource 1)
  have hlog := hratio.clog hslit
  have hsource : xiSquaredSeamCassiniSource (1 + z) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hslit
    exact Complex.slitPlane_ne_zero hslit rfl
  have h := hlog.const_mul (-2 : ℂ)
  change HasDerivAt (fun y : ℂ => -2 * Complex.log
      (xiSquaredSeamCassiniSource (1 + y) / xiSquaredSeamCassiniSource 1))
    (-2 * logDeriv xiSquaredSeamCassiniSource (1 + z)) z
  convert h using 1
  rw [logDeriv_apply]
  field_simp [xiSquaredSeamCassiniSource_one_ne, hsource]

/-- The source exponent has exactly the completed-seam moment germ as its local derivative. -/
theorem deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm :
    deriv completedSeamSourceLogExponent =ᶠ[𝓝 0]
      completedSeamMomentGerm := by
  have hratioCont : ContinuousAt (fun z : ℂ =>
      xiSquaredSeamCassiniSource (1 + z) /
        xiSquaredSeamCassiniSource 1) 0 := by
    have hshift : ContinuousAt (fun z : ℂ =>
        xiSquaredSeamCassiniSource (1 + z)) 0 :=
      differentiable_xiSquaredSeamCassiniSource.continuous.continuousAt.comp
        (continuousAt_const.add continuousAt_id)
    exact hshift.div_const _
  have hslit : ∀ᶠ z : ℂ in 𝓝 0,
      xiSquaredSeamCassiniSource (1 + z) /
        xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane := by
    have hone : (1 : ℂ) ∈ Complex.slitPlane := Complex.one_mem_slitPlane
    have hratio0 : xiSquaredSeamCassiniSource (1 + (0 : ℂ)) /
        xiSquaredSeamCassiniSource 1 = 1 := by
      simp [xiSquaredSeamCassiniSource_one_ne]
    have hmem : xiSquaredSeamCassiniSource (1 + (0 : ℂ)) /
        xiSquaredSeamCassiniSource 1 ∈ Complex.slitPlane := by
      rw [hratio0]
      exact hone
    exact hratioCont.eventually (Complex.isOpen_slitPlane.mem_nhds hmem)
  filter_upwards [hslit,
    completedSeamMomentGerm_eventuallyEq_negTwoCassiniShiftLogDeriv]
    with z hzslit hsource
  rw [hsource]
  exact (hasDerivAt_completedSeamSourceLogExponent hzslit).deriv

/-- Upstream producer interface: a finite positive compact Thorin measure represents the exact
normalized completed-seam source exponent near the origin. -/
def PrimeArchCompactThorinExponentRepresentation : Prop :=
  ∃ (μ : Measure ℝ) (B : ℝ),
    IsFiniteMeasure μ ∧
    0 < B ∧
    (∀ᵐ x : ℝ ∂μ, 0 ≤ x ∧ |x| ≤ B) ∧
    completedSeamSourceLogExponent =ᶠ[𝓝 0] compactThorinExponent μ

/-- An exact compact Thorin exponent representation discharges the compact Markov germ premise. -/
theorem primeArchCompactMarkovGermRepresentation_of_compactThorinExponent
    (hrep : PrimeArchCompactThorinExponentRepresentation) :
    PrimeArchCompactMarkovGermRepresentation := by
  obtain ⟨μ, B, hfinite, hB, hsupport, hexponent⟩ := hrep
  letI : IsFiniteMeasure μ := hfinite
  have hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B := hsupport.mono fun _ hx => hx.2
  have hradius : (0 : ℝ) < 1 / (2 * B) := by positivity
  have hdisk : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / (2 * B) :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hradius)
  have hthorin : deriv (compactThorinExponent μ) =ᶠ[𝓝 0]
      compactMarkovTransform μ := by
    filter_upwards [hdisk] with z hz
    exact (hasDerivAt_compactThorinExponent μ hB hbound hz).deriv
  refine ⟨μ, B, hfinite, hB, hsupport, ?_⟩
  exact deriv_completedSeamSourceLogExponent_eventuallyEq_momentGerm.symm.trans
    (hexponent.deriv.trans hthorin)

/-- Right-to-left capstone: exact compact positive Thorin exponent representation implies RH. -/
theorem riemannHypothesis_of_primeArchCompactThorinExponentRepresentation
    (hrep : PrimeArchCompactThorinExponentRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchCompactMarkovGermRepresentation
    (primeArchCompactMarkovGermRepresentation_of_compactThorinExponent hrep)

end
end RHTower

