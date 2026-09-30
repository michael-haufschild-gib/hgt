import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaContour
import GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticTail
import GaloisForLFunctions.RHTower.LiClockPairedEtaQuotientStability
import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaGrowingWindow
import GaloisForLFunctions.RHTower.LiClockWeightedResponseStability
import GaloisForLFunctions.RHTower.LiClockCentralTraceSineReflection

/-!
# Quantitative literal finite eta approximation of the complete clock

The exact paired arithmetic tails and a positive central denominator floor give
the calibrated completed source error. One actual radius transports this to
every complex clock with the sharp sinh envelope. The finite response is real
at real clocks, converges uniformly on logarithmically growing complex windows,
and preserves every fixed positive fraction of the actual source margin on
clocks up to twenty. Normalized convergence remains uniform down to zero.
-/

open Complex Set Metric Filter Topology MeasureTheory
open RiemannGaussian
namespace RHTower
noncomputable section

/-- The literal finite completed arithmetic response on the chosen source circle. -/
def liClockPairedEtaFiniteClockResponse (N : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (liClockPairedEtaFiniteSourceTrace N) r t

private theorem central_coordinate_bounds {z : ℂ} (hz : ‖z‖ ≤ 1/128) :
    ‖(1/2+z*I)-((1/2:ℝ):ℂ)‖ ≤ 1/128 ∧
    (1/4:ℝ) ≤ (1/2+z*I).re ∧ ‖(1/2+z*I)‖ ≤ (3/4:ℝ) := by
  have hs : ‖(1/2+z*I)-((1/2:ℝ):ℂ)‖ ≤ 1/128 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      add_sub_cancel_left, norm_mul, norm_I, mul_one] using hz
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hsre : (1/2+z*I).re = (1/2:ℝ)-z.im := by
    norm_num [Complex.add_re, Complex.mul_re]
    ring
  have hnorm := norm_add_le (1/2:ℂ) (z*I)
  have hhalf : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
  rw [hhalf, norm_mul, norm_I, mul_one] at hnorm
  refine ⟨hs, ?_, ?_⟩
  · rw [hsre]
    linarith [hi.2]
  · linarith

/-- The finite denominator has a strict real-part floor throughout the full central disk. -/
theorem liClockPairedEtaFiniteCore_re_gt_one_sixteenth
    (N : ℕ) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {z : ℂ} (hz : ‖z‖ ≤ 1/128) :
    (1/16:ℝ) < (pairedEtaCorePartialSum N (1/2+z*I)).re := by
  obtain ⟨hs, hσ, hR⟩ := central_coordinate_bounds hz
  have hfloor := liClockPairedEtaCore_re_gt_one_eighth_of_norm_sub_half_le hs
  have htail := liClockPairedEtaCore_sub_partialSum_norm_le_on_central_box hσ hR N
  have hre := (Complex.abs_re_le_norm
    (pairedEtaCore (1/2+z*I)-pairedEtaCorePartialSum N (1/2+z*I)))
  have hu := (le_abs_self _).trans hre
  simp only [Complex.sub_re] at hu
  linarith

/-- The literal finite arithmetic response is real at real clocks; no finite oddness is assumed. -/
theorem liClockPairedEtaFiniteClockResponse_im_ofReal_eq_zero
    (N : ℕ) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/128) (t : ℝ) :
    (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).im = 0 := by
  have hnz (z : ℂ) (hz : z ∈ closedBall (0:ℂ) r) :
      pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
    have hzNorm : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hfloor := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall (hzNorm.trans hrsmall)
    intro hzero
    norm_num [hzero] at hfloor
  exact liClockCentralTraceSineContour_im_ofReal_eq_zero hr
    (diffContOnCl_liClockPairedEtaFiniteSourceTrace_ball N hrsmall hnz)
    (liClockPairedEtaFiniteSourceTrace_neg_conj N) t

/-- Every completion term cancels exactly in the finite-minus-complete source difference. -/
theorem norm_liClockPairedEtaFiniteSourceTrace_sub_le
    (N : ℕ) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {z : ℂ} (hz : ‖z‖ ≤ 1/128) :
    ‖liClockPairedEtaFiniteSourceTrace N z-liEvenCrossActualClockPairedEtaSourceTrace z‖ ≤
      liClockPairedEtaSourceErrorEnvelope N := by
  obtain ⟨hs, hσ, hR⟩ := central_coordinate_bounds hz
  have hfloor := liClockPairedEtaCore_norm_gt_one_eighth_of_norm_sub_half_le hs
  have htail := liClockPairedEtaCore_sub_partialSum_norm_le_on_central_box hσ hR N
  have hdtail := liClockPairedEtaArithmeticDerivativeValue_sub_partialSum_norm_le_on_central_box hσ hR N
  have hd := liClockPairedEtaArithmeticDerivativeValue_norm_le_sixteen_on_central_box hσ hR
  rw [norm_sub_rev] at htail hdtail
  have hq := liClockPairedEtaQuotient_norm_sub_le hfloor htail hsmall hd hdtail
  have heq : liClockPairedEtaFiniteSourceTrace N z-liEvenCrossActualClockPairedEtaSourceTrace z =
      I*(pairedEtaCoreDerivativePartialSum N (1/2+z*I)/pairedEtaCorePartialSum N (1/2+z*I)-
        pairedEtaArithmeticDerivativeValue (1/2+z*I)/pairedEtaCore (1/2+z*I)) := by
    dsimp only [liClockPairedEtaFiniteSourceTrace, liEvenCrossActualClockPairedEtaSourceTrace,
      pairedEtaArithmeticQuotientPartialSum]
    ring
  rw [heq, norm_mul, norm_I, one_mul]
  unfold liClockPairedEtaSourceErrorEnvelope
  convert hq using 1
  ring

/-- One actual central radius transports the full finite arithmetic error to every complex clock. -/
theorem exists_liClockPairedEtaFiniteClockResponse_error_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ N : ℕ, 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16 → ∀ t : ℂ,
      ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ ≤
        (liClockPairedEtaSourceErrorEnvelope N)*Real.sinh (‖t‖/r) := by
  obtain ⟨r₀, hr₀, hr₀small, hcontour⟩ := exists_liEvenCrossActualClockPairedEtaContour_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr₀ N hsmall t => ?_⟩
  have hrsmall : r ≤ 1/128 := hrr₀.le.trans hr₀small
  have hnz (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hfloor := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall (hzNorm.le.trans hrsmall)
    intro hzero
    norm_num [hzero] at hfloor
  have hfinite := continuousOn_liClockPairedEtaFiniteSourceTrace_sphere N hrsmall hnz
  have hcomplete := (hcontour r hr hrr₀).1
  have hnonneg := liClockPairedEtaSourceErrorEnvelope_nonneg N
  have hbound (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      ‖liClockPairedEtaFiniteSourceTrace N z-liEvenCrossActualClockPairedEtaSourceTrace z‖ ≤
        liClockPairedEtaSourceErrorEnvelope N := by
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact norm_liClockPairedEtaFiniteSourceTrace_sub_le N hsmall (hzNorm.le.trans hrsmall)
  simpa only [liClockPairedEtaFiniteClockResponse, (hcontour r hr hrr₀).2 t] using
    norm_liClockCentralTraceSineContour_sub_le hr hnonneg hfinite hcomplete hbound t


private theorem normalized_clock_distance_le {X : ℂ} {t r B : ℝ}
    (ht : 0 < t) (ht20 : t ≤ 20) (hr : 0 < r) (hB : 0 ≤ B)
    (herror : ‖X-(liEvenCrossActualClockResponse t:ℂ)‖ ≤ B*Real.sinh (t/r)) :
    ‖X/(t:ℂ)-(liEvenCrossActualCurrentClockSeries (t^2/16):ℂ)‖ ≤
      B*(Real.cosh (20/r)/r) := by
  have htne : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hidentity : X/(t:ℂ)-(liEvenCrossActualCurrentClockSeries (t^2/16):ℂ) =
      (X-(liEvenCrossActualClockResponse t:ℂ))/(t:ℂ) := by
    simp only [liEvenCrossActualClockResponse, Complex.ofReal_mul]
    field_simp [htne]
  rw [hidentity, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply (div_le_iff₀ ht).2
  calc
    _ ≤ B*Real.sinh (t/r) := herror
    _ ≤ B*((Real.cosh (20/r)/r)*t) :=
      mul_le_mul_of_nonneg_left (liClock_sinh_clock_le_linear hr ht.le ht20) hB
    _ = _ := by ring

/-- Literal finite arithmetic approximates the complete response on growing complex windows
and preserves every fixed positive fraction of the actual margin on real clocks up to twenty. -/
theorem exists_liClockPairedEtaFiniteClockResponse_uniform_windows :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      (∀ c : ℝ, 0 < c → c < r/4 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ t : ℂ, ‖t‖ ≤ c*Real.log (2*(N:ℝ)+1) →
          ‖liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t‖ < ε) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t → t ≤ 20 →
        θ*((1051/2184:ℝ)*xiShiftAbsoluteMass 0)*t ≤
          (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re ∧
        0 < (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t → t ≤ 20 →
        ‖liClockPairedEtaFiniteClockResponse N r (t:ℂ)/(t:ℂ)-
          (liEvenCrossActualCurrentClockSeries (t^2/16):ℂ)‖ < ε) := by
  obtain ⟨r₀, hr₀, hr₀small, herror⟩ := exists_liClockPairedEtaFiniteClockResponse_error_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr₀ => ⟨?_, ?_, ?_⟩⟩
  · intro c hc hcr ε hε
    have hlimit := liClockPairedEtaSourceErrorEnvelope_mul_sinh_tendsto_zero hr hc hcr
    have hevent := hlimit.eventually (eventually_lt_nhds hε)
    filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth, hevent]
      with N hsmall hN
    intro t ht
    have henv : Real.sinh (‖t‖/r) ≤ Real.sinh (c*Real.log (2*(N:ℝ)+1)/r) :=
      Real.sinh_le_sinh.mpr (div_le_div_of_nonneg_right ht hr.le)
    exact ((herror r hr hrr₀ N hsmall t).trans
      (mul_le_mul_of_nonneg_left henv (liClockPairedEtaSourceErrorEnvelope_nonneg N))).trans_lt hN
  · intro θ hθ hθ1
    have hmargin : 0 < (1-θ)*((1051/2184:ℝ)*xiShiftAbsoluteMass 0) :=
      mul_pos (sub_pos.mpr hθ1) (mul_pos (by norm_num) (xiShiftAbsoluteMass_pos 0))
    have hlimit : Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N*
        (Real.cosh (20/r)/r)) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        liClockPairedEtaSourceErrorEnvelope_tendsto_zero.mul_const (Real.cosh (20/r)/r)
    have hevent := hlimit.eventually (eventually_lt_nhds hmargin)
    filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth, hevent]
      with N hsmall hN
    intro t ht ht20
    have hFerror (u : ℝ) (hu : 0 ≤ u) (_hu20 : u ≤ 20) :
        ‖liClockPairedEtaFiniteClockResponse N r (u:ℂ)-(liEvenCrossActualClockResponse u:ℂ)‖ ≤
          liClockPairedEtaSourceErrorEnvelope N*Real.sinh (u/r) := by
      simpa only [liEvenCrossActualComplexClockResponse_ofReal, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hu] using herror r hr hrr₀ N hsmall (u:ℂ)
    have hBsmall : liClockPairedEtaSourceErrorEnvelope N*Real.cosh (20/r)/r ≤
        (1-θ)*((1051/2184:ℝ)*xiShiftAbsoluteMass 0) := by
      calc
        _ = liClockPairedEtaSourceErrorEnvelope N*(Real.cosh (20/r)/r) := by ring
        _ ≤ _ := hN.le
    exact ⟨liClockApproximateResponse_ge_fraction_of_positive_margin hr
        (liClockPairedEtaSourceErrorEnvelope_nonneg N) hFerror hBsmall ht.le ht20,
      liClockApproximateResponse_pos_of_small_weighted_error hr
        (liClockPairedEtaSourceErrorEnvelope_nonneg N) hθ hFerror hBsmall ht ht20⟩


  · intro ε hε
    have hlimit : Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N*
        (Real.cosh (20/r)/r)) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        liClockPairedEtaSourceErrorEnvelope_tendsto_zero.mul_const (Real.cosh (20/r)/r)
    have hevent := hlimit.eventually (eventually_lt_nhds hε)
    filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth, hevent]
      with N hsmall hN
    intro t ht ht20
    have hFerror :
        ‖liClockPairedEtaFiniteClockResponse N r (t:ℂ)-(liEvenCrossActualClockResponse t:ℂ)‖ ≤
          liClockPairedEtaSourceErrorEnvelope N*Real.sinh (t/r) := by
      simpa only [liEvenCrossActualComplexClockResponse_ofReal, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht] using herror r hr hrr₀ N hsmall (t:ℂ)
    exact (normalized_clock_distance_le ht ht20 hr
      (liClockPairedEtaSourceErrorEnvelope_nonneg N) hFerror).trans_lt hN

end
end RHTower
