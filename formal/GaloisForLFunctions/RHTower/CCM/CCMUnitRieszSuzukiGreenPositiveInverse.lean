import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszSuzukiGreenProducerClassification
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewSubexponentialCriterion

/-!
# Positive inverse of the Suzuki unit-Riesz Green filter

The Green filter is `K f = f + (1/2) R_(1/2) f - 2 R_1 f`, where each `R_a` is
the exponential resolvent starting at a fixed base. Its inverse is exactly
`g + (3/2) I g + (1/2) I² g`. These positive coefficients preserve one-sided bounds.

For the literal Suzuki Green source, the base terms are retained explicitly and bounded.
An upper Green bound therefore gives a quadratic lower bound on the screw function;
the existing subexponential Landau criterion yields RH. The resulting equivalence needs
only a one-sided Green bound. It does not assert that this bound holds unconditionally,
or transfer an integer-logarithmic bound to all real apertures.
-/

open Set MeasureTheory Topology
noncomputable section

namespace RHTower.UnitRieszGreenInverse

def resolvent (rate base : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-rate * t) * ∫ u in base..t, Real.exp (rate * u) * f u

theorem hasDerivAt_resolvent {f : ℝ → ℝ} (hf : Continuous f)
    (rate base t : ℝ) :
    HasDerivAt (resolvent rate base f) (f t - rate * resolvent rate base f t) t := by
  have hc : Continuous (fun u => Real.exp (rate * u) * f u) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (a := base)
    (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  have he := (Real.hasDerivAt_exp (-rate * t)).comp t
    ((hasDerivAt_id t).const_mul (-rate))
  have hcancel : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  convert he.mul hi using 1 <;> first
  | rfl
  | (simp only [resolvent, Function.comp_apply, mul_one]
     linear_combination -(f t) * hcancel)

theorem continuous_resolvent {f : ℝ → ℝ} (hf : Continuous f) (rate base : ℝ) :
    Continuous (resolvent rate base f) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_resolvent hf rate base t).continuousAt

@[simp] theorem resolvent_base (rate base : ℝ) (f : ℝ → ℝ) :
    resolvent rate base f base = 0 := by simp [resolvent]

theorem resolvent_eq_integral (rate base : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    resolvent rate base f t = ∫ u in base..t, Real.exp (rate * (u - t)) * f u := by
  rw [resolvent, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

def greenFilter (base : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t + (1 / 2 : ℝ) * resolvent (1 / 2) base f t - 2 * resolvent 1 base f t

theorem continuous_greenFilter {f : ℝ → ℝ} (hf : Continuous f) (base : ℝ) :
    Continuous (greenFilter base f) :=
  (hf.add ((continuous_resolvent hf _ _).const_mul _)).sub
    ((continuous_resolvent hf _ _).const_mul _)

theorem integral_greenFilter {f : ℝ → ℝ} (hf : Continuous f) (base t : ℝ) :
    (∫ u in base..t, greenFilter base f u) =
      -resolvent (1 / 2) base f t + 2 * resolvent 1 base f t := by
  have hd (u : ℝ) : HasDerivAt
      (fun v => -resolvent (1 / 2) base f v + 2 * resolvent 1 base f v)
      (greenFilter base f u) u := by
    convert (hasDerivAt_resolvent hf (1 / 2) base u).neg.add
      ((hasDerivAt_resolvent hf 1 base u).const_mul 2) using 1 <;>
      first | rfl | (simp only [greenFilter]; ring)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_greenFilter hf base).intervalIntegrable base t)

theorem continuous_integral {f : ℝ → ℝ} (hf : Continuous f) (base : ℝ) :
    Continuous (fun t => ∫ u in base..t, f u) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter volume (𝓝 t)) hf.continuousAt).continuousAt

theorem integral_integral_greenFilter {f : ℝ → ℝ} (hf : Continuous f) (base t : ℝ) :
    (∫ u in base..t, ∫ v in base..u, greenFilter base f v) =
      2 * resolvent (1 / 2) base f t - 2 * resolvent 1 base f t := by
  have hd (u : ℝ) : HasDerivAt
      (fun v => 2 * resolvent (1 / 2) base f v - 2 * resolvent 1 base f v)
      (∫ v in base..u, greenFilter base f v) u := by
    rw [integral_greenFilter hf]
    convert ((hasDerivAt_resolvent hf (1 / 2) base u).const_mul 2).sub
      ((hasDerivAt_resolvent hf 1 base u).const_mul 2) using 1 <;> first | rfl | ring
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_integral (continuous_greenFilter hf base) base).intervalIntegrable base t)

def positiveInverse (base : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  g t + (3 / 2 : ℝ) * (∫ u in base..t, g u) +
    (1 / 2 : ℝ) * (∫ u in base..t, ∫ v in base..u, g v)

theorem positiveInverse_greenFilter {f : ℝ → ℝ} (hf : Continuous f) (base t : ℝ) :
    positiveInverse base (greenFilter base f) t = f t := by
  rw [positiveInverse, integral_greenFilter hf, integral_integral_greenFilter hf, greenFilter]
  ring

theorem positiveInverse_congr {f g : ℝ → ℝ} {base t : ℝ} (ht : base ≤ t)
    (hfg : ∀ u ∈ Icc base t, f u = g u) :
    positiveInverse base f t = positiveInverse base g t := by
  have hi (u : ℝ) (hu : u ∈ Icc base t) :
      (∫ v in base..u, f v) = ∫ v in base..u, g v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hu.1] at hv
    exact hfg v ⟨hv.1, hv.2.trans hu.2⟩
  have hii : (∫ u in base..t, ∫ v in base..u, f v) =
      ∫ u in base..t, ∫ v in base..u, g v := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact hi u hu
  rw [positiveInverse, positiveInverse, hfg t ⟨ht, le_rfl⟩, hi t ⟨ht, le_rfl⟩, hii]

theorem positiveInverse_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {base t : ℝ} (ht : base ≤ t) (hfg : ∀ u ∈ Icc base t, f u ≤ g u) :
    positiveInverse base f t ≤ positiveInverse base g t := by
  have hi (u : ℝ) (hu : u ∈ Icc base t) :
      (∫ v in base..u, f v) ≤ ∫ v in base..u, g v := by
    apply intervalIntegral.integral_mono_on hu.1 (hf.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
    intro v hv
    exact hfg v ⟨hv.1, hv.2.trans hu.2⟩
  have hii := intervalIntegral.integral_mono_on (μ := volume) ht
    ((continuous_integral hf base).intervalIntegrable base t)
    ((continuous_integral hg base).intervalIntegrable base t) hi
  have hit := hi t ⟨ht, le_rfl⟩
  have hft := hfg t ⟨ht, le_rfl⟩
  dsimp [positiveInverse]
  linarith

theorem positiveInverse_const (base B t : ℝ) :
    positiveInverse base (fun _ => B) t =
      B * (1 + (3 / 2 : ℝ) * (t - base) + (1 / 4 : ℝ) * (t - base) ^ 2) := by
  have hi : (∫ u in base..t, B * (u - base)) = B * (t - base) ^ 2 / 2 := by
    have hd (u : ℝ) : HasDerivAt (fun v : ℝ => B * (v - base) ^ 2 / 2)
        (B * (u - base)) u := by
      convert ((((hasDerivAt_id u).sub_const base).pow 2).const_mul B).div_const 2
        using 1 <;> first | rfl | (simp only [id_eq]; ring)
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable base t)
  simp only [positiveInverse, intervalIntegral.integral_const, smul_eq_mul]
  rw [show (fun u : ℝ => (u - base) * B) = (fun u => B * (u - base)) by funext u; ring,
    hi]
  ring

theorem le_quadratic_of_greenFilter_le {f : ℝ → ℝ} (hf : Continuous f)
    {base B t : ℝ} (ht : base ≤ t)
    (hB : ∀ u ∈ Icc base t, greenFilter base f u ≤ B) :
    f t ≤ B * (1 + (3 / 2 : ℝ) * (t - base) + (1 / 4 : ℝ) * (t - base) ^ 2) := by
  have h := positiveInverse_mono (continuous_greenFilter hf base) continuous_const ht hB
  simpa only [positiveInverse_greenFilter hf, positiveInverse_const] using h

theorem quadratic_le_of_le_greenFilter {f : ℝ → ℝ} (hf : Continuous f)
    {base B t : ℝ} (ht : base ≤ t)
    (hB : ∀ u ∈ Icc base t, B ≤ greenFilter base f u) :
    B * (1 + (3 / 2 : ℝ) * (t - base) + (1 / 4 : ℝ) * (t - base) ^ 2) ≤ f t := by
  have h := positiveInverse_mono continuous_const (continuous_greenFilter hf base) ht hB
  simpa only [positiveInverse_greenFilter hf, positiveInverse_const] using h

end RHTower.UnitRieszGreenInverse

namespace RHTower

open UnitRieszGreenInverse GaloisForLFunctions.RHTower

def unitRieszSuzukiGreenBoundary (t : ℝ) : ℝ :=
  (-(1 / 2 : ℝ) * suzukiPsi unitRieszSuzukiBase +
      ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase) *
    Real.exp ((unitRieszSuzukiBase - t) / 2) +
  (suzukiPsi unitRieszSuzukiBase - ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase) *
    Real.exp (unitRieszSuzukiBase - t)

def unitRieszSuzukiGreenBoundaryBound : ℝ :=
  |-(1 / 2 : ℝ) * suzukiPsi unitRieszSuzukiBase +
    ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| +
  |suzukiPsi unitRieszSuzukiBase - ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase|

theorem abs_unitRieszSuzukiGreenBoundary_le {t : ℝ} (ht : unitRieszSuzukiBase ≤ t) :
    |unitRieszSuzukiGreenBoundary t| ≤ unitRieszSuzukiGreenBoundaryBound := by
  have hhalf : Real.exp ((unitRieszSuzukiBase - t) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hone : Real.exp (unitRieszSuzukiBase - t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  unfold unitRieszSuzukiGreenBoundary unitRieszSuzukiGreenBoundaryBound
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hhalf)
    (mul_le_of_le_one_right (abs_nonneg _) hone)

theorem integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond (t : ℝ) :
    (∫ u in unitRieszSuzukiBase..t, suzukiPsi u * unitRieszSuzukiReporterSecond t u) =
      (1 / 4 : ℝ) * resolvent (1 / 2) unitRieszSuzukiBase suzukiPsi t -
        resolvent 1 unitRieszSuzukiBase suzukiPsi t := by
  have hc (a : ℝ) : Continuous (fun u => Real.exp (a * (u - t)) * suzukiPsi u) := by
    have hs := continuous_suzukiPsi
    fun_prop
  rw [resolvent_eq_integral, resolvent_eq_integral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hc (1 / 2)).const_mul (1 / 4) |>.intervalIntegrable _ _)
      ((hc 1).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [unitRieszSuzukiReporterSecond, one_mul, show (1 / 2 : ℝ) * (u - t) =
    (u - t) / 2 by ring]
  ring

theorem greenFilter_suzukiPsi_eq {t : ℝ} (ht : unitRieszSuzukiBase ≤ t) :
    greenFilter unitRieszSuzukiBase suzukiPsi t =
      -2 * unitRieszSuzukiGreen t + 2 * unitRieszSuzukiGreenBoundary t := by
  rw [unitRieszSuzukiGreen_eq_raw ht, unitRieszSuzukiReporterDeriv_H,
    integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond]
  unfold greenFilter unitRieszSuzukiGreenBoundary unitRieszSuzukiReporterDeriv
    unitRieszSuzukiReporter
  ring

theorem suzukiPsi_eq_positiveInverse_correctedGreen {t : ℝ}
    (ht : unitRieszSuzukiBase ≤ t) :
    suzukiPsi t = positiveInverse unitRieszSuzukiBase
      (fun u => -2 * unitRieszSuzukiGreen u + 2 * unitRieszSuzukiGreenBoundary u) t := by
  calc
    suzukiPsi t = positiveInverse unitRieszSuzukiBase
        (greenFilter unitRieszSuzukiBase suzukiPsi) t :=
      (positiveInverse_greenFilter continuous_suzukiPsi _ _).symm
    _ = _ := positiveInverse_congr ht (fun u hu => greenFilter_suzukiPsi_eq hu.1)

theorem suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le
    {B t : ℝ} (ht : unitRieszSuzukiBase ≤ t)
    (hB : ∀ u ∈ Icc unitRieszSuzukiBase t, unitRieszSuzukiGreen u ≤ B) :
    -(2 * (B + unitRieszSuzukiGreenBoundaryBound) *
      (1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
        (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2)) ≤ suzukiPsi t := by
  have h := quadratic_le_of_le_greenFilter continuous_suzukiPsi ht
    (B := -(2 * (B + unitRieszSuzukiGreenBoundaryBound))) ?_
  · simpa only [neg_mul] using h
  · intro u hu
    rw [greenFilter_suzukiPsi_eq hu.1]
    have hb := (abs_le.mp (abs_unitRieszSuzukiGreenBoundary_le hu.1)).1
    linarith [hB u hu]

theorem exists_suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le
    {B : ℝ} (hB : ∀ t : ℝ, unitRieszSuzukiBase ≤ t → unitRieszSuzukiGreen t ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → -(C * (1 + t) ^ 2) ≤ suzukiPsi t := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_suzukiPsi.continuousOn (s := Icc (0 : ℝ) unitRieszSuzukiBase))
  let A := max 0 (2 * (B + unitRieszSuzukiGreenBoundaryBound))
  have hA : 0 ≤ A := le_max_left _ _
  have hBA : 2 * (B + unitRieszSuzukiGreenBoundaryBound) ≤ A := le_max_right _ _
  refine ⟨2 * A + |M|, by positivity, fun t ht => ?_⟩
  have hsq : 1 ≤ (1 + t) ^ 2 := by nlinarith [sq_nonneg t]
  by_cases hbt : unitRieszSuzukiBase ≤ t
  · have hl := suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le hbt
      (fun u hu => hB u hu.1)
    have hd : 0 ≤ t - unitRieszSuzukiBase := sub_nonneg.mpr hbt
    have hdt : t - unitRieszSuzukiBase ≤ t := by linarith [unitRieszSuzukiBase_pos]
    have hp0 : 0 ≤ 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
        (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 := by positivity
    have hp : 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
        (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 ≤ 2 * (1 + t) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdt) (add_nonneg ht hd)]
    have h1 := mul_le_mul_of_nonneg_right hBA hp0
    have h2 := mul_le_mul_of_nonneg_left hp hA
    have h3 := mul_nonneg (abs_nonneg M) (sq_nonneg (1 + t))
    nlinarith only [hl, h1, h2, h3]
  · have hm := hM t ⟨ht, le_of_not_ge hbt⟩
    rw [Real.norm_eq_abs] at hm
    have hneg := neg_abs_le (suzukiPsi t)
    have h1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg M)
    have h2 := mul_nonneg hA (sq_nonneg (1 + t))
    nlinarith [le_abs_self M]

theorem UnitRieszGreenInverse.quadratic_le_exponential
    {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (1 + t) ^ 2 ≤ ((rate + 2) ^ 2 / rate ^ 2) * Real.exp (rate * t) := by
  have he : 1 ≤ Real.exp (rate * t / 2) := Real.one_le_exp_iff.mpr (by positivity)
  have he' := Real.add_one_le_exp (rate * t / 2)
  have hlin : rate * (1 + t) ≤ (rate + 2) * Real.exp (rate * t / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left he hr.le]
  have hl0 : 0 ≤ rate * (1 + t) := by positivity
  have hs : (rate * (1 + t)) ^ 2 ≤ ((rate + 2) * Real.exp (rate * t / 2)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlin)
      (show 0 ≤ (rate + 2) * Real.exp (rate * t / 2) + rate * (1 + t) by positivity)]
  have hexp : Real.exp (rate * t / 2) ^ 2 = Real.exp (rate * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, hexp] at hs
  rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hr)]
  nlinarith only [hs]

theorem riemannHypothesis_of_unitRieszSuzukiGreen_boundedAbove
    {B : ℝ} (hB : ∀ t : ℝ, unitRieszSuzukiBase ≤ t → unitRieszSuzukiGreen t ≤ B) :
    RiemannHypothesis := by
  obtain ⟨C, hC, hlow⟩ := exists_suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le hB
  apply riemannHypothesis_of_suzukiPsiSubexponentialBelow
  intro rate hr
  refine ⟨C * ((rate + 2) ^ 2 / rate ^ 2), fun t ht => ?_⟩
  have h := mul_le_mul_of_nonneg_left (quadratic_le_exponential hr ht) hC
  nlinarith only [h, hlow t ht]

theorem riemannHypothesis_iff_unitRieszSuzukiGreen_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ t : ℝ,
      unitRieszSuzukiBase ≤ t → unitRieszSuzukiGreen t ≤ B := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := riemannHypothesis_iff_suzukiExplicitScrewBounded.mp hRH
    have hC0 : 0 ≤ C := (abs_nonneg (suzukiPsi 0)).trans (hC 0 le_rfl)
    refine ⟨4 * C + 2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase|, fun t ht => ?_⟩
    exact (le_abs_self _).trans (abs_unitRieszSuzukiGreen_le_of_suzuki_bound hC0 hC ht)
  · rintro ⟨B, hB⟩
    exact riemannHypothesis_of_unitRieszSuzukiGreen_boundedAbove hB

end RHTower
