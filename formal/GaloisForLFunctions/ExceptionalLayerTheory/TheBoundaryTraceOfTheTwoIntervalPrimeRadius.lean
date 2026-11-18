import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorKeepsItsBoundaryTrace
import GaloisForLFunctions.ZeroConfigurationGeometry.TwoIntervalAmplitudeAliasingAndCoprimeRealization
import Mathlib.NumberTheory.Chebyshev

/-!
# The ordinary-prime radius on the extremal zero line

After division by the extremal power, the two adjacent ordinary-prime increments
track two translates of the same boundary trace. Almost periodicity turns a limiting
radius into an exact circle identity on the entire real line.
-/

noncomputable section
open Complex Filter Topology RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The ordinary-prime error in logarithmic coordinates. -/
def thetaLogError (t : ℝ) : ℝ := Chebyshev.theta (Real.exp t) - Real.exp t

/-- Discrepancy of the ordinary-prime radius from the trial quartet amplitude. -/
def thetaRadialDiscrepancy (β γ : ℝ) (m : ℕ) : ℝ → ℝ :=
  radialDiscrepancyOf thetaLogError β γ m

/-- A step in a trace from which the exponential growth has been removed. -/
def boundaryStep (β h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (β * h) * f (t + h) - f t

private def stepPair (β h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ⟨boundaryStep β h f t, boundaryStep β h f (t + h)⟩

private def normalizedTheta (β t : ℝ) := thetaLogError t / Real.exp (β * t)

private theorem normalizedTheta_sub_trace (hΘ : 1 / 2 < zetaZeroAbscissa) :
    Tendsto (fun t => normalizedTheta zetaZeroAbscissa t -
      primeErrorBoundaryTrace zetaZeroAbscissa t) atTop (𝓝 0) := by
  let β := zetaZeroAbscissa
  obtain ⟨L, hL⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hp := (tendsto_normalized_primeError_sub_boundary hΘ).comp Real.tendsto_exp_atTop
  simp only [Function.comp_def, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hp
  have hpow : Tendsto (fun t : ℝ => L * Real.exp (-(β - 1 / 2) * t)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (β - 1/2)
      (sub_pos.mpr hΘ)).const_mul L
  have hdiff : Tendsto (fun t => (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)) /
      Real.exp (β * t)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hpow
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    have hb := hL (Real.exp t)
    rw [← Real.exp_half] at hb
    calc _ ≤ L * Real.exp (t / 2) / Real.exp (β * t) :=
              div_le_div_of_nonneg_right hb (Real.exp_pos _).le
      _ = _ := by rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring
  have h := hp.sub hdiff
  rw [sub_zero] at h
  apply h.congr
  intro t
  dsimp only [normalizedTheta, thetaLogError, β]
  rw [mul_comm t zetaZeroAbscissa]
  ring

private theorem normalizedRadius_eq (β h t : ℝ) :
    twoIntervalRadius thetaLogError h (Real.exp (β * h)) t / Real.exp (β * t) =
      ‖stepPair β h (normalizedTheta β) t‖ := by
  rw [twoIntervalRadius_eq_complex_norm (Real.exp_pos _)]
  have hs (s : ℝ) : boundaryStep β h (normalizedTheta β) s =
      logStepIncrement thetaLogError s h / Real.exp (β * s) := by
    simp only [boundaryStep, normalizedTheta, logStepIncrement, mul_add, Real.exp_add]
    field_simp <;> ring
  have hz : stepPair β h (normalizedTheta β) t =
      ((⟨logStepIncrement thetaLogError t h,
        logStepIncrement thetaLogError (t+h) h / Real.exp (β*h)⟩ : ℂ) /
        (Real.exp (β*t) : ℂ)) := by
    apply Complex.ext
    · simp [stepPair, hs, Complex.div_ofReal_re]
    · simp only [stepPair, hs, Complex.div_ofReal_im, mul_add, Real.exp_add]
      ring
  rw [hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private theorem stepPair_sub_tendsto_zero {f g : ℝ → ℝ}
    (hf : Tendsto (fun t => f t - g t) atTop (𝓝 0)) (β h : ℝ) :
    Tendsto (fun t => stepPair β h f t - stepPair β h g t) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t + h) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hs : Tendsto (fun t => boundaryStep β h f t - boundaryStep β h g t) atTop (𝓝 0) := by
    have hd := ((hf.comp ht).const_mul (Real.exp (β*h))).sub hf
    simp only [mul_zero, sub_zero, Function.comp_def] at hd
    exact hd.congr fun t => by dsimp only [boundaryStep]; ring
  have hpair := hs.norm.add (hs.comp ht).norm
  simp only [norm_zero, zero_add] at hpair
  exact squeeze_zero_norm' (.of_forall fun t => Complex.norm_le_abs_re_add_abs_im _) hpair

/-- The normalized radius tracks the Euclidean norm of two consecutive
increments of the actual extremal trace, including an infinite extremal layer. -/
theorem tendsto_normalizedThetaRadius_sub_boundary (hΘ : 1 / 2 < zetaZeroAbscissa) (h : ℝ) :
    Tendsto (fun t => twoIntervalRadius thetaLogError h (Real.exp (zetaZeroAbscissa*h)) t /
      Real.exp (zetaZeroAbscissa*t) -
      ‖(⟨boundaryStep zetaZeroAbscissa h (primeErrorBoundaryTrace zetaZeroAbscissa) t,
          boundaryStep zetaZeroAbscissa h (primeErrorBoundaryTrace zetaZeroAbscissa) (t+h)⟩ : ℂ)‖)
      atTop (𝓝 0) := by
  simp only [normalizedRadius_eq]
  have hd := (stepPair_sub_tendsto_zero (normalizedTheta_sub_trace hΘ) zetaZeroAbscissa h).norm
  rw [norm_zero] at hd
  exact squeeze_zero_norm' (.of_forall fun t => abs_norm_sub_norm_le _ _) hd

private theorem normalizedDiscrepancy_tendsto_zero {g : ℝ → ℝ} {β : ℝ} (hβ : 1/2 < β)
    (hb : ¬ IsLogSqrtSqUnbounded g) :
    Tendsto (fun t => g t / Real.exp (β*t)) atTop (𝓝 0) := by
  rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hb
  obtain ⟨K,T,hK⟩ := hb
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (β-1/2)
    (sub_pos.mpr hβ)).const_mul (4*|K|)
  rw [mul_zero] at hd
  apply squeeze_zero_norm' _ hd
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1:ℝ)] with t ht ht1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), Real.rpow_two]
  have hp : (1+t)^2 ≤ 4*t^2 := by nlinarith only [ht1, sq_nonneg (t-1)]
  have hk := (hK t ht).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
  calc _ ≤ (|K| * Real.exp (t/2) * (4*t^2)) / Real.exp (β*t) :=
          div_le_div_of_nonneg_right (hk.trans (mul_le_mul_of_nonneg_left hp (by positivity))) (Real.exp_pos _).le
    _ = _ := by
      rw [show -(β-1/2)*t = t/2-β*t by ring, Real.exp_sub]
      ring

private theorem almostPeriodic_pairNorm_sub {f : ℝ → ℝ}
    (hf : _root_.HTGeometry.IsBohrAlmostPeriodic f) (β h C : ℝ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (fun t => ‖stepPair β h f t‖ - C) := by
  intro ε hε
  let A := Real.exp (β*h)
  let δ := ε / (2*(A+1))
  have hA : 0 < A := Real.exp_pos _
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨L,hL,hshift⟩ := hf δ hδ
  refine ⟨L,hL,fun a => ?_⟩
  obtain ⟨τ,hτ,hu⟩ := hshift a
  refine ⟨τ,hτ,fun t => ?_⟩
  have hstep (s : ℝ) : |boundaryStep β h f (s+τ) - boundaryStep β h f s| ≤ (A+1)*δ := by
    have e : boundaryStep β h f (s+τ) - boundaryStep β h f s =
        A*(f ((s+h)+τ)-f (s+h)) - (f (s+τ)-f s) := by
      dsimp only [boundaryStep, A]; rw [add_right_comm s τ h]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hA, add_mul, one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hu (s+h)) hA.le) (hu s)
  change |(‖stepPair β h f (t+τ)‖-C) - (‖stepPair β h f t‖-C)| ≤ ε
  rw [show (‖stepPair β h f (t+τ)‖-C) - (‖stepPair β h f t‖-C) =
    ‖stepPair β h f (t+τ)‖ - ‖stepPair β h f t‖ by ring]
  refine (abs_norm_sub_norm_le _ _).trans ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
  change |boundaryStep β h f (t+τ) - boundaryStep β h f t| +
      |boundaryStep β h f (t+τ+h) - boundaryStep β h f (t+h)| ≤ ε
  rw [add_right_comm t τ h]
  refine (add_le_add (hstep t) (hstep (t+h))).trans_eq ?_
  dsimp only [δ]
  field_simp
  ring

/-- A bounded discrepancy at the extremal exponent forces every point of the
two-increment boundary trace onto the trial circle. -/
theorem boundaryStep_circle_of_bounded_thetaRadial {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    let h := quarterPeriodStep γ
    let D := boundaryStep zetaZeroAbscissa h (primeErrorBoundaryTrace zetaZeroAbscissa)
    ∀ t : ℝ, D t ^ 2 + D (t+h) ^ 2 = quartetRadialCoeff zetaZeroAbscissa γ m ^ 2 := by
  intro h D
  let β := zetaZeroAbscissa
  let F := primeErrorBoundaryTrace β
  let C := quartetRadialCoeff β γ m
  have hlim := (normalizedDiscrepancy_tendsto_zero hΘ hb).sub
    (tendsto_normalizedThetaRadius_sub_boundary hΘ h)
  rw [sub_zero] at hlim
  have hlim' : Tendsto (fun t => ‖stepPair β h F t‖ - C) atTop (𝓝 0) := by
    apply hlim.congr
    intro t
    change (_ - C * Real.exp (β*t)) / Real.exp (β*t) -
      (twoIntervalRadius thetaLogError h (Real.exp (β*h)) t / Real.exp (β*t) -
        ‖stepPair β h F t‖) = _
    rw [sub_div, mul_div_cancel_right₀ _ (Real.exp_pos _).ne']
    ring
  have hnorm := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
    (almostPeriodic_pairNorm_sub (isBohrAlmostPeriodic_primeErrorBoundaryTrace hΘ) β h C) hlim'
  intro t
  have hs := congrArg (fun r : ℝ => r^2) (sub_eq_zero.mp (hnorm t))
  simpa only [Complex.sq_norm, stepPair, Complex.normSq_mk, sq] using hs

/-- If the extremal line is empty, the normalized ordinary-prime discrepancy
converges to the negative trial radius. Zeros may approach the line from the left. -/
theorem tendsto_thetaRadial_div_exp_of_unattained {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hempty : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ zetaZeroAbscissa) :
    Tendsto (fun t => thetaRadialDiscrepancy zetaZeroAbscissa γ m t /
      Real.exp (zetaZeroAbscissa*t)) atTop (𝓝 (-quartetRadialCoeff zetaZeroAbscissa γ m)) := by
  have hr := tendsto_normalizedThetaRadius_sub_boundary hΘ (quarterPeriodStep γ)
  simp only [boundaryStep, primeErrorBoundaryTrace_eq_zero_of_empty hempty, mul_zero, sub_zero,
    show (⟨0, 0⟩ : ℂ) = 0 from rfl, norm_zero] at hr
  have hd := hr.sub_const (quartetRadialCoeff zetaZeroAbscissa γ m)
  rw [zero_sub] at hd
  apply hd.congr
  intro t
  simp only [thetaRadialDiscrepancy, radialDiscrepancyOf, quarterPeriodScale, sub_div,
    mul_div_cancel_right₀ _ (Real.exp_pos _).ne']

/-- At an unattained extremal abscissa above one half, every positive trial
multiplicity and every nonzero trial ordinate satisfy ordinary-prime radial exclusion. -/
theorem thetaRadial_unbounded_of_unattained {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hempty : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ zetaZeroAbscissa)
    (hγ : γ ≠ 0) (hm : 1 ≤ m) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m) := by
  by_contra hb
  have he := tendsto_nhds_unique (tendsto_thetaRadial_div_exp_of_unattained (γ := γ) (m := m) hΘ hempty)
    (normalizedDiscrepancy_tendsto_zero hΘ hb)
  exact (neg_lt_zero.mpr (quartetRadialCoeff_pos hγ hm)).ne he

#print axioms tendsto_normalizedThetaRadius_sub_boundary
#print axioms boundaryStep_circle_of_bounded_thetaRadial
#print axioms tendsto_thetaRadial_div_exp_of_unattained
#print axioms thetaRadial_unbounded_of_unattained

end GaloisForLFunctions.ExceptionalLayerTheory
