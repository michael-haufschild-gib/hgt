import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartNeutralHeightTransversality
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Global selectivity no-go for the reflected bi-heat theta finite part

The canonical off-wall imaginary finite-part channel is an absolutely
convergent sine spectrum.  A sharp exponent-direction divided-difference
estimate makes its amplitudes summable, so the channel is Bohr almost
periodic.  Neutral-height transversality makes it nonzero; oddness and Bohr
recurrence then force both strict signs above every threshold.  Continuity
forces a zero between successive opposite signs.

Therefore local off-wall orientation cannot extend to a global one-sign or
global nonvanishing theorem.  The strongest survivor is exact: the canonical
channel has positive values, negative values, and zeros cofinally in positive
height.  Any RBH proof route must separate actual Xi heights from this
recurrent zero set rather than attempt global analytic sign propagation.
-/

open Complex Filter Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Height-independent coefficient of one paired sine atom. -/
def reflectedBiHeatFinitePartMixedPhaseAmplitude
    (sigma x : ℝ) (p : ℕ × ℕ) : ℝ :=
  let d := (p.1 : ℝ) + 1
  let N := (p.2 : ℝ) + 1
  let r := (N + d) / N
  heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma))

/-- Logarithmic frequency of one paired sine atom. -/
def reflectedBiHeatFinitePartMixedPhaseFrequency
    (p : ℕ × ℕ) : ℝ :=
  let d := (p.1 : ℝ) + 1
  let N := (p.2 : ℝ) + 1
  Real.log ((N + d) / N)

/-- The phase amplitude has a summable Gaussian/inverse-square majorant. -/
theorem abs_reflectedBiHeatFinitePartMixedPhaseAmplitude_le
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (p : ℕ × ℕ) :
    |reflectedBiHeatFinitePartMixedPhaseAmplitude sigma P.x p| ≤
      reflectedBiHeatFinitePartMixedSlopeMajorant P p := by
  let d : ℝ := (p.1 : ℝ) + 1
  let N : ℝ := (p.2 : ℝ) + 1
  let r : ℝ := (N + d) / N
  have hd : 0 < d := by dsimp [d]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 1 < r := by
    dsimp [r]
    rw [lt_div_iff₀ hN]
    linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr.le
  have hlog : Real.log r ≤ d / N := by
    calc
      Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hr)
      _ = d / N := by
        dsimp [r]
        field_simp
        ring
  have hargLeft : (sigma - 1) * Real.log r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog0
  have hargRight : -sigma * Real.log r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog0
  have hdiffExp :=
    GaloisForLFunctions.HTGeometry.abs_exp_sub_exp_le_of_nonpos
      hargLeft hargRight
  have hpowExpLeft : r ^ (sigma - 1) =
      Real.exp ((sigma - 1) * Real.log r) := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hr)]
    congr 1
    ring
  have hpowExpRight : r ^ (-sigma) =
      Real.exp (-sigma * Real.log r) := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hr)]
    congr 1
    ring
  have hcenter : |2 * sigma - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hdiff : |r ^ (sigma - 1) - r ^ (-sigma)| ≤ Real.log r := by
    rw [hpowExpLeft, hpowExpRight]
    refine le_trans hdiffExp ?_
    rw [show (sigma - 1) * Real.log r - -sigma * Real.log r =
      (2 * sigma - 1) * Real.log r by ring, abs_mul,
      abs_of_nonneg hlog0]
    exact mul_le_of_le_one_left hlog0 hcenter
  rw [reflectedBiHeatFinitePartMixedPhaseAmplitude,
    reflectedBiHeatFinitePartMixedSlopeMajorant]
  change |heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) *
      (r ^ (sigma - 1) - r ^ (-sigma))| ≤
    2 * (d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2)))
  rw [abs_mul, abs_mul, abs_of_pos (heatCoeff_pos P.x _),
    abs_of_pos (one_div_pos.mpr hN)]
  have hfront0 : 0 ≤ heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) :=
    mul_nonneg (heatCoeff_pos P.x _).le (one_div_pos.mpr hN).le
  calc
    heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) *
          |r ^ (sigma - 1) - r ^ (-sigma)| ≤
        heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) * Real.log r := by
      exact mul_le_mul_of_nonneg_left hdiff hfront0
    _ ≤ heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) * (d / N) := by
      exact mul_le_mul_of_nonneg_left hlog hfront0
    _ ≤ 2 * (d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2))) := by
      have hbase0 : 0 ≤ d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2)) := by
        exact mul_nonneg hd.le (mul_nonneg (heatCoeff_pos P.x _).le
          (one_div_nonneg.mpr (sq_nonneg N)))
      have heq : heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) * (d / N) =
          d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2)) := by
        field_simp
      rw [heq]
      linarith

theorem summable_abs_reflectedBiHeatFinitePartMixedPhaseAmplitude
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    Summable (fun p : ℕ × ℕ =>
      |reflectedBiHeatFinitePartMixedPhaseAmplitude sigma P.x p|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun p => abs_reflectedBiHeatFinitePartMixedPhaseAmplitude_le
      P hsigma0 hsigma1 p)
  exact summable_reflectedBiHeatFinitePartMixedSlopeMajorant P

theorem reflectedBiHeatFinitePartMixedPhaseAtom_eq_amplitude_mul_sin
    (sigma x gamma : ℝ) (p : ℕ × ℕ) :
    reflectedBiHeatFinitePartMixedPhaseAtom sigma x gamma p =
      reflectedBiHeatFinitePartMixedPhaseAmplitude sigma x p *
        Real.sin (reflectedBiHeatFinitePartMixedPhaseFrequency p * gamma) := by
  rw [reflectedBiHeatFinitePartMixedPhaseAtom,
    reflectedBiHeatFinitePartMixedPhaseAmplitude,
    reflectedBiHeatFinitePartMixedPhaseFrequency]
  ring_nf

/-- Complex exponential carrier whose imaginary part is the paired phase. -/
def reflectedBiHeatFinitePartMixedPhaseCarrier
    (sigma : ℝ) (P : ReflectedBiHeatDatum) (gamma : ℝ) : ℂ :=
  GaloisForLFunctions.expSeriesCarrier
    (fun p : ℕ × ℕ =>
      ((reflectedBiHeatFinitePartMixedPhaseAmplitude sigma P.x p : ℝ) : ℂ))
    reflectedBiHeatFinitePartMixedPhaseFrequency gamma

theorem summable_norm_reflectedBiHeatFinitePartMixedPhaseAmplitude
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖((reflectedBiHeatFinitePartMixedPhaseAmplitude sigma P.x p : ℝ) : ℂ)‖) := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using
    summable_abs_reflectedBiHeatFinitePartMixedPhaseAmplitude
      P hsigma0 hsigma1

theorem expChar_im (omega gamma : ℝ) :
    (GaloisForLFunctions.expChar omega gamma).im =
      Real.sin (omega * gamma) := by
  rw [GaloisForLFunctions.expChar, Complex.exp_im]
  simp

theorem reflectedBiHeatFinitePartMixedPhaseCarrier_im
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (reflectedBiHeatFinitePartMixedPhaseCarrier sigma P gamma).im =
      reflectedBiHeatFinitePartMixedPhase sigma gamma P := by
  have ha := summable_norm_reflectedBiHeatFinitePartMixedPhaseAmplitude
    P hsigma0 hsigma1
  have hs := GaloisForLFunctions.summable_expSeries ha
    reflectedBiHeatFinitePartMixedPhaseFrequency gamma
  rw [reflectedBiHeatFinitePartMixedPhaseCarrier,
    GaloisForLFunctions.expSeriesCarrier, Complex.im_tsum hs,
    reflectedBiHeatFinitePartMixedPhase]
  apply tsum_congr
  intro p
  rw [reflectedBiHeatFinitePartMixedPhaseAtom_eq_amplitude_mul_sin,
    mul_im, expChar_im]
  simp

theorem isBohrAlmostPeriodic_im {f : ℝ → ℂ}
    (hap : HTGeometry.IsBohrAlmostPeriodic f) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => (f t).im) := by
  intro epsilon hepsilon
  obtain ⟨L, hL, hdense⟩ := hap epsilon hepsilon
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨tau, htaumem, htau⟩ := hdense a
  refine ⟨tau, htaumem, fun x => ?_⟩
  have hx := htau x
  rw [Real.norm_eq_abs]
  calc
    |(f (x + tau)).im - (f x).im| =
        |(f (x + tau) - f x).im| := by simp
    _ ≤ ‖f (x + tau) - f x‖ := Complex.abs_im_le_norm _
    _ ≤ epsilon := hx

theorem isBohrAlmostPeriodic_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    HTGeometry.IsBohrAlmostPeriodic
      (fun gamma => reflectedBiHeatFinitePartMixedPhase sigma gamma P) := by
  have ha := summable_norm_reflectedBiHeatFinitePartMixedPhaseAmplitude
    P hsigma0 hsigma1
  have hap := GaloisForLFunctions.isBohrAlmostPeriodic_expSeriesCarrier
    ha reflectedBiHeatFinitePartMixedPhaseFrequency
  have him := isBohrAlmostPeriodic_im hap
  convert him using 1
  funext gamma
  exact (reflectedBiHeatFinitePartMixedPhaseCarrier_im
    P sigma gamma hsigma0 hsigma1).symm

theorem continuous_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    Continuous (fun gamma =>
      reflectedBiHeatFinitePartMixedPhase sigma gamma P) := by
  have ha := summable_norm_reflectedBiHeatFinitePartMixedPhaseAmplitude
    P hsigma0 hsigma1
  have hc := GaloisForLFunctions.continuous_expSeriesCarrier ha
    reflectedBiHeatFinitePartMixedPhaseFrequency
  have him : Continuous (fun gamma =>
      (reflectedBiHeatFinitePartMixedPhaseCarrier sigma P gamma).im) :=
    Complex.continuous_im.comp hc
  convert him using 1
  funext gamma
  exact (reflectedBiHeatFinitePartMixedPhaseCarrier_im
    P sigma gamma hsigma0 hsigma1).symm

theorem reflectedBiHeatFinitePartMixedPhase_neg
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ) :
    reflectedBiHeatFinitePartMixedPhase sigma (-gamma) P =
      -reflectedBiHeatFinitePartMixedPhase sigma gamma P := by
  rw [reflectedBiHeatFinitePartMixedPhase,
    reflectedBiHeatFinitePartMixedPhase, ← tsum_neg]
  apply tsum_congr
  intro p
  rw [reflectedBiHeatFinitePartMixedPhaseAtom_eq_amplitude_mul_sin,
    reflectedBiHeatFinitePartMixedPhaseAtom_eq_amplitude_mul_sin]
  rw [show reflectedBiHeatFinitePartMixedPhaseFrequency p * -gamma =
    -(reflectedBiHeatFinitePartMixedPhaseFrequency p * gamma) by ring,
    Real.sin_neg]
  ring

theorem exists_pos_of_odd {f : ℝ → ℝ}
    (hodd : ∀ t, f (-t) = -f t) {t0 : ℝ} (hne : f t0 ≠ 0) :
    ∃ t, 0 < f t := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨-t0, ?_⟩
    rw [hodd]
    linarith
  · exact ⟨t0, hpos⟩

theorem cofinal_pos_of_isBohrAlmostPeriodic
    {f : ℝ → ℝ} (hap : HTGeometry.IsBohrAlmostPeriodic f)
    {t0 : ℝ} (hpos : 0 < f t0) (T : ℝ) :
    ∃ t, T < t ∧ 0 < f t := by
  obtain ⟨L, hL, hdense⟩ := hap (f t0 / 2) (by positivity)
  obtain ⟨tau, htaumem, htau⟩ := hdense (T - t0 + 1)
  refine ⟨t0 + tau, ?_, ?_⟩
  · linarith [htaumem.1]
  · have hclose := htau t0
    rw [Real.norm_eq_abs] at hclose
    have hlower := (abs_le.mp hclose).1
    linarith

theorem cofinal_neg_of_isBohrAlmostPeriodic
    {f : ℝ → ℝ} (hap : HTGeometry.IsBohrAlmostPeriodic f)
    {t0 : ℝ} (hneg : f t0 < 0) (T : ℝ) :
    ∃ t, T < t ∧ f t < 0 := by
  obtain ⟨L, hL, hdense⟩ := hap (-f t0 / 2) (by linarith)
  obtain ⟨tau, htaumem, htau⟩ := hdense (T - t0 + 1)
  refine ⟨t0 + tau, ?_, ?_⟩
  · linarith [htaumem.1]
  · have hclose := htau t0
    rw [Real.norm_eq_abs] at hclose
    have hupper := (abs_le.mp hclose).2
    linarith

/-- A nonzero odd Bohr almost-periodic real function takes both strict signs
above every threshold. -/
theorem cofinal_both_signs_of_odd_isBohrAlmostPeriodic
    {f : ℝ → ℝ} (hap : HTGeometry.IsBohrAlmostPeriodic f)
    (hodd : ∀ t, f (-t) = -f t) {t0 : ℝ} (hne : f t0 ≠ 0)
    (T : ℝ) :
    (∃ t, T < t ∧ 0 < f t) ∧ (∃ t, T < t ∧ f t < 0) := by
  obtain ⟨s, hspos⟩ := exists_pos_of_odd hodd hne
  have hsneg : f (-s) < 0 := by
    rw [hodd]
    linarith
  exact ⟨cofinal_pos_of_isBohrAlmostPeriodic hap hspos T,
    cofinal_neg_of_isBohrAlmostPeriodic hap hsneg T⟩

/-- A continuous nonzero odd Bohr almost-periodic real function has a zero
above every threshold. -/
theorem cofinal_zero_of_continuous_odd_isBohrAlmostPeriodic
    {f : ℝ → ℝ} (hcont : Continuous f)
    (hap : HTGeometry.IsBohrAlmostPeriodic f)
    (hodd : ∀ t, f (-t) = -f t) {t0 : ℝ} (hne : f t0 ≠ 0)
    (T : ℝ) :
    ∃ t, T < t ∧ f t = 0 := by
  obtain ⟨hpos, hneg⟩ :=
    cofinal_both_signs_of_odd_isBohrAlmostPeriodic hap hodd hne T
  obtain ⟨a, hTa, haneg⟩ := hneg
  obtain ⟨b, hab, hbpos⟩ :=
    cofinal_pos_of_isBohrAlmostPeriodic hap
      (exists_pos_of_odd hodd hne).choose_spec a
  have hiv := intermediate_value_Icc hab.le hcont.continuousOn
  obtain ⟨t, htmem, htzero⟩ := hiv ⟨haneg.le, hbpos.le⟩
  exact ⟨t, lt_of_lt_of_le hTa htmem.1, htzero⟩

theorem exists_ne_zero_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) :
    ∃ gamma, reflectedBiHeatFinitePartMixedPhase sigma gamma P ≠ 0 := by
  by_contra hnone
  have hnone' : ∀ gamma,
      ¬ reflectedBiHeatFinitePartMixedPhase sigma gamma P ≠ 0 :=
    not_exists.mp hnone
  have hfun : (fun gamma =>
      reflectedBiHeatFinitePartMixedPhase sigma gamma P) =
      (fun _gamma : ℝ => 0) := by
    funext gamma
    exact not_ne_iff.mp (hnone' gamma)
  have hderiv := hasDerivAt_reflectedBiHeatFinitePartMixedPhase_zero
    P sigma hsigma0 hsigma1
  rw [hfun] at hderiv
  have hzero : HasDerivAt (fun _gamma : ℝ => (0 : ℝ)) 0 0 :=
    hasDerivAt_const 0 0
  have hslopeZero : reflectedBiHeatFinitePartMixedSlope sigma P = 0 :=
    hderiv.unique hzero
  exact hoffWall ((reflectedBiHeatFinitePartMixedSlope_eq_zero_iff
    P hsigma0 hsigma1).1 hslopeZero)

theorem cofinal_both_signs_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) (T : ℝ) :
    (∃ gamma, T < gamma ∧
      0 < reflectedBiHeatFinitePartMixedPhase sigma gamma P) ∧
    (∃ gamma, T < gamma ∧
      reflectedBiHeatFinitePartMixedPhase sigma gamma P < 0) := by
  obtain ⟨gamma0, hgamma0⟩ :=
    exists_ne_zero_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1 hoffWall
  exact cofinal_both_signs_of_odd_isBohrAlmostPeriodic
    (isBohrAlmostPeriodic_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1)
    (reflectedBiHeatFinitePartMixedPhase_neg P sigma) hgamma0 T

theorem cofinal_zero_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) (T : ℝ) :
    ∃ gamma, T < gamma ∧
      reflectedBiHeatFinitePartMixedPhase sigma gamma P = 0 := by
  obtain ⟨gamma0, hgamma0⟩ :=
    exists_ne_zero_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1 hoffWall
  exact cofinal_zero_of_continuous_odd_isBohrAlmostPeriodic
    (continuous_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1)
    (isBohrAlmostPeriodic_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1)
    (reflectedBiHeatFinitePartMixedPhase_neg P sigma) hgamma0 T

/-- **Cofinal-zero survivor.**  Every off-wall canonical finite-part imaginary
channel has zeros above every real height threshold. -/
theorem cofinal_zero_reflectedBiHeatFinitePart_vertical_im
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) (T : ℝ) :
    ∃ gamma, T < gamma ∧
      (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im = 0 := by
  obtain ⟨gamma, hTgamma, hzero⟩ :=
    cofinal_zero_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1 hoffWall T
  refine ⟨gamma, hTgamma, ?_⟩
  rw [reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase]
  exact hzero

/-- Every off-wall canonical finite-part imaginary channel takes both strict
signs above every real height threshold. -/
theorem cofinal_both_signs_reflectedBiHeatFinitePart_vertical_im
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) (T : ℝ) :
    (∃ gamma, T < gamma ∧
      0 < (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im) ∧
    (∃ gamma, T < gamma ∧
      (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im < 0) := by
  obtain ⟨hpos, hneg⟩ :=
    cofinal_both_signs_reflectedBiHeatFinitePartMixedPhase
      P sigma hsigma0 hsigma1 hoffWall T
  constructor
  · obtain ⟨gamma, hTgamma, hgamma⟩ := hpos
    refine ⟨gamma, hTgamma, ?_⟩
    rw [reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase]
    exact hgamma
  · obtain ⟨gamma, hTgamma, hgamma⟩ := hneg
    refine ⟨gamma, hTgamma, ?_⟩
    rw [reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase]
    exact hgamma

/-- Global positive-height nonvanishing of the canonical odd channel is
impossible off the critical wall. -/
theorem not_global_nonvanishing_reflectedBiHeatFinitePart_vertical_im
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) :
    ¬ ∀ gamma, 0 < gamma →
      (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im ≠ 0 := by
  intro hglobal
  obtain ⟨gamma, hgamma, hzero⟩ :=
    cofinal_zero_reflectedBiHeatFinitePart_vertical_im
      P sigma hsigma0 hsigma1 hoffWall 0
  exact hglobal gamma hgamma hzero

end RHTower
