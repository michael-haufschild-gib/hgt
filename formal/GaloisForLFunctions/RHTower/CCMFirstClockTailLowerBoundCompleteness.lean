import GaloisForLFunctions.RHTower.CCMFirstClockVolterraReflection
import GaloisForLFunctions.RHTower.PerronLaplaceKernel
import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow

/-!
# Tail lower-bound completeness of the literal first CCM clock

This module strengthens first-clock sign completeness.  A fixed lower bound on the published
first clock on any aperture tail already implies RH.  The proof replaces the signed first-clock
divisor by a nonnegative carrier using one affine tail term and one compact floor correction,
then runs the existing branch-free continuous Landau descent.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The literal first published CCM clock is bounded below on some physical aperture tail. -/
def CCMFirstClockPublishedSourceEventuallyBoundedBelow : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ Real.pi / 2 ≤ A ∧
    ∀ L : ℝ, A ≤ L →
      -C ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L)

/-- The source lower bound becomes an affine lower bound for the exact Xi rational divisor. -/
theorem ccmFirstClockXiRationalDivisor_re_add_half_mul_nonneg_of_source_lowerBound
    {C A : ℝ} (hC : 0 ≤ C) (hA : Real.pi / 2 ≤ A)
    (hsource : ∀ L : ℝ, A ≤ L →
      -C ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L))
    {L : ℝ} (hL : A ≤ L) :
    0 ≤ (ccmFirstClockXiRationalDivisor L).re + (C / 2) * L := by
  have hphysical : Real.pi / 2 ≤ L := hA.trans hL
  have h := hsource L hL
  rw [ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor
    hphysical] at h
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hphysical
  have hscale : 0 < 2 / L := by positivity
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ L / 2)
  have hmul' : (L / 2) * (-C) ≤
      (ccmFirstClockXiRationalDivisor L).re := by
    calc
      (L / 2) * (-C) ≤
          (L / 2) * ((2 / L) * (ccmFirstClockXiRationalDivisor L).re) := hmul
      _ = (ccmFirstClockXiRationalDivisor L).re := by
        field_simp [hLpos.ne']
  nlinarith

/-- Negative part inserted only on the compact interval `(pi/2,A]`. -/
def ccmFirstClockTailFloorCorrection (d A L : ℝ) : ℝ :=
  (Ioc (Real.pi / 2) A).indicator
    (fun x : ℝ => max (-((ccmFirstClockXiRationalDivisor x).re + d * x)) 0) L

/-- Affine-plus-compact corrected real first-clock carrier. -/
def ccmFirstClockTailFloorCarrier (d A L : ℝ) : ℝ :=
  (ccmFirstClockXiRationalDivisor L).re + d * L +
    ccmFirstClockTailFloorCorrection d A L

theorem measurable_ccmFirstClockTailFloorCorrection (d A : ℝ) :
    Measurable (ccmFirstClockTailFloorCorrection d A) := by
  unfold ccmFirstClockTailFloorCorrection
  exact ((measurable_ccmFirstClockXiRationalDivisor.re.add
    (measurable_const.mul measurable_id)).neg.max measurable_const)
      |>.indicator measurableSet_Ioc

theorem measurable_ccmFirstClockTailFloorCarrier (d A : ℝ) :
    Measurable (ccmFirstClockTailFloorCarrier d A) := by
  unfold ccmFirstClockTailFloorCarrier
  exact (measurable_ccmFirstClockXiRationalDivisor.re.add
    (measurable_const.mul measurable_id)).add
      (measurable_ccmFirstClockTailFloorCorrection d A)

/-- Compact flooring plus a valid affine tail bound makes the corrected carrier nonnegative. -/
theorem ccmFirstClockTailFloorCarrier_nonneg
    {d A : ℝ}
    (htail : ∀ L : ℝ, A ≤ L →
      0 ≤ (ccmFirstClockXiRationalDivisor L).re + d * L)
    {L : ℝ} (hL : Real.pi / 2 < L) :
    0 ≤ ccmFirstClockTailFloorCarrier d A L := by
  by_cases hLA : L ≤ A
  · have hmem : L ∈ Ioc (Real.pi / 2) A := ⟨hL, hLA⟩
    rw [ccmFirstClockTailFloorCarrier, ccmFirstClockTailFloorCorrection,
      Set.indicator_of_mem hmem]
    by_cases hx : 0 ≤ (ccmFirstClockXiRationalDivisor L).re + d * L
    · rw [max_eq_right]
      · simpa using hx
      · linarith
    · rw [max_eq_left]
      · ring_nf
        exact le_rfl
      · linarith
  · rw [ccmFirstClockTailFloorCarrier, ccmFirstClockTailFloorCorrection,
      Set.indicator_of_notMem]
    · simpa using htail L (le_of_not_ge hLA)
    · exact fun hmem => hLA hmem.2

/-- Local integrability of the complete first-clock divisor on the compact correction interval. -/
theorem integrableOn_ccmFirstClockXiRationalDivisor_floorInterval
    {A : ℝ} (hA : Real.pi / 2 ≤ A) :
    IntegrableOn ccmFirstClockXiRationalDivisor (Ioc (Real.pi / 2) A) := by
  let B : ℝ → ℂ := fun L =>
    Complex.exp (-(1 : ℂ) * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L
  let P : ℝ → ℂ := fun L => Complex.exp (L : ℂ)
  have hBglobal : IntegrableOn B (Ioi 0) := by
    exact integrableOn_exp_mul_ccmFirstClockXiRationalDivisor
      (s := (1 : ℂ)) (by norm_num)
  have hB : IntegrableOn B (Ioc (Real.pi / 2) A) :=
    hBglobal.mono_set (by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL.1)
  have hPmeas : AEStronglyMeasurable P
      (volume.restrict (Ioc (Real.pi / 2) A)) :=
    (by fun_prop : Continuous P).aestronglyMeasurable
  have hPbound : ∀ᵐ L : ℝ ∂volume.restrict (Ioc (Real.pi / 2) A),
      ‖P L‖ ≤ Real.exp A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    dsimp only [P]
    rw [Complex.norm_exp]
    simpa using Real.exp_le_exp.mpr hL.2
  have hPB : IntegrableOn (fun L => P L * B L)
      (Ioc (Real.pi / 2) A) := hB.bdd_mul hPmeas hPbound
  apply hPB.congr
  filter_upwards with L
  dsimp only [P, B]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The raw compact negative part is integrable. -/
theorem integrableOn_ccmFirstClockTailFloorRaw
    {d A : ℝ} (hA : Real.pi / 2 ≤ A) :
    IntegrableOn
      (fun L : ℝ => max (-((ccmFirstClockXiRationalDivisor L).re + d * L)) 0)
      (Ioc (Real.pi / 2) A) := by
  have hQ : IntegrableOn
      (fun L : ℝ => (ccmFirstClockXiRationalDivisor L).re)
      (Ioc (Real.pi / 2) A) :=
    (integrableOn_ccmFirstClockXiRationalDivisor_floorInterval hA).re
  have hlin : IntegrableOn (fun L : ℝ => d * L)
      (Ioc (Real.pi / 2) A) := by
    exact (by fun_prop : Continuous (fun L : ℝ => d * L)).integrableOn_Ioc
  have hneg : IntegrableOn
      (fun L : ℝ => -((ccmFirstClockXiRationalDivisor L).re + d * L))
      (Ioc (Real.pi / 2) A) := (hQ.add hlin).neg
  have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ))
      (Ioc (Real.pi / 2) A) := continuous_const.integrableOn_Ioc
  change IntegrableOn
    ((fun L : ℝ => -((ccmFirstClockXiRationalDivisor L).re + d * L)) ⊔
      fun _ : ℝ => 0) (Ioc (Real.pi / 2) A)
  exact hneg.sup hzero

theorem integrable_ccmFirstClockTailFloorCorrection
    {d A : ℝ} (hA : Real.pi / 2 ≤ A) :
    Integrable (ccmFirstClockTailFloorCorrection d A) := by
  exact (integrableOn_ccmFirstClockTailFloorRaw hA).integrable_indicator
    measurableSet_Ioc

/-- A compactly supported integrable density has an entire Laplace transform. -/
theorem differentiable_compactLaplaceIntegral
    {a A : ℝ} (ha : 0 ≤ a) (hA : a ≤ A)
    {f : ℝ → ℂ} (hf : IntegrableOn f (Ioc a A)) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ L : ℝ in Ioc a A, Complex.exp (-s * (L : ℂ)) * f L) := by
  intro s₀
  let F : ℂ → ℝ → ℂ := fun s L =>
    Complex.exp (-s * (L : ℂ)) * f L
  let F' : ℂ → ℝ → ℂ := fun s L =>
    (-(L : ℂ)) * Complex.exp (-s * (L : ℂ)) * f L
  let bound : ℝ → ℝ := fun L =>
    A * Real.exp ((|s₀.re| + 1) * A) * ‖f L‖
  have hA0 : 0 ≤ A := ha.trans hA
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hFmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (F s) (volume.restrict (Ioc a A)) := by
    filter_upwards with s
    exact (by fun_prop : Continuous (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)))).aestronglyMeasurable.mul hf.1
  have hFint : Integrable (F s₀) (volume.restrict (Ioc a A)) := by
    apply hf.bdd_mul
    · exact (by fun_prop : Continuous (fun L : ℝ =>
        Complex.exp (-s₀ * (L : ℂ)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      rw [Complex.norm_exp]
      have hre : (-s₀ * (L : ℂ)).re = -s₀.re * L := by simp [mul_re]
      rw [hre]
      apply Real.exp_le_exp.mpr
      have hL0 : 0 ≤ L := ha.trans hL.1.le
      calc
        -s₀.re * L ≤ |s₀.re| * L :=
          mul_le_mul_of_nonneg_right (neg_le_abs s₀.re) hL0
        _ ≤ |s₀.re| * A :=
          mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)
  have hF'meas : AEStronglyMeasurable (F' s₀)
      (volume.restrict (Ioc a A)) := by
    exact (by fun_prop : Continuous (fun L : ℝ =>
      (-(L : ℂ)) * Complex.exp (-s₀ * (L : ℂ)))).aestronglyMeasurable.mul hf.1
  have hboundInt : Integrable bound (volume.restrict (Ioc a A)) := by
    exact hf.norm.const_mul _
  have hbound : ∀ᵐ L ∂volume.restrict (Ioc a A),
      ∀ s ∈ Metric.ball s₀ 1, ‖F' s L‖ ≤ bound L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    intro s hs
    have hdist : ‖s - s₀‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hreDiff : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
    have hsre : -s.re ≤ |s₀.re| + 1 := by
      linarith [neg_le_abs s₀.re, neg_le_abs (s.re - s₀.re)]
    have hL0 : 0 ≤ L := ha.trans hL.1.le
    have hexp : Real.exp (-s.re * L) ≤
        Real.exp ((|s₀.re| + 1) * A) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right hsre hL0).trans
        (mul_le_mul_of_nonneg_left hL.2 (by positivity))
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hL0, Complex.norm_exp]
    have hre : (-s * (L : ℂ)).re = -s.re * L := by simp [mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hL.2 hexp (Real.exp_pos _).le hA0) (norm_nonneg _)
  have hdiff : ∀ᵐ L ∂volume.restrict (Ioc a A),
      ∀ s ∈ Metric.ball s₀ 1, HasDerivAt (fun s => F s L) (F' s L) s := by
    filter_upwards with L
    intro s hs
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (L : ℂ)))
        (-(L : ℂ) * Complex.exp (-s * (L : ℂ))) s := by
      simpa [mul_comm] using
        (((hasDerivAt_id s).neg.mul_const (L : ℂ)).cexp)
    simpa only [F, F', mul_assoc] using hexp.mul_const (f L)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a A)) (F := F) (F' := F')
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := bound)
    hball hFmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2.differentiableAt

/-- Entire compact floor-correction Laplace transform. -/
def ccmFirstClockTailFloorCorrectionLaplace (d A : ℝ) (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioc (Real.pi / 2) A,
    Complex.exp (-s * (L : ℂ)) *
      ((max (-((ccmFirstClockXiRationalDivisor L).re + d * L)) 0 : ℝ) : ℂ)

theorem differentiable_ccmFirstClockTailFloorCorrectionLaplace
    {d A : ℝ} (hA : Real.pi / 2 ≤ A) :
    Differentiable ℂ (ccmFirstClockTailFloorCorrectionLaplace d A) := by
  exact differentiable_compactLaplaceIntegral (by positivity) hA
    (integrableOn_ccmFirstClockTailFloorRaw hA).ofReal

/-- Compact head deleted from the full linear tent transform. -/
def ccmFirstClockTailLinearHeadLaplace (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioc (0 : ℝ) (Real.pi / 2),
    Complex.exp (-s * (L : ℂ)) * (L : ℂ)

theorem differentiable_ccmFirstClockTailLinearHeadLaplace :
    Differentiable ℂ ccmFirstClockTailLinearHeadLaplace := by
  exact differentiable_compactLaplaceIntegral (le_refl 0) (by positivity)
    ((by fun_prop : Continuous (fun L : ℝ => (L : ℂ))).integrableOn_Ioc)

/-- Holomorphic continuation of `d * integral_(pi/2)^infinity L exp(-sL) dL`. -/
def ccmFirstClockTailLinearContinuation (d : ℝ) (s : ℂ) : ℂ :=
  (d : ℂ) * (1 / s ^ 2 - ccmFirstClockTailLinearHeadLaplace s)

theorem differentiableAt_ccmFirstClockTailLinearContinuation
    (d : ℝ) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (ccmFirstClockTailLinearContinuation d) s := by
  unfold ccmFirstClockTailLinearContinuation
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hrat : DifferentiableAt ℂ (fun w : ℂ => 1 / w ^ 2) s := by
    fun_prop
  have hhead : DifferentiableAt ℂ ccmFirstClockTailLinearHeadLaplace s :=
    differentiable_ccmFirstClockTailLinearHeadLaplace s
  exact differentiableAt_const.mul (hrat.sub hhead)

theorem integral_tail_linear_eq_continuation
    {d : ℝ} {s : ℂ} (hs : 0 < s.re) :
    (∫ L : ℝ in Ioi (Real.pi / 2),
      Complex.exp (-s * (L : ℂ)) * ((d * L : ℝ) : ℂ)) =
      ccmFirstClockTailLinearContinuation d s := by
  let f : ℝ → ℂ := fun L =>
    Complex.exp (-s * (L : ℂ)) * (L : ℂ)
  have hfull : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_mul_exp_neg_mul (c := s) hs
    apply h.congr_fun _ measurableSet_Ioi
    intro L hL
    dsimp only [f]
    ring
  have hhead : IntegrableOn f (Ioc 0 (Real.pi / 2)) :=
    hfull.mono_set (by intro L hL; exact hL.1)
  have htail : IntegrableOn f (Ioi (Real.pi / 2)) :=
    hfull.mono_set (by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.pi / 2))
      (Ioi (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro L hheadL htailL
    exact (not_lt_of_ge hheadL.2) htailL
  have hsplit := setIntegral_union₀ hdisj.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hhead htail
  rw [Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hsplit
  have hfullValue := integral_mul_exp_neg_mul_Ioi (c := s) hs
  have htailValue : (∫ L : ℝ in Ioi (Real.pi / 2), f L) =
      1 / s ^ 2 - ccmFirstClockTailLinearHeadLaplace s := by
    dsimp only [f] at hsplit
    rw [show (∫ L : ℝ in Ioi 0, f L) = 1 / s ^ 2 by
      dsimp only [f]
      rw [show (fun L : ℝ => Complex.exp (-s * (L : ℂ)) * (L : ℂ)) =
          fun L : ℝ => (L : ℂ) * Complex.exp (-(s * L)) by
        funext L
        ring]
      exact hfullValue] at hsplit
    unfold ccmFirstClockTailLinearHeadLaplace
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit.symm
  unfold ccmFirstClockTailLinearContinuation
  rw [show (∫ L : ℝ in Ioi (Real.pi / 2),
      Complex.exp (-s * (L : ℂ)) * ((d * L : ℝ) : ℂ)) =
      (d : ℂ) * ∫ L : ℝ in Ioi (Real.pi / 2), f L by
      rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro L hL
    dsimp only [f]
    push_cast
    ring, htailValue]

/-- Real exponential weighting preserves integrability of the compact floor correction. -/
theorem integrableOn_ccmFirstClockTailFloorCorrectionDensity
    {d A r : ℝ} (hA : Real.pi / 2 ≤ A) :
    IntegrableOn (fun L : ℝ =>
      Real.exp (-r * L) * ccmFirstClockTailFloorCorrection d A L)
      (Ioi (Real.pi / 2)) := by
  let raw : ℝ → ℝ := fun L =>
    max (-((ccmFirstClockXiRationalDivisor L).re + d * L)) 0
  have hraw : IntegrableOn raw (Ioc (Real.pi / 2) A) :=
    integrableOn_ccmFirstClockTailFloorRaw hA
  have hexpMeas : AEStronglyMeasurable (fun L : ℝ => Real.exp (-r * L))
      (volume.restrict (Ioc (Real.pi / 2) A)) :=
    (by fun_prop : Continuous (fun L : ℝ => Real.exp (-r * L))).aestronglyMeasurable
  have hexpBound : ∀ᵐ L : ℝ ∂volume.restrict (Ioc (Real.pi / 2) A),
      ‖Real.exp (-r * L)‖ ≤ Real.exp (|r| * A) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 ≤ L :=
      (by positivity : (0 : ℝ) ≤ Real.pi / 2).trans hL.1.le
    calc
      -r * L ≤ |-r * L| := le_abs_self _
      _ = |r| * L := by rw [abs_mul, abs_neg, abs_of_nonneg hL0]
      _ ≤ |r| * A := mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)
  have hweighted : IntegrableOn (fun L => Real.exp (-r * L) * raw L)
      (Ioc (Real.pi / 2) A) := hraw.bdd_mul hexpMeas hexpBound
  have hglobal := hweighted.integrable_indicator measurableSet_Ioc
  apply hglobal.integrableOn.congr
  filter_upwards with L
  unfold ccmFirstClockTailFloorCorrection
  dsimp only [raw]
  by_cases hmem : L ∈ Ioc (Real.pi / 2) A
  · simp [Set.indicator_of_mem hmem]
  · simp [Set.indicator_of_notMem hmem]

/-- Every positive exponential moment of the affine correction exists. -/
theorem integrableOn_ccmFirstClockTailLinearDensity
    {d r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun L : ℝ => Real.exp (-r * L) * (d * L))
      (Ioi (Real.pi / 2)) := by
  have hbase := integrableOn_pow_mul_exp_neg_mul_Ioi hr 1
  have htail := hbase.mono_set (show Ioi (Real.pi / 2) ⊆ Ioi 0 by
    intro L hL
    exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
  have hscaled := htail.const_mul d
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro L hL
  simp only [pow_one]
  ring

/-- Complex exponential weighting preserves the compact correction as well. -/
theorem integrableOn_cexp_mul_ccmFirstClockTailFloorCorrection
    {d A : ℝ} (hA : Real.pi / 2 ≤ A) (s : ℂ) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) *
        (ccmFirstClockTailFloorCorrection d A L : ℂ))
      (Ioi (Real.pi / 2)) := by
  let raw : ℝ → ℝ := fun L =>
    max (-((ccmFirstClockXiRationalDivisor L).re + d * L)) 0
  have hraw : IntegrableOn (fun L => (raw L : ℂ))
      (Ioc (Real.pi / 2) A) :=
    (integrableOn_ccmFirstClockTailFloorRaw hA).ofReal
  have hexpMeas : AEStronglyMeasurable
      (fun L : ℝ => Complex.exp (-s * (L : ℂ)))
      (volume.restrict (Ioc (Real.pi / 2) A)) :=
    (by fun_prop : Continuous (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)))).aestronglyMeasurable
  have hexpBound : ∀ᵐ L : ℝ ∂volume.restrict (Ioc (Real.pi / 2) A),
      ‖Complex.exp (-s * (L : ℂ))‖ ≤ Real.exp (|s.re| * A) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    rw [Complex.norm_exp]
    have hre : (-s * (L : ℂ)).re = -s.re * L := by simp [mul_re]
    rw [hre]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 ≤ L :=
      (by positivity : (0 : ℝ) ≤ Real.pi / 2).trans hL.1.le
    calc
      -s.re * L ≤ |-s.re * L| := le_abs_self _
      _ = |s.re| * L := by rw [abs_mul, abs_neg, abs_of_nonneg hL0]
      _ ≤ |s.re| * A := mul_le_mul_of_nonneg_left hL.2 (abs_nonneg _)
  have hweighted : IntegrableOn (fun L =>
      Complex.exp (-s * (L : ℂ)) * (raw L : ℂ))
      (Ioc (Real.pi / 2) A) := hraw.bdd_mul hexpMeas hexpBound
  have hglobal := hweighted.integrable_indicator measurableSet_Ioc
  apply hglobal.integrableOn.congr
  filter_upwards with L
  unfold ccmFirstClockTailFloorCorrection
  dsimp only [raw]
  by_cases hmem : L ∈ Ioc (Real.pi / 2) A
  · simp [Set.indicator_of_mem hmem]
  · simp [Set.indicator_of_notMem hmem]

theorem integral_tail_floorCorrection_eq_compactLaplace
    {d A : ℝ} (s : ℂ) :
    (∫ L : ℝ in Ioi (Real.pi / 2),
      Complex.exp (-s * (L : ℂ)) *
        (ccmFirstClockTailFloorCorrection d A L : ℂ)) =
      ccmFirstClockTailFloorCorrectionLaplace d A s := by
  let raw : ℝ → ℂ := fun L =>
    ((max (-((ccmFirstClockXiRationalDivisor L).re + d * L)) 0 : ℝ) : ℂ)
  have hfun : (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) *
        (ccmFirstClockTailFloorCorrection d A L : ℂ)) =
      (Ioc (Real.pi / 2) A).indicator
        (fun L : ℝ => Complex.exp (-s * (L : ℂ)) * raw L) := by
    funext L
    unfold ccmFirstClockTailFloorCorrection
    dsimp only [raw]
    by_cases hmem : L ∈ Ioc (Real.pi / 2) A
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  rw [hfun, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr]
  · rfl
  · intro L hL
    exact hL.1

/-- Ordinary Laplace transform of the corrected nonnegative physical carrier. -/
def ccmFirstClockTailFloorLaplace (d A : ℝ) (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi (Real.pi / 2),
    Complex.exp (-s * (L : ℂ)) *
      (ccmFirstClockTailFloorCarrier d A L : ℂ)

/-- Meromorphic-free continuation of the corrected carrier through every positive-axis disk. -/
def ccmFirstClockTailFloorContinuation (d A : ℝ) (s : ℂ) : ℂ :=
  ccmFirstClockTailContinuation s +
    ccmFirstClockTailLinearContinuation d s +
    ccmFirstClockTailFloorCorrectionLaplace d A s

/-- On the unconditional half-plane, corrected continuation equals its ordinary Laplace integral. -/
theorem integral_ccmFirstClockTailFloorCarrier_eq_continuation
    {d A : ℝ} (hA : Real.pi / 2 ≤ A)
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    ccmFirstClockTailFloorLaplace d A s =
      ccmFirstClockTailFloorContinuation d A s := by
  let q : ℝ → ℂ := fun L =>
    Complex.exp (-s * (L : ℂ)) * ccmFirstClockXiRationalDivisor L
  let lin : ℝ → ℂ := fun L =>
    Complex.exp (-s * (L : ℂ)) * ((d * L : ℝ) : ℂ)
  let corr : ℝ → ℂ := fun L =>
    Complex.exp (-s * (L : ℂ)) *
      (ccmFirstClockTailFloorCorrection d A L : ℂ)
  have hq : IntegrableOn q (Ioi (Real.pi / 2)) :=
    (integrableOn_exp_mul_ccmFirstClockXiRationalDivisor hsHalf).mono_set (by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
  have hlin : IntegrableOn lin (Ioi (Real.pi / 2)) := by
    have hbase := integrableOn_mul_exp_neg_mul (c := s) (by linarith)
    have htail := hbase.mono_set (show Ioi (Real.pi / 2) ⊆ Ioi 0 by
      intro L hL
      exact lt_trans (by positivity : 0 < Real.pi / 2) hL)
    have hscaled := htail.const_mul (d : ℂ)
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro L hL
    dsimp only [lin]
    push_cast
    ring
  have hcorr : IntegrableOn corr (Ioi (Real.pi / 2)) :=
    integrableOn_cexp_mul_ccmFirstClockTailFloorCorrection hA s
  have hQreal (L : ℝ) : ccmFirstClockXiRationalDivisor L =
      ((ccmFirstClockXiRationalDivisor L).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [ccmFirstClockXiRationalDivisor_im_eq_zero L]
  have hintegrand : (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) *
        (ccmFirstClockTailFloorCarrier d A L : ℂ)) =
      fun L => (q L + lin L) + corr L := by
    funext L
    dsimp only [q, lin, corr]
    rw [hQreal L]
    unfold ccmFirstClockTailFloorCarrier
    push_cast
    ring
  unfold ccmFirstClockTailFloorLaplace,
    ccmFirstClockTailFloorContinuation
  rw [hintegrand, integral_add (hq.add hlin) hcorr,
    integral_add hq hlin,
    integral_tail_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation hsHalf,
    integral_tail_linear_eq_continuation (by linarith),
    integral_tail_floorCorrection_eq_compactLaplace]

/-- Corrected continuation is analytic on the same narrow positive strip as the Xi tail. -/
theorem analyticOnNhd_ccmFirstClockTailFloorContinuation_strip
    {d A b : ℝ} (hA : Real.pi / 2 ≤ A) (hb : 0 < b) :
    AnalyticOnNhd ℂ (ccmFirstClockTailFloorContinuation d A)
      (ccmFirstClockLandauStrip b) := by
  intro s hs
  have hQ := analyticOnNhd_ccmFirstClockTailContinuation_strip hb s hs
  have hsre : 0 < s.re := hb.trans hs.1
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero, zero_re] at hsre
    linarith
  have hlin := differentiableAt_ccmFirstClockTailLinearContinuation d hs0
  have hcorr := differentiable_ccmFirstClockTailFloorCorrectionLaplace hA s
  exact (hQ.differentiableAt.add hlin).add hcorr |>.analyticAt

/-- Translation of the corrected tail continuation to a Landau MGF center. -/
def ccmFirstClockTailFloorLandauContinuation
    (d A r : ℝ) (z : ℂ) : ℂ :=
  ccmFirstClockTailFloorContinuation d A ((r : ℂ) - z)

theorem differentiableOn_ccmFirstClockTailFloorLandauContinuation_closedBall
    {d A r : ℝ} (hA : Real.pi / 2 ≤ A) (hr : 0 < r)
    {R : NNReal} (hR : (R : ℝ) < r / 2) :
    DifferentiableOn ℂ (ccmFirstClockTailFloorLandauContinuation d A r)
      (Metric.closedBall 0 (R : ℝ)) := by
  have hQ := differentiableOn_ccmFirstClockLandauContinuation_closedBall hr hR
  intro z hz
  have hzNorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  let s : ℂ := (r : ℂ) - z
  have hsre : 0 < s.re := by
    have hreNorm : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    dsimp only [s]
    simp only [sub_re, ofReal_re]
    linarith [le_trans (le_abs_self z.re) hreNorm]
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero, zero_re] at hsre
    linarith
  have haffine : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) - w) z := by
    fun_prop
  have hlinAt : DifferentiableAt ℂ
      (fun w : ℂ => ccmFirstClockTailLinearContinuation d ((r : ℂ) - w)) z :=
    (differentiableAt_ccmFirstClockTailLinearContinuation d hs0).comp z haffine
  have hcorrAt : DifferentiableAt ℂ
      (fun w : ℂ => ccmFirstClockTailFloorCorrectionLaplace d A ((r : ℂ) - w)) z :=
    (differentiable_ccmFirstClockTailFloorCorrectionLaplace hA _).comp z haffine
  unfold ccmFirstClockTailFloorLandauContinuation,
    ccmFirstClockTailFloorContinuation
  exact ((hQ z hz).add hlinAt.differentiableWithinAt).add
    hcorrAt.differentiableWithinAt

end

end RHTower
