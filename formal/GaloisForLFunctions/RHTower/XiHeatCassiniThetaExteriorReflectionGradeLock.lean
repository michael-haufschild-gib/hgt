import GaloisForLFunctions.RHTower.XiHeatCassiniWoldThetaGreenCompensation

/-!
# Exterior theta reflection is a scalar grade lock

Reflecting the safe theta line from `c` to `-c` does not create a second phase equation.
The even Xi-mass test is unchanged after reversing the frequency variable, whereas the
phase-linear theta logarithmic jet is odd.  Consequently the complete reflected wave packet is
the negative of the original packet.  This closes the apparent two-line route to an independent
quadrature before any norm or asymptotic estimate is introduced.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Reflection of the exterior theta parameter, with simultaneous frequency reversal. -/
theorem thetaEsscherResolventParameter_neg_height_neg_frequency
    (c x : ℝ) :
    thetaEsscherResolventParameter (-c) (-x) =
      -thetaEsscherResolventParameter c x := by
  unfold thetaEsscherResolventParameter
  push_cast
  ring

/-- Evenness of the analytic mass test identifies the reflected bottom test after reversing
frequency. -/
theorem xiMassBottomTest_neg_height (a c : ℝ) (tau : ℂ) (x : ℝ) :
    xiMassBottomTest a (-c) tau x = xiMassBottomTest a c tau (-x) := by
  rw [xiMassBottomTest, xiMassBottomTest]
  have harg :
      ((((-x : ℝ) : ℂ) - (c : ℂ) * Complex.I)) =
        -(((x : ℂ) - ((-c : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [harg, xiMassAnalyticTest_neg]

/-- The phase-linear theta row changes sign under exterior-line reflection. -/
theorem pinnedMean_thetaQuantileResolvent_neg_height_neg_frequency
    {c : ℝ} (hc : 1 / 2 ≤ |c|) (x : ℝ) :
    pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter (-c) (-x))
          thetaQuantileCoordinate) =
      -pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter c x)
          thetaQuantileCoordinate) := by
  have hnegc : 1 / 2 ≤ |-c| := by simpa using hc
  have hleft :
      IsUnit (thetaSourcePencil (thetaEsscherResolventParameter (-c) (-x))) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hnegc (-x)
  have hright :
      IsUnit (thetaSourcePencil (thetaEsscherResolventParameter c x)) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hc x
  rw [pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hleft,
    pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv hright,
    thetaEsscherResolventParameter_neg_height_neg_frequency,
    logDeriv_XiC_neg]
  ring

/-- Pointwise scalar grade lock: the reflected phase-linear theta integrand is the negative of the
original integrand at reversed frequency. -/
theorem xiMassThetaQuantileResolventIntegrand_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) (x : ℝ) :
    xiMassThetaQuantileResolventIntegrand a (-c) tau x =
      -xiMassThetaQuantileResolventIntegrand a c tau (-x) := by
  rw [xiMassThetaQuantileResolventIntegrand,
    xiMassThetaQuantileResolventIntegrand,
    xiMassBottomTest_neg_height,
    pinnedMean_thetaQuantileResolvent_neg_height_neg_frequency hc]
  ring

/-- **Exterior reflection grade lock.**  The complete reflected theta wave packet is exactly the
negative of the original packet. -/
theorem xiMassThetaQuantileResolventIntegral_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileResolventIntegral a (-c) tau =
      -xiMassThetaQuantileResolventIntegral a c tau := by
  rw [xiMassThetaQuantileResolventIntegral,
    xiMassThetaQuantileResolventIntegral]
  have hpoint :
      xiMassThetaQuantileResolventIntegrand a (-c) tau =
        fun x : ℝ => -xiMassThetaQuantileResolventIntegrand a c tau (-x) := by
    funext x
    exact xiMassThetaQuantileResolventIntegrand_neg_height a hc tau x
  rw [hpoint, MeasureTheory.integral_neg]
  congr 1
  exact MeasureTheory.integral_neg_eq_self
    (xiMassThetaQuantileResolventIntegrand a c tau) volume

/-- The two exterior packets have identically zero sum, so they cannot provide two independent
scalar equations. -/
theorem xiMassThetaQuantileResolventIntegral_exterior_pair_eq_zero
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileResolventIntegral a (-c) tau +
        xiMassThetaQuantileResolventIntegral a c tau = 0 := by
  rw [xiMassThetaQuantileResolventIntegral_neg_height a hc]
  exact neg_add_cancel _

/-- Reflection preserves the packet norm and hence cannot improve its scalar line-bound problem. -/
theorem norm_xiMassThetaQuantileResolventIntegral_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    ‖xiMassThetaQuantileResolventIntegral a (-c) tau‖ =
      ‖xiMassThetaQuantileResolventIntegral a c tau‖ := by
  rw [xiMassThetaQuantileResolventIntegral_neg_height a hc, norm_neg]

/-- Polarized theta Green packet is the same fixed scalar times the phase-linear packet on either
exterior line. -/
theorem xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral_of_half_le_abs
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileMetricSymplecticIntegral a c tau =
      Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        xiMassThetaQuantileResolventIntegral a c tau := by
  rw [xiMassThetaQuantileMetricSymplecticIntegral,
    xiMassThetaQuantileResolventIntegral]
  have hfun : xiMassThetaQuantileMetricSymplecticIntegrand a c tau =
      fun x => (Complex.I * pinnedFirstMoment thetaQuantileCoordinate) *
        xiMassThetaQuantileResolventIntegrand a c tau x := by
    funext x
    have hpencil : IsUnit
        (thetaSourcePencil (thetaEsscherResolventParameter c (-x))) :=
      isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs hc (-x)
    rw [xiMassThetaQuantileMetricSymplecticIntegrand,
      xiMassThetaQuantileResolventIntegrand,
      thetaQuantileMetricSymplecticCurrent_resolvent_eq_I_mul_pinnedMean hpencil]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]

/-- Polarized theta Green current belongs to the odd exterior-reflection grade. -/
theorem xiMassThetaQuantileMetricSymplecticIntegral_neg_height
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiMassThetaQuantileMetricSymplecticIntegral a (-c) tau =
      -xiMassThetaQuantileMetricSymplecticIntegral a c tau := by
  have hnegc : 1 / 2 ≤ |-c| := by simpa using hc
  rw [xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral_of_half_le_abs
      a hnegc,
    xiMassThetaQuantileMetricSymplecticIntegral_eq_I_mul_resolventIntegral_of_half_le_abs
      a hc,
    xiMassThetaQuantileResolventIntegral_neg_height a hc]
  ring

/-- Grade-compatible reflected Ward packet.  Wold current receives the same odd-grade sign as the
theta current. -/
def xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket
    (a c : ℝ) (tau : ℂ) : ℂ :=
  xiMassThetaQuantileMetricSymplecticIntegral a (-c) tau -
    Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
      xiHeatCassiniPureWoldHalfDensityLayer a tau

/-- Reflected Ward packet is exactly the negative of the original packet, not a second equation. -/
theorem xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket_eq_neg
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket a c tau =
      -xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau := by
  rw [xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket,
    xiHeatCassiniWoldThetaGreenCompensatedPacket,
    xiMassThetaQuantileMetricSymplecticIntegral_neg_height a hc]
  ring

/-- The grade-compatible reflected Ward packet inherits the unconditional vertical bound, but
only because it is the negative of the original Ward law. -/
theorem exists_norm_xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket_vertical_bound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket a c
        ((sigma : ℂ) + u * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_norm_xiHeatCassiniWoldThetaGreenCompensatedPacket_vertical_bound
      hhalf hca hsigma
  refine ⟨C, fun u => ?_⟩
  rw [xiHeatCassiniReflectedWoldThetaGreenCompensatedPacket_eq_neg a
    (by rw [abs_of_pos (lt_trans (by norm_num) hhalf)]; exact hhalf.le), norm_neg]
  exact hC u

/-- Even exterior-grade projection of the two plus-sign packets isolates twice the pure Wold
current.  Bounding both plus-sign packets would therefore solve the original RH-strength current,
and is not supplied by reflection. -/
theorem xiHeatCassiniWoldThetaGreenCompensatedPacket_add_neg_height_eq_pureWold
    (a : ℝ) {c : ℝ} (hc : 1 / 2 ≤ |c|) (tau : ℂ) :
    xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau +
        xiHeatCassiniWoldThetaGreenCompensatedPacket a (-c) tau =
      2 * (Complex.I * pinnedFirstMoment thetaQuantileCoordinate *
        xiHeatCassiniPureWoldHalfDensityLayer a tau) := by
  rw [xiHeatCassiniWoldThetaGreenCompensatedPacket,
    xiHeatCassiniWoldThetaGreenCompensatedPacket,
    xiMassThetaQuantileMetricSymplecticIntegral_neg_height a hc]
  ring

/-- Uniform bound for the wrong-grade reflected packet, which keeps the even Wold sign while
reflecting only the odd theta current. -/
def XiHeatCassiniWrongGradeReflectedWoldThetaGreenLineBound
    (a c sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiHeatCassiniWoldThetaGreenCompensatedPacket a (-c)
      ((sigma : ℂ) + u * Complex.I)‖ ≤ C

/-- Since the right-line Ward packet is already bounded, the wrong-grade reflected packet is
bounded exactly when the even Wold current is bounded. -/
theorem xiHeatCassiniPureWoldHalfDensityLineBound_iff_wrongGradeReflected
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    XiHeatCassiniPureWoldHalfDensityLineBound a sigma ↔
      XiHeatCassiniWrongGradeReflectedWoldThetaGreenLineBound a c sigma := by
  let q : ℂ := 2 * (Complex.I * pinnedFirstMoment thetaQuantileCoordinate)
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero Complex.I_ne_zero
        pinnedFirstMoment_thetaQuantileCoordinate_ne_zero)
  have hcabs : 1 / 2 ≤ |c| := by
    rw [abs_of_pos (lt_trans (by norm_num) hhalf)]
    exact hhalf.le
  obtain ⟨CR, hCR⟩ :=
    exists_norm_xiHeatCassiniWoldThetaGreenCompensatedPacket_vertical_bound
      hhalf hca hsigma
  constructor
  · rintro ⟨CW, hCW⟩
    refine ⟨‖q‖ * CW + CR, fun u => ?_⟩
    let tau : ℂ := (sigma : ℂ) + u * Complex.I
    have hpair :=
      xiHeatCassiniWoldThetaGreenCompensatedPacket_add_neg_height_eq_pureWold
        a hcabs tau
    have hsolve :
        xiHeatCassiniWoldThetaGreenCompensatedPacket a (-c) tau =
          q * xiHeatCassiniPureWoldHalfDensityLayer a tau -
            xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau := by
      dsimp only [q] at hpair ⊢
      linear_combination hpair
    rw [hsolve]
    calc
      ‖q * xiHeatCassiniPureWoldHalfDensityLayer a tau -
          xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau‖ ≤
        ‖q * xiHeatCassiniPureWoldHalfDensityLayer a tau‖ +
          ‖xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau‖ :=
            norm_sub_le _ _
      _ ≤ ‖q‖ * CW + CR := by
        rw [norm_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hCW u) (norm_nonneg q)) (hCR u)
  · rintro ⟨CL, hCL⟩
    refine ⟨‖q⁻¹‖ * (CR + CL), fun u => ?_⟩
    let tau : ℂ := (sigma : ℂ) + u * Complex.I
    have hpair :=
      xiHeatCassiniWoldThetaGreenCompensatedPacket_add_neg_height_eq_pureWold
        a hcabs tau
    have hsolve :
        xiHeatCassiniPureWoldHalfDensityLayer a tau =
          q⁻¹ *
            (xiHeatCassiniWoldThetaGreenCompensatedPacket a c tau +
              xiHeatCassiniWoldThetaGreenCompensatedPacket a (-c) tau) := by
      dsimp only [q] at hpair ⊢
      rw [hpair]
      field_simp [pinnedFirstMoment_thetaQuantileCoordinate_ne_zero]
    rw [hsolve, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (hCR u) (hCL u)))
      (norm_nonneg _)

/-- **Wrong-grade reflection criterion.**  Asking the reflected theta line to retain the same Wold
sign is exactly RH; exterior reflection itself provides only the opposite, grade-compatible sign. -/
theorem riemannHypothesis_iff_xiHeatCassiniWrongGradeReflectedWoldThetaGreenLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      XiHeatCassiniWrongGradeReflectedWoldThetaGreenLineBound a c sigma :=
  (riemannHypothesis_iff_xiHeatCassiniPureWoldHalfDensityLineBound
    hhalf hca hsigma).trans
      (xiHeatCassiniPureWoldHalfDensityLineBound_iff_wrongGradeReflected
        hhalf hca hsigma)

end

end RHTower
