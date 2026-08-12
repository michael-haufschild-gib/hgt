import GaloisForLFunctions.RHTower.SourceHorizontalRouteNProjectiveCremonaInvolution
import GaloisForLFunctions.RHTower.DeningerExponentGammaSixShellTransportRigidity
import GaloisForLFunctions.RHTower.DeningerMertensAdiabaticCorner

/-!
# Route-N parity versus Deninger Gamma-six mixed curvature

The source Gamma-six clock is not a label-blind composite.  Its tame construction retains the
ordered prime pair `(2,3)`.  Multiplying the already source-derived Route-N odds at exactly these
two labels produces critical odds `1/6` and reciprocal orientations

`6^(-1-2|t|)` and `6^(-1+2|t|)`.

After division by critical odds, the inward orientation is exactly Deninger's mixed
reflection--Wold curvature `(1/6)^(2|t|)`; the outward orientation is its reciprocal.  Hence the
shell anomaly and the adaptive parity doublet are one coefficient, not two possible constraints.
The result identifies a legal source carrier for the reciprocal-odds polarity while preserving
both prime labels.  It does not assert Wold stationarity or event-level abelian admission.
-/

namespace RHTower

noncomputable section

/-- Prime-labelled critical Route-N reservoir at the ordered Gamma-six pair `(2,3)`. -/
def routeNGammaSixCriticalParityOdds : ℝ :=
  routeNGammaSewnCriticalSquarefreeParityOdds ⟨2, Nat.prime_two⟩ *
    routeNGammaSewnCriticalSquarefreeParityOdds ⟨3, Nat.prime_three⟩

/-- Product of the two inward Route-N orientations, retaining factors at `2` and `3`. -/
def routeNGammaSixInwardAdaptiveParityOdds (t : ℝ) : ℝ :=
  routeNGammaSewnInwardAdaptiveParityOdds t ⟨2, Nat.prime_two⟩ *
    routeNGammaSewnInwardAdaptiveParityOdds t ⟨3, Nat.prime_three⟩

/-- Product of the two outward Route-N orientations, retaining factors at `2` and `3`. -/
def routeNGammaSixOutwardAdaptiveParityOdds (t : ℝ) : ℝ :=
  routeNGammaSewnOutwardAdaptiveParityOdds t ⟨2, Nat.prime_two⟩ *
    routeNGammaSewnOutwardAdaptiveParityOdds t ⟨3, Nat.prime_three⟩

theorem routeNGammaSixCriticalParityOdds_eq :
    routeNGammaSixCriticalParityOdds = (1 / 6 : ℝ) := by
  rw [routeNGammaSixCriticalParityOdds,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq]
  norm_num [routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]

theorem routeNGammaSixInwardAdaptiveParityOdds_eq (t : ℝ) :
    routeNGammaSixInwardAdaptiveParityOdds t =
      (6 : ℝ) ^ (-2 * |t| - 1) := by
  rw [routeNGammaSixInwardAdaptiveParityOdds,
    routeNGammaSewnInwardAdaptiveParityOdds_eq,
    routeNGammaSewnInwardAdaptiveParityOdds_eq]
  change (2 : ℝ) ^ (-2 * |t| - 1) * (3 : ℝ) ^ (-2 * |t| - 1) =
    (6 : ℝ) ^ (-2 * |t| - 1)
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem routeNGammaSixOutwardAdaptiveParityOdds_eq (t : ℝ) :
    routeNGammaSixOutwardAdaptiveParityOdds t =
      (6 : ℝ) ^ (2 * |t| - 1) := by
  rw [routeNGammaSixOutwardAdaptiveParityOdds,
    routeNGammaSewnOutwardAdaptiveParityOdds_eq,
    routeNGammaSewnOutwardAdaptiveParityOdds_eq]
  change (2 : ℝ) ^ (2 * |t| - 1) * (3 : ℝ) ^ (2 * |t| - 1) =
    (6 : ℝ) ^ (2 * |t| - 1)
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The ordered `(2,3)` product still obeys the exact critical-reservoir law. -/
theorem routeNGammaSixAdaptiveParityOdds_mul_eq_critical_sq (t : ℝ) :
    routeNGammaSixOutwardAdaptiveParityOdds t *
        routeNGammaSixInwardAdaptiveParityOdds t =
      routeNGammaSixCriticalParityOdds ^ 2 := by
  rw [routeNGammaSixOutwardAdaptiveParityOdds,
    routeNGammaSixInwardAdaptiveParityOdds,
    routeNGammaSixCriticalParityOdds]
  rw [mul_mul_mul_comm,
    routeNGammaSewnAdaptiveParityOdds_mul_eq_critical_sq,
    routeNGammaSewnAdaptiveParityOdds_mul_eq_critical_sq]
  ring

/-- **N/L coefficient collision.**  Normalized inward Route-N `(2,3)` odds are exactly the
Deninger mixed reflection--Wold curvature. -/
theorem routeNGammaSixInward_div_critical_eq_reflectionWoldCurvature
    (t : ℝ) :
    routeNGammaSixInwardAdaptiveParityOdds t /
        routeNGammaSixCriticalParityOdds =
      deningerGammaSixReflectionWoldCurvature |t| := by
  rw [routeNGammaSixInwardAdaptiveParityOdds_eq,
    routeNGammaSixCriticalParityOdds_eq,
    deningerGammaSixReflectionWoldCurvature]
  have h6 : (0 : ℝ) < 6 := by norm_num
  rw [div_eq_iff (by norm_num : (1 / 6 : ℝ) ≠ 0)]
  rw [show (1 / 6 : ℝ) = (6 : ℝ) ^ (-1 : ℝ) by
      rw [Real.rpow_neg_one]
      norm_num,
    ← Real.rpow_mul h6.le,
    ← Real.rpow_add h6]
  congr 1
  ring

/-- Normalized outward Route-N odds are the reciprocal Deninger mixed curvature. -/
theorem routeNGammaSixOutward_div_critical_mul_reflectionWoldCurvature
    (t : ℝ) :
    (routeNGammaSixOutwardAdaptiveParityOdds t /
        routeNGammaSixCriticalParityOdds) *
      deningerGammaSixReflectionWoldCurvature |t| = 1 := by
  have hc : routeNGammaSixCriticalParityOdds ≠ 0 := by
    rw [routeNGammaSixCriticalParityOdds_eq]
    norm_num
  have hreservoir := routeNGammaSixAdaptiveParityOdds_mul_eq_critical_sq t
  have hcurvature :=
    routeNGammaSixInward_div_critical_eq_reflectionWoldCurvature t
  rw [← hcurvature]
  field_simp [hc]
  nlinarith

/-- One literal Gamma-six Wold step scales the shell carrier by the normalized inward Route-N
orientation.  This is the same source anomaly in parity and shell coordinates. -/
theorem deningerGammaSixShellReflectionMultiplier_wold_eq_routeNInward
    (t : ℝ) (n : ℕ) :
    deningerGammaSixShellReflectionMultiplier |t|
        (deningerGammaSixWoldCoordinate n) =
      (routeNGammaSixInwardAdaptiveParityOdds t /
          routeNGammaSixCriticalParityOdds) *
        deningerGammaSixShellReflectionMultiplier |t| n := by
  rw [deningerGammaSixShellReflectionMultiplier_wold,
    routeNGammaSixInward_div_critical_eq_reflectionWoldCurvature]

/-- Positive-half source point carrying the unsigned retained horizontal grade. -/
def routeNGammaSixPositiveSpectralPoint (t : ℝ) : ℂ :=
  ((((1 + |t|) / 2 : ℝ)) : ℂ)

@[simp] theorem routeNGammaSixPositiveSpectralPoint_re (t : ℝ) :
    (routeNGammaSixPositiveSpectralPoint t).re = (1 + |t|) / 2 := by
  rfl

/-- The signed difference of the two Route-N orientations is not a new scalar: it is exactly the
grade-two marked Gamma-six tame/Calderón reader, multiplied by critical vacuum odds. -/
theorem routeNGammaSixOutward_sub_inward_eq_critical_mul_tameReader
    (t : ℝ) :
    routeNGammaSixOutwardAdaptiveParityOdds t -
        routeNGammaSixInwardAdaptiveParityOdds t =
      routeNGammaSixCriticalParityOdds *
        deningerGammaSixExceptionalTameReader 2
          (routeNGammaSixPositiveSpectralPoint t) := by
  have h6 : (0 : ℝ) < 6 := by norm_num
  rw [routeNGammaSixOutwardAdaptiveParityOdds_eq,
    routeNGammaSixInwardAdaptiveParityOdds_eq,
    routeNGammaSixCriticalParityOdds_eq,
    deningerGammaSixExceptionalTameReader_eq_mateCurvature,
    deningerTensorSquareRadialMateCurvature_eq_sinh]
  · rw [routeNGammaSixPositiveSpectralPoint_re]
    norm_num [Real.rpow_def_of_pos h6, Real.sinh_eq]
    have hlog36 : Real.log 36 = 2 * Real.log 6 := by
      rw [show (36 : ℝ) = 6 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog36]
    have hpos :
        Real.exp (-Real.log 6 + Real.log 6 * |t| * 2) =
          (1 / 6 : ℝ) * Real.exp (|t| * (2 * Real.log 6)) := by
      rw [show -Real.log 6 + Real.log 6 * |t| * 2 =
          -Real.log 6 + |t| * (2 * Real.log 6) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log h6]
      norm_num
    have hneg :
        Real.exp (-Real.log 6 - Real.log 6 * |t| * 2) =
          (1 / 6 : ℝ) * Real.exp (-(|t| * (2 * Real.log 6))) := by
      rw [show -Real.log 6 - Real.log 6 * |t| * 2 =
          -Real.log 6 + (-(|t| * (2 * Real.log 6))) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log h6]
      norm_num
    rw [show Real.log 6 * (2 * |t| - 1) =
          -Real.log 6 + Real.log 6 * |t| * 2 by ring,
      show Real.log 6 * (-(2 * |t|) - 1) =
          -Real.log 6 - Real.log 6 * |t| * 2 by ring,
      show (2 * ((1 + |t|) / 2) - 1) * (2 * Real.log 6) =
          |t| * (2 * Real.log 6) by ring]
    rw [hpos, hneg]
    ring
  · positivity

/-- The tempting direct S1 landing into Hardy vacuum is identically blind: depth zero of every
source-curved Poisson character is one, independently of horizontal orientation. -/
theorem deningerSourceCurvedPoissonCoefficient_orientationDifference_vacuum
    (p : Nat.Primes) (t : ℝ) :
    deningerSourceCurvedPoissonCoefficient p (1 + t) 0 -
        deningerSourceCurvedPoissonCoefficient p (1 - t) 0 = 0 := by
  simp [deningerSourceCurvedPoissonCoefficient]

/-- Equality of the prime-labelled Gamma-six orientations is neutral-grade rigidity. -/
theorem routeNGammaSixOutwardAdaptiveParityOdds_eq_inward_iff (t : ℝ) :
    routeNGammaSixOutwardAdaptiveParityOdds t =
        routeNGammaSixInwardAdaptiveParityOdds t ↔
      t = 0 := by
  rw [routeNGammaSixOutwardAdaptiveParityOdds_eq,
    routeNGammaSixInwardAdaptiveParityOdds_eq]
  constructor
  · intro h
    have hexponent :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 6)).injective h
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

/-- Positive survivor of the vacuum no-go: the grade-two marked tame reader is coefficient
faithful and vanishes exactly at neutral grade. -/
theorem routeNGammaSixOutward_sub_inward_eq_zero_iff (t : ℝ) :
    routeNGammaSixOutwardAdaptiveParityOdds t -
        routeNGammaSixInwardAdaptiveParityOdds t = 0 ↔
      t = 0 := by
  rw [sub_eq_zero, routeNGammaSixOutwardAdaptiveParityOdds_eq_inward_iff]

end

end RHTower
