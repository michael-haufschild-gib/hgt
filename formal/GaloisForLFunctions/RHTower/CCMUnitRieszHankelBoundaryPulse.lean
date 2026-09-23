import GaloisForLFunctions.RHTower.CCMBoundaryRelativeTrace
import GaloisForLFunctions.RHTower.CCMUnitRieszCesaroCurvature

/-!
# Unit-Riesz curvature as a Hankel boundary pulse

The canonical fast-minus-slow FU--UR curvature pair has positive boundary relative trace at every
positive aperture, despite its sign-changing pointwise density.  Its exact pulse is bounded by
`3/128` and peaks at `2 log 2`.  The same pair cannot be an EP positive operator covariance:
every separated two-sample compression has strictly negative determinant.
-/

open Complex Matrix Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Fast positive channel whose square is the fast FU--UR curvature density. -/
def unitRieszFastLeakProfile (t : ℝ) : ℂ :=
  ((Real.sqrt (3 / 32) * Real.exp (-t / 2) : ℝ) : ℂ)

/-- Slow positive channel whose square is the slow FU--UR curvature density. -/
def unitRieszSlowLeakProfile (t : ℝ) : ℂ :=
  ((Real.sqrt (3 / 128) * Real.exp (-t / 4) : ℝ) : ℂ)

theorem leakDensity_unitRieszFastLeakProfile (t : ℝ) :
    leakDensity unitRieszFastLeakProfile t =
      unitRieszCesaroFastLeakDensity t := by
  unfold leakDensity unitRieszFastLeakProfile unitRieszCesaroFastLeakDensity
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 32), ← Real.exp_nat_mul]
  congr 1
  ring

theorem leakDensity_unitRieszSlowLeakProfile (t : ℝ) :
    leakDensity unitRieszSlowLeakProfile t =
      unitRieszCesaroSlowLeakDensity t := by
  unfold leakDensity unitRieszSlowLeakProfile unitRieszCesaroSlowLeakDensity
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 128), ← Real.exp_nat_mul]
  congr 1
  ring

theorem leakProfile_unitRieszFast : LeakProfile unitRieszFastLeakProfile := by
  refine ⟨?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ?_
    unfold unitRieszFastLeakProfile
    fun_prop
  · refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_one_add_mul_exp_neg (b := 1) one_pos).const_mul (3 / 32))
      ?_ measurableSet_Ioi
    intro t _
    change (3 / 32) * ((1 + t) * Real.exp (-1 * t)) =
      (1 + t) * leakDensity unitRieszFastLeakProfile t
    rw [leakDensity_unitRieszFastLeakProfile,
      unitRieszCesaroFastLeakDensity]
    ring

theorem leakProfile_unitRieszSlow : LeakProfile unitRieszSlowLeakProfile := by
  refine ⟨?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ?_
    unfold unitRieszSlowLeakProfile
    fun_prop
  · refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_one_add_mul_exp_neg (b := 1 / 2) (by norm_num)).const_mul
        (3 / 128)) ?_ measurableSet_Ioi
    intro t _
    change (3 / 128) * ((1 + t) * Real.exp (-(1 / 2) * t)) =
      (1 + t) * leakDensity unitRieszSlowLeakProfile t
    rw [leakDensity_unitRieszSlowLeakProfile,
      unitRieszCesaroSlowLeakDensity]
    have he : Real.exp (-(1 / 2) * t) = Real.exp (-t / 2) := by
      congr 1
      ring
    rw [he]
    ring

/-- Exact gap profile for any pure exponential leakage density. -/
theorem hankelGapProfile_of_leakDensity_exp
    {ℓ : ℝ → ℂ} {c a u : ℝ}
    (hdens : ∀ t, leakDensity ℓ t = c * Real.exp (-(a * t)))
    (ha : 0 < a) (hu : 0 ≤ u) :
    hankelGapProfile ℓ u = c / a ^ (2 : ℕ) * Real.exp (-(a * u)) := by
  have hb : (0 : ℝ) < ((a : ℂ)).re := by simpa
  have hcomplex := integral_Ioi_sub_mul_cexp_neg_mul (b := (a : ℂ)) hb hu
  have hpt : ∀ t : ℝ,
      (((t - u) * leakDensity ℓ t : ℝ) : ℂ) =
        (c : ℂ) * (((t : ℂ) - (u : ℂ)) *
          Complex.exp (-((a : ℂ) * (t : ℂ)))) := by
    intro t
    have hE : Complex.exp (-((a : ℂ) * (t : ℂ))) =
        ((Real.exp (-(a * t)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hdens t, hE]
    push_cast
    ring
  have hcast : ((hankelGapProfile ℓ u : ℝ) : ℂ) =
      ((c / a ^ (2 : ℕ) * Real.exp (-(a * u)) : ℝ) : ℂ) := by
    unfold hankelGapProfile
    calc
      ((∫ t in Ioi u, (t - u) * leakDensity ℓ t : ℝ) : ℂ) =
          ∫ t in Ioi u, (((t - u) * leakDensity ℓ t : ℝ) : ℂ) :=
        integral_complex_ofReal.symm
      _ = ∫ t in Ioi u,
          (c : ℂ) * (((t : ℂ) - (u : ℂ)) *
            Complex.exp (-((a : ℂ) * (t : ℂ)))) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t
      _ = (c : ℂ) * ∫ t in Ioi u,
          ((t : ℂ) - (u : ℂ)) *
            Complex.exp (-((a : ℂ) * (t : ℂ))) := integral_const_mul _ _
      _ = (c : ℂ) *
          (Complex.exp (-((a : ℂ) * (u : ℂ))) * (a : ℂ)⁻¹ ^ (2 : ℕ)) := by
        rw [hcomplex]
      _ = ((c / a ^ (2 : ℕ) * Real.exp (-(a * u)) : ℝ) : ℂ) := by
        have hE : Complex.exp (-((a : ℂ) * (u : ℂ))) =
            ((Real.exp (-(a * u)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
        rw [hE]
        push_cast
        field_simp [ha.ne']
  exact_mod_cast hcast

theorem hankelGapProfile_unitRieszFast {u : ℝ} (hu : 0 ≤ u) :
    hankelGapProfile unitRieszFastLeakProfile u =
      (3 / 32) * Real.exp (-u) := by
  rw [hankelGapProfile_of_leakDensity_exp
    (fun t => by
      rw [leakDensity_unitRieszFastLeakProfile,
        unitRieszCesaroFastLeakDensity]
      congr 2
      ring) one_pos hu]
  ring_nf

theorem hankelGapProfile_unitRieszSlow {u : ℝ} (hu : 0 ≤ u) :
    hankelGapProfile unitRieszSlowLeakProfile u =
      (3 / 32) * Real.exp (-u / 2) := by
  rw [hankelGapProfile_of_leakDensity_exp
    (fun t => by
      rw [leakDensity_unitRieszSlowLeakProfile,
        unitRieszCesaroSlowLeakDensity]
      congr 2
      ring) (by norm_num : (0 : ℝ) < 1 / 2) hu]
  ring_nf

/-- Signed fast-minus-slow HG boundary response selected by FU--UR curvature. -/
def unitRieszBoundaryPulse (u : ℝ) : ℝ :=
  boundaryRelativeTrace unitRieszFastLeakProfile u -
    boundaryRelativeTrace unitRieszSlowLeakProfile u

theorem unitRieszBoundaryPulse_eq {u : ℝ} (hu : 0 < u) :
    unitRieszBoundaryPulse u =
      (3 / 32) * (Real.exp (-u / 2) - Real.exp (-u)) := by
  rw [unitRieszBoundaryPulse,
    boundaryRelativeTrace_eq_gap_sub leakProfile_unitRieszFast hu,
    boundaryRelativeTrace_eq_gap_sub leakProfile_unitRieszSlow hu,
    hankelGapProfile_unitRieszFast (le_refl 0),
    hankelGapProfile_unitRieszFast hu.le,
    hankelGapProfile_unitRieszSlow (le_refl 0),
    hankelGapProfile_unitRieszSlow hu.le]
  norm_num
  ring

theorem unitRieszBoundaryPulse_pos {u : ℝ} (hu : 0 < u) :
    0 < unitRieszBoundaryPulse u := by
  rw [unitRieszBoundaryPulse_eq hu]
  have he : Real.exp (-u) < Real.exp (-u / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  positivity

theorem unitRieszBoundaryPulse_le (u : ℝ) :
    unitRieszBoundaryPulse u ≤ 3 / 128 := by
  by_cases hu : 0 < u
  · rw [unitRieszBoundaryPulse_eq hu]
    have hs : 0 ≤ (Real.exp (-u / 2) - 1 / 2) ^ (2 : ℕ) := sq_nonneg _
    have he : Real.exp (-u) = Real.exp (-u / 2) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    nlinarith
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    unfold unitRieszBoundaryPulse boundaryRelativeTrace
    have hfast :
        (∫ t in Ioi (0 : ℝ), min t u * leakDensity unitRieszFastLeakProfile t) =
          ∫ t in Ioi (0 : ℝ), u * leakDensity unitRieszFastLeakProfile t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change min t u * leakDensity unitRieszFastLeakProfile t =
        u * leakDensity unitRieszFastLeakProfile t
      rw [min_eq_right (hu0.trans ht.le)]
    have hslow :
        (∫ t in Ioi (0 : ℝ), min t u * leakDensity unitRieszSlowLeakProfile t) =
          ∫ t in Ioi (0 : ℝ), u * leakDensity unitRieszSlowLeakProfile t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change min t u * leakDensity unitRieszSlowLeakProfile t =
        u * leakDensity unitRieszSlowLeakProfile t
      rw [min_eq_right (hu0.trans ht.le)]
    rw [hfast, hslow]
    rw [integral_const_mul, integral_const_mul]
    rw [show (∫ t in Ioi (0 : ℝ), leakDensity unitRieszFastLeakProfile t) = 3 / 32 by
      rw [setIntegral_congr_fun measurableSet_Ioi fun t _ =>
        leakDensity_unitRieszFastLeakProfile t,
        integral_unitRieszCesaroFastLeakDensity]]
    rw [show (∫ t in Ioi (0 : ℝ), leakDensity unitRieszSlowLeakProfile t) = 3 / 64 by
      rw [setIntegral_congr_fun measurableSet_Ioi fun t _ =>
        leakDensity_unitRieszSlowLeakProfile t,
        integral_unitRieszCesaroSlowLeakDensity]]
    nlinarith

theorem unitRieszBoundaryPulse_at_two_log_two :
    unitRieszBoundaryPulse (2 * Real.log 2) = 3 / 128 := by
  have hu : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  rw [unitRieszBoundaryPulse_eq hu]
  have hhalf : Real.exp (-(2 * Real.log 2) / 2) = (1 / 2 : ℝ) := by
    rw [show -(2 * Real.log 2) / 2 = -Real.log 2 by ring,
      Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hquarter : Real.exp (-(2 * Real.log 2)) = (1 / 4 : ℝ) := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
      neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [hhalf, hquarter]
  norm_num

/-- Four-unit normalization of canonical boundary pulse. -/
def unitRieszFourUnitBoundaryPulse (u : ℝ) : ℝ :=
  (256 / 3) * unitRieszBoundaryPulse u

theorem unitRieszFourUnitBoundaryPulse_eq {u : ℝ} (hu : 0 < u) :
    unitRieszFourUnitBoundaryPulse u =
      8 * (Real.exp (-u / 2) - Real.exp (-u)) := by
  rw [unitRieszFourUnitBoundaryPulse, unitRieszBoundaryPulse_eq hu]
  ring

/-- Exact square slack between incoming four-unit pole trace and normalized curvature pulse. -/
theorem poleBoundaryTrace_sub_unitRieszFourUnitBoundaryPulse
    {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace polePacketProfile u -
        unitRieszFourUnitBoundaryPulse u =
      4 * (1 - Real.exp (-u / 2)) ^ (2 : ℕ) := by
  rw [boundaryRelativeTrace_polePacket hu,
    unitRieszFourUnitBoundaryPulse_eq hu]
  have he : Real.exp (-u) = Real.exp (-u / 2) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

theorem unitRieszFourUnitBoundaryPulse_lt_pole
    {u : ℝ} (hu : 0 < u) :
    unitRieszFourUnitBoundaryPulse u <
      boundaryRelativeTrace polePacketProfile u := by
  rw [sub_pos.symm,
    poleBoundaryTrace_sub_unitRieszFourUnitBoundaryPulse hu]
  have hne : 1 - Real.exp (-u / 2) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (Real.exp_lt_one_iff.mpr (by linarith))
  positivity

/-- Positive output-cutoff coefficient of the fast rank-one Hankel channel. -/
def unitRieszFastBoundaryCoefficient (u : ℝ) : ℝ :=
  (3 / 32) * (1 - Real.exp (-u))

/-- Positive output-cutoff coefficient of the slow rank-one Hankel channel. -/
def unitRieszSlowBoundaryCoefficient (u : ℝ) : ℝ :=
  (3 / 64) * (1 - Real.exp (-u / 2))

/-- Two-point compression of the fast-minus-slow boundary covariance. -/
def unitRieszBoundaryCovarianceCore (u y z : ℝ) : ℝ :=
  unitRieszFastBoundaryCoefficient u * Real.exp (-(y + z) / 2) -
    unitRieszSlowBoundaryCoefficient u * Real.exp (-(y + z) / 4)

theorem unitRieszBoundaryCovarianceCore_twoPoint_det (u L : ℝ) :
    unitRieszBoundaryCovarianceCore u 0 0 *
        unitRieszBoundaryCovarianceCore u L L -
      unitRieszBoundaryCovarianceCore u 0 L *
        unitRieszBoundaryCovarianceCore u L 0 =
    -(unitRieszFastBoundaryCoefficient u *
        unitRieszSlowBoundaryCoefficient u *
          (Real.exp (-L / 2) - Real.exp (-L / 4)) ^ (2 : ℕ)) := by
  unfold unitRieszBoundaryCovarianceCore
  have hsum : Real.exp (-(L + L) / 2) = Real.exp (-L / 2) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsumSlow : Real.exp (-(L + L) / 4) = Real.exp (-L / 4) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [zero_add, add_zero, neg_zero, zero_div, Real.exp_zero]
  rw [hsum, hsumSlow]
  ring

theorem unitRieszFastBoundaryCoefficient_pos {u : ℝ} (hu : 0 < u) :
    0 < unitRieszFastBoundaryCoefficient u := by
  unfold unitRieszFastBoundaryCoefficient
  have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  positivity

theorem unitRieszSlowBoundaryCoefficient_pos {u : ℝ} (hu : 0 < u) :
    0 < unitRieszSlowBoundaryCoefficient u := by
  unfold unitRieszSlowBoundaryCoefficient
  have h := Real.exp_lt_one_iff.mpr (by linarith : -u / 2 < 0)
  positivity

/-- Scalar-positive boundary pulse is never a positive operator covariance: every positive
aperture and every nonzero input separation expose a strictly negative two-point determinant. -/
theorem unitRieszBoundaryCovarianceCore_twoPoint_det_neg
    {u L : ℝ} (hu : 0 < u) (hL : 0 < L) :
    unitRieszBoundaryCovarianceCore u 0 0 *
        unitRieszBoundaryCovarianceCore u L L -
      unitRieszBoundaryCovarianceCore u 0 L *
        unitRieszBoundaryCovarianceCore u L 0 < 0 := by
  rw [unitRieszBoundaryCovarianceCore_twoPoint_det]
  apply neg_lt_zero.mpr
  have hdiff : Real.exp (-L / 2) - Real.exp (-L / 4) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_lt (Real.exp_lt_exp.mpr (by linarith))
  exact mul_pos
    (mul_pos (unitRieszFastBoundaryCoefficient_pos hu)
      (unitRieszSlowBoundaryCoefficient_pos hu))
    (sq_pos_of_ne_zero hdiff)

/-- Hermitian two-sample compression of fast-minus-slow output-boundary covariance. -/
def unitRieszBoundaryCovarianceMatrix (u L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![unitRieszBoundaryCovarianceCore u 0 0,
      unitRieszBoundaryCovarianceCore u 0 L;
    unitRieszBoundaryCovarianceCore u L 0,
      unitRieszBoundaryCovarianceCore u L L]

theorem unitRieszBoundaryCovarianceMatrix_det (u L : ℝ) :
    (unitRieszBoundaryCovarianceMatrix u L).det =
      -(unitRieszFastBoundaryCoefficient u *
        unitRieszSlowBoundaryCoefficient u *
          (Real.exp (-L / 2) - Real.exp (-L / 4)) ^ (2 : ℕ)) := by
  rw [unitRieszBoundaryCovarianceMatrix, Matrix.det_fin_two_of,
    unitRieszBoundaryCovarianceCore_twoPoint_det]

/-- EP obstruction: scalar boundary-trace positivity does not upgrade to positive
operator-valued covariance. -/
theorem unitRieszBoundaryCovarianceMatrix_not_posSemidef
    {u L : ℝ} (hu : 0 < u) (hL : 0 < L) :
    ¬(unitRieszBoundaryCovarianceMatrix u L).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  rw [unitRieszBoundaryCovarianceMatrix_det] at hdet
  have hneg := unitRieszBoundaryCovarianceCore_twoPoint_det_neg hu hL
  rw [unitRieszBoundaryCovarianceCore_twoPoint_det] at hneg
  exact (not_le_of_gt hneg) hdet

end GaloisForLFunctions.RHTower

end
