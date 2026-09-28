import GaloisForLFunctions.RHTower.CCMCoherentSignedMomentGammaControl
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Local capacity for the signed arithmetic moment

The reciprocal-Gamma square can be integrated over any displacement region.
On a radius-R window its capacity is at most R². Splitting the literal signed
charge into the window and its complement therefore retains the small radius
factor on concentrated energy and exposes the remaining tail separately.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

def ccmGammaSignedMomentLocalCapacity (s : Set ℝ) : ℝ :=
  ∫ r in s, r^2*ccmGammaHigherBinetModeDensity |r|

def ccmActualHeadSignedMomentLocalCharge (T : ℝ) (N : ℕ) (s : Set ℝ) : ℝ :=
  ∫ r in s, r*ccmActualHeadMidpointSignedMoment T N r

def ccmActualHeadSignedMomentLocalEnergy (T : ℝ) (N : ℕ) (s : Set ℝ) : ℝ :=
  ∫ r in s, (ccmActualHeadMidpointSignedMoment T N r)^2*ccmGammaHigherBinetDualDensity |r|

theorem ccmGammaSignedMomentLocalCapacity_nonneg (s : Set ℝ) :
    0 ≤ ccmGammaSignedMomentLocalCapacity s :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg r)
    (ccmGammaHigherBinetModeDensity_abs_nonneg r)

theorem ccmActualHeadSignedMomentLocalEnergy_nonneg (T : ℝ) (N : ℕ) (s : Set ℝ) :
    0 ≤ ccmActualHeadSignedMomentLocalEnergy T N s :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmGammaSignedMomentLocalCapacity_le_capacity (s : Set ℝ) :
    ccmGammaSignedMomentLocalCapacity s ≤ ccmGammaSignedMomentCapacity :=
  setIntegral_le_integral integrable_ccmGammaSignedMomentCapacityDensity
    (Filter.Eventually.of_forall fun r => mul_nonneg (sq_nonneg r)
      (ccmGammaHigherBinetModeDensity_abs_nonneg r))

theorem ccmActualHeadSignedMomentLocalEnergy_le_energy (T : ℝ) (N : ℕ) (s : Set ℝ) :
    ccmActualHeadSignedMomentLocalEnergy T N s ≤ ccmActualHeadSignedMomentGammaEnergy T N :=
  setIntegral_le_integral (integrable_ccmActualHeadSignedMomentGammaDensity T N)
    (Filter.Eventually.of_forall fun r => mul_nonneg (sq_nonneg _)
      (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))

theorem ccmActualHeadSignedMomentLocalCharge_dual_bound
    (T : ℝ) (N : ℕ) (s : Set ℝ) (t : ℝ) :
    2*t*ccmActualHeadSignedMomentLocalCharge T N s ≤
      ccmActualHeadSignedMomentLocalEnergy T N s + t^2*ccmGammaSignedMomentLocalCapacity s := by
  have hpoint (r : ℝ) : 2*t*(r*ccmActualHeadMidpointSignedMoment T N r) ≤
      (ccmActualHeadMidpointSignedMoment T N r)^2*ccmGammaHigherBinetDualDensity |r| +
        t^2*(r^2*ccmGammaHigherBinetModeDensity |r|) := by
    have h := sq_nonneg (ccmActualHeadMidpointSignedMoment T N r *
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|) -
      t*r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))
    rw [ccmGammaSignedMomentWeightedSquare] at h
    linarith only [h]
  have h := integral_mono
    (((integrable_ccmActualHeadSignedMoment_displacement T N).restrict (s := s)).const_mul (2*t))
    (((integrable_ccmActualHeadSignedMomentGammaDensity T N).restrict (s := s)).add
      ((integrable_ccmGammaSignedMomentCapacityDensity.restrict (s := s)).const_mul (t^2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_ccmActualHeadSignedMomentGammaDensity T N).restrict)
    ((integrable_ccmGammaSignedMomentCapacityDensity.restrict).const_mul (t^2))] at h
  simpa only [integral_const_mul, ccmActualHeadSignedMomentLocalCharge,
    ccmActualHeadSignedMomentLocalEnergy, ccmGammaSignedMomentLocalCapacity] using h

theorem sq_ccmActualHeadSignedMomentLocalCharge_le_capacity
    (T : ℝ) (N : ℕ) (s : Set ℝ) :
    (ccmActualHeadSignedMomentLocalCharge T N s)^2 ≤
      ccmGammaSignedMomentLocalCapacity s*ccmActualHeadSignedMomentLocalEnergy T N s := by
  let Q := ccmActualHeadSignedMomentLocalCharge T N s
  let A := ccmGammaSignedMomentLocalCapacity s
  let E := ccmActualHeadSignedMomentLocalEnergy T N s
  have hA : 0 ≤ A := ccmGammaSignedMomentLocalCapacity_nonneg s
  have hdual (t : ℝ) : 2*t*Q ≤ E+t^2*A :=
    ccmActualHeadSignedMomentLocalCharge_dual_bound T N s t
  change Q^2 ≤ A*E
  rcases hA.eq_or_lt with hzero | hpos
  · have hQ : Q = 0 := by
      by_contra hQ
      have h := hdual ((E+1)/(2*Q))
      have he : 2*((E+1)/(2*Q))*Q = E+1 := by field_simp
      rw [← hzero, mul_zero, add_zero, he] at h
      linarith only [h]
    rw [hQ, ← hzero]
    simp
  · have h := hdual (Q/A)
    have he : (Q/A)^2*A = Q^2/A := by field_simp [ne_of_gt hpos]
    have hl : 2*(Q/A)*Q = 2*(Q^2/A) := by ring
    rw [he, hl] at h
    have hd : Q^2/A ≤ E := by linarith only [h]
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hd

theorem abs_ccmActualHeadSignedMomentLocalCharge_le_sqrt
    (T : ℝ) (N : ℕ) (s : Set ℝ) :
    |ccmActualHeadSignedMomentLocalCharge T N s| ≤
      Real.sqrt (ccmGammaSignedMomentLocalCapacity s)*
        Real.sqrt (ccmActualHeadSignedMomentLocalEnergy T N s) := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (ccmGammaSignedMomentLocalCapacity_nonneg s),
    Real.sq_sqrt (ccmActualHeadSignedMomentLocalEnergy_nonneg T N s)]
  exact sq_ccmActualHeadSignedMomentLocalCharge_le_capacity T N s

private theorem integral_abs_window (R : NNReal) :
    (∫ r in Icc (-(R : ℝ)) (R : ℝ), |r|) = (R : ℝ)^2 := by
  let ρ : ℝ := R
  have hρ : 0 ≤ ρ := R.2
  change (∫ r in Icc (-ρ) ρ, |r|) = ρ^2
  have hn : -ρ ≤ 0 := neg_nonpos.mpr hρ
  have hi (a b : ℝ) : IntervalIntegrable (fun r : ℝ => |r|) volume a b :=
    continuous_abs.intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_trans hn hρ),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-ρ) 0) (hi 0 ρ)]
  have hl : (∫ r in (-ρ)..0, |r|) = ∫ r in (-ρ)..0, -r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hn] at hr
    exact abs_of_nonpos hr.2
  have hr : (∫ r in (0 : ℝ)..ρ, |r|) = ∫ r in (0 : ℝ)..ρ, r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hρ] at hr
    exact abs_of_nonneg hr.1
  rw [hl, hr, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

/-- The singular Gamma kernel has quadratically vanishing local moment capacity. -/
theorem ccmGammaSignedMomentLocalCapacity_window_le_sq (R : NNReal) :
    ccmGammaSignedMomentLocalCapacity (Icc (-(R : ℝ)) (R : ℝ)) ≤ (R : ℝ)^2 := by
  rw [← integral_abs_window R]
  exact integral_mono (integrable_ccmGammaSignedMomentCapacityDensity.restrict)
    (continuous_abs.continuousOn.integrableOn_Icc)
    ccmGammaSignedMomentCapacityDensity_le_abs

theorem abs_ccmActualHeadSignedMomentLocalCharge_window_le_radius
    (T : ℝ) (N : ℕ) (R : NNReal) :
    |ccmActualHeadSignedMomentLocalCharge T N (Icc (-(R : ℝ)) (R : ℝ))| ≤
      (R : ℝ)*Real.sqrt (ccmActualHeadSignedMomentLocalEnergy T N (Icc (-(R : ℝ)) (R : ℝ))) := by
  apply (abs_ccmActualHeadSignedMomentLocalCharge_le_sqrt T N _).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ Real.sqrt ((R : ℝ)^2) := Real.sqrt_le_sqrt (ccmGammaSignedMomentLocalCapacity_window_le_sq R)
    _ = (R : ℝ) := Real.sqrt_sq R.2

theorem ccmActualHeadSignedMomentCharge_eq_window_add_tail
    (T : ℝ) (N : ℕ) (R : NNReal) :
    ccmActualHeadSignedMomentCharge T N =
      ccmActualHeadSignedMomentLocalCharge T N (Icc (-(R : ℝ)) (R : ℝ)) +
        ccmActualHeadSignedMomentLocalCharge T N (Icc (-(R : ℝ)) (R : ℝ))ᶜ :=
  (integral_add_compl measurableSet_Icc (integrable_ccmActualHeadSignedMoment_displacement T N)).symm

theorem ccmActualHeadSignedMomentGammaEnergy_eq_window_add_tail
    (T : ℝ) (N : ℕ) (R : NNReal) :
    ccmActualHeadSignedMomentGammaEnergy T N =
      ccmActualHeadSignedMomentLocalEnergy T N (Icc (-(R : ℝ)) (R : ℝ)) +
        ccmActualHeadSignedMomentLocalEnergy T N (Icc (-(R : ℝ)) (R : ℝ))ᶜ :=
  (integral_add_compl measurableSet_Icc (integrable_ccmActualHeadSignedMomentGammaDensity T N)).symm

/-- A radius factor controls concentrated energy; only the outer tail pays global capacity. -/
theorem abs_ccmActualHeadSignedMomentCharge_le_local_energy_tail
    (T : ℝ) (N : ℕ) (R : NNReal) :
    |ccmActualHeadSignedMomentCharge T N| ≤
      (R : ℝ)*Real.sqrt (ccmActualHeadSignedMomentLocalEnergy T N (Icc (-(R : ℝ)) (R : ℝ))) +
        Real.sqrt (ccmGammaSignedMomentLocalCapacity (Icc (-(R : ℝ)) (R : ℝ))ᶜ)*
          Real.sqrt (ccmActualHeadSignedMomentLocalEnergy T N (Icc (-(R : ℝ)) (R : ℝ))ᶜ) := by
  rw [ccmActualHeadSignedMomentCharge_eq_window_add_tail T N R]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_ccmActualHeadSignedMomentLocalCharge_window_le_radius T N R)
    (abs_ccmActualHeadSignedMomentLocalCharge_le_sqrt T N _))

end RHTower
