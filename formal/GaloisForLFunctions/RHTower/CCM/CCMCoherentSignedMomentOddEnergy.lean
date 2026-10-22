import GaloisForLFunctions.RHTower.CCM.CCMCoherentSignedMomentArithmeticAction

/-!
# Only displacement asymmetry carries the moment charge

Reflection splits the literal prime-plus-terminal moment into even and odd
parts. The signed displacement charge sees only the odd part. Reciprocal-Gamma
energy splits exactly, so removing the even part strengthens the charge bound
without changing the arithmetic observable or assuming cancellation.
-/

noncomputable section
open MeasureTheory Filter

namespace RHTower

def ccmActualHeadSignedMomentOddPart (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (ccmActualHeadMidpointSignedMoment T N r-ccmActualHeadMidpointSignedMoment T N (-r))/2

def ccmActualHeadSignedMomentEvenPart (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (ccmActualHeadMidpointSignedMoment T N r+ccmActualHeadMidpointSignedMoment T N (-r))/2

theorem ccmActualHeadSignedMomentOddPart_neg (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadSignedMomentOddPart T N (-r) = -ccmActualHeadSignedMomentOddPart T N r := by
  simp only [ccmActualHeadSignedMomentOddPart, neg_neg]
  ring

theorem ccmActualHeadSignedMomentEvenPart_neg (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadSignedMomentEvenPart T N (-r) = ccmActualHeadSignedMomentEvenPart T N r := by
  simp only [ccmActualHeadSignedMomentEvenPart, neg_neg]
  ring

private theorem memLp_reflection (T : ℝ) (N : ℕ) (ε : ℝ) :
    MemLp (fun r : ℝ =>
      ((ccmActualHeadMidpointSignedMoment T N r+ε*ccmActualHeadMidpointSignedMoment T N (-r))/2)*
        Real.sqrt (ccmGammaHigherBinetDualDensity |r|)) 2 := by
  have h := memLp_ccmActualHeadSignedMoment_mul_sqrtDual T N
  have hn := h.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  refine ((h.add (hn.const_mul ε)).const_mul (1/2 : ℝ)).ae_eq (Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply, Function.comp_def, abs_neg]
  ring

private theorem integrable_reflection (T : ℝ) (N : ℕ) (ε : ℝ) :
    Integrable (fun r : ℝ =>
      ((ccmActualHeadMidpointSignedMoment T N r+ε*ccmActualHeadMidpointSignedMoment T N (-r))/2)^2*
        ccmGammaHigherBinetDualDensity |r|) := by
  have h := (memLp_reflection T N ε).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  refine h.congr (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))]

theorem integrable_ccmActualHeadSignedMomentOddGammaDensity (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => (ccmActualHeadSignedMomentOddPart T N r)^2*
      ccmGammaHigherBinetDualDensity |r|) := by
  simpa only [ccmActualHeadSignedMomentOddPart, neg_one_mul, ← sub_eq_add_neg] using
    integrable_reflection T N (-1)

theorem integrable_ccmActualHeadSignedMomentEvenGammaDensity (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => (ccmActualHeadSignedMomentEvenPart T N r)^2*
      ccmGammaHigherBinetDualDensity |r|) := by
  simpa only [ccmActualHeadSignedMomentEvenPart, one_mul] using integrable_reflection T N 1

def ccmActualHeadSignedMomentOddGammaEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, (ccmActualHeadSignedMomentOddPart T N r)^2*ccmGammaHigherBinetDualDensity |r|

def ccmActualHeadSignedMomentEvenGammaEnergy (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, (ccmActualHeadSignedMomentEvenPart T N r)^2*ccmGammaHigherBinetDualDensity |r|

theorem ccmActualHeadSignedMomentOddGammaEnergy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmActualHeadSignedMomentOddGammaEnergy T N :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadSignedMomentEvenGammaEnergy_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmActualHeadSignedMomentEvenGammaEnergy T N :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

/-- Reflection gives an exact orthogonal energy decomposition. -/
theorem ccmActualHeadSignedMomentGammaEnergy_eq_odd_add_even (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentGammaEnergy T N =
      ccmActualHeadSignedMomentOddGammaEnergy T N+ccmActualHeadSignedMomentEvenGammaEnergy T N := by
  have h := integrable_ccmActualHeadSignedMomentGammaDensity T N
  have hn : Integrable (fun r : ℝ => (ccmActualHeadMidpointSignedMoment T N (-r))^2*
      ccmGammaHigherBinetDualDensity |r|) := by
    simpa only [abs_neg] using h.comp_neg
  unfold ccmActualHeadSignedMomentOddGammaEnergy ccmActualHeadSignedMomentEvenGammaEnergy
  rw [← integral_add (integrable_ccmActualHeadSignedMomentOddGammaDensity T N)
    (integrable_ccmActualHeadSignedMomentEvenGammaDensity T N)]
  have he (r : ℝ) : (ccmActualHeadSignedMomentOddPart T N r)^2*ccmGammaHigherBinetDualDensity |r| +
      (ccmActualHeadSignedMomentEvenPart T N r)^2*ccmGammaHigherBinetDualDensity |r| =
      ((ccmActualHeadMidpointSignedMoment T N r)^2*ccmGammaHigherBinetDualDensity |r| +
        (ccmActualHeadMidpointSignedMoment T N (-r))^2*ccmGammaHigherBinetDualDensity |r|)/2 := by
    unfold ccmActualHeadSignedMomentOddPart ccmActualHeadSignedMomentEvenPart
    ring
  simp_rw [he]
  rw [integral_div, integral_add h hn]
  have hs := integral_neg_eq_self
    (fun r : ℝ => (ccmActualHeadMidpointSignedMoment T N r)^2*ccmGammaHigherBinetDualDensity |r|) volume
  simp only [abs_neg] at hs
  rw [hs]
  unfold ccmActualHeadSignedMomentGammaEnergy
  ring

theorem ccmActualHeadSignedMomentOddGammaEnergy_le_energy (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentOddGammaEnergy T N ≤ ccmActualHeadSignedMomentGammaEnergy T N := by
  rw [ccmActualHeadSignedMomentGammaEnergy_eq_odd_add_even]
  exact le_add_of_nonneg_right (ccmActualHeadSignedMomentEvenGammaEnergy_nonneg T N)

private theorem reflected_charge_integrable (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => r*ccmActualHeadMidpointSignedMoment T N (-r)) := by
  have h := (integrable_ccmActualHeadSignedMoment_displacement T N).comp_neg.neg
  refine h.congr (Eventually.of_forall fun r => ?_)
  change -((-r)*ccmActualHeadMidpointSignedMoment T N (-r)) =
    r*ccmActualHeadMidpointSignedMoment T N (-r)
  ring

theorem integrable_ccmActualHeadSignedMomentOdd_displacement (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => r*ccmActualHeadSignedMomentOddPart T N r) := by
  have h := ((integrable_ccmActualHeadSignedMoment_displacement T N).sub
    (reflected_charge_integrable T N)).div_const 2
  refine h.congr (Eventually.of_forall fun r => ?_)
  dsimp only [ccmActualHeadSignedMomentOddPart, Pi.sub_apply]
  ring

/-- The even transport component contributes exactly zero to the arithmetic charge. -/
theorem ccmActualHeadSignedMomentCharge_eq_odd_charge (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentCharge T N = ∫ r : ℝ, r*ccmActualHeadSignedMomentOddPart T N r := by
  have hs := integral_neg_eq_self
    (fun r : ℝ => r*ccmActualHeadMidpointSignedMoment T N r) volume
  simp only [neg_mul, integral_neg] at hs
  have he (r : ℝ) : r*ccmActualHeadSignedMomentOddPart T N r =
      (r*ccmActualHeadMidpointSignedMoment T N r-r*ccmActualHeadMidpointSignedMoment T N (-r))/2 := by
    unfold ccmActualHeadSignedMomentOddPart
    ring
  simp_rw [he]
  rw [integral_div, integral_sub (integrable_ccmActualHeadSignedMoment_displacement T N)
    (reflected_charge_integrable T N)]
  unfold ccmActualHeadSignedMomentCharge
  linarith only [hs]

theorem ccmActualHeadSignedMomentCharge_odd_dual_bound (T : ℝ) (N : ℕ) (t : ℝ) :
    2*t*ccmActualHeadSignedMomentCharge T N ≤
      ccmActualHeadSignedMomentOddGammaEnergy T N+t^2*ccmGammaSignedMomentCapacity := by
  have hp (r : ℝ) : 2*t*(r*ccmActualHeadSignedMomentOddPart T N r) ≤
      (ccmActualHeadSignedMomentOddPart T N r)^2*ccmGammaHigherBinetDualDensity |r| +
        t^2*(r^2*ccmGammaHigherBinetModeDensity |r|) := by
    have h := sq_nonneg (ccmActualHeadSignedMomentOddPart T N r *
      Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-t*r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|))
    rw [ccmGammaSignedMomentWeightedSquare] at h
    linarith only [h]
  have h := integral_mono ((integrable_ccmActualHeadSignedMomentOdd_displacement T N).const_mul (2*t))
    ((integrable_ccmActualHeadSignedMomentOddGammaDensity T N).add
      (integrable_ccmGammaSignedMomentCapacityDensity.const_mul (t^2))) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_ccmActualHeadSignedMomentOddGammaDensity T N)
    (integrable_ccmGammaSignedMomentCapacityDensity.const_mul (t^2)), integral_const_mul,
    integral_const_mul, ← ccmActualHeadSignedMomentCharge_eq_odd_charge] at h
  exact h

/-- Only the antisymmetric transport energy is required to control the signed remainder action. -/
theorem sq_ccmActualHeadSignedMomentCharge_le_odd_energy (T : ℝ) (N : ℕ) :
    (ccmActualHeadSignedMomentCharge T N)^2 ≤
      ccmGammaSignedMomentCapacity*ccmActualHeadSignedMomentOddGammaEnergy T N := by
  let Q := ccmActualHeadSignedMomentCharge T N
  let A := ccmGammaSignedMomentCapacity
  have hA : 0 < A := ccmGammaSignedMomentCapacity_pos
  have h := ccmActualHeadSignedMomentCharge_odd_dual_bound T N (Q/A)
  change 2*(Q/A)*Q ≤ ccmActualHeadSignedMomentOddGammaEnergy T N+(Q/A)^2*A at h
  have he : (Q/A)^2*A = Q^2/A := by field_simp [ne_of_gt hA]
  have hl : 2*(Q/A)*Q = 2*(Q^2/A) := by ring
  rw [he, hl] at h
  have hd : Q^2/A ≤ ccmActualHeadSignedMomentOddGammaEnergy T N := by linarith only [h]
  simpa only [mul_comm] using (div_le_iff₀ hA).mp hd

/-- The physical Chebyshev-Volterra action pays only for displacement asymmetry. -/
theorem sq_ccmActualTimeChebyshevVolterraAction_le_odd_energy (H : NNReal) :
    (2*Real.pi)^2 * (∫ h in (0 : ℝ)..(H : ℝ), h*(1+criticalMellinNormalizedChebyshevError h +
      (1/2 : ℝ)*(∫ u in Set.Ioc (0 : ℝ) h, criticalMellinNormalizedChebyshevError u)))^2 ≤
      ccmGammaSignedMomentCapacity * ccmActualHeadSignedMomentOddGammaEnergy (H : ℝ)
        (Nat.floor (Real.exp (H : ℝ))+1) := by
  have h := sq_ccmActualHeadSignedMomentCharge_le_odd_energy (H : ℝ)
    (Nat.floor (Real.exp (H : ℝ))+1)
  rw [ccmActualTimeSignedMomentCharge_eq_chebyshevVolterra, mul_pow] at h
  exact h

end RHTower
