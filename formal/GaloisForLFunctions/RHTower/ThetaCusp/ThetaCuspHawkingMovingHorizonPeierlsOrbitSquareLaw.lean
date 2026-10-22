import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCausalOpticalGainSquareParityObstruction

/-!
# Moving-horizon/Peierls reflected-orbit square law

The correct polarized plus-plus/minus-minus BM causal-current candidate has a reflection-orbit sum equal to a
strictly negative square of the moving-event-horizon third-mass defect.

`[NEW] [PEIERLS POLARIZATION] [THIRD-MASS MEMORY] [NEGATIVE SQUARE] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Reflected orbit sum of the unit-carrier BM Peierls polarized cut at the canonical radial
midpoint. -/
def d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut
    (n : ℕ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n q (1 / 2) +
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut n
      (xiZeroCopyReflectEquiv q) (1 / 2)

theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -2 * (d4BMXiMixedHorizonAngularCausalOpticalDensity q : ℂ) *
        (8 * (n : ℂ) + 5) := by
  unfold d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add
    n q (by norm_num) (by norm_num)]
  rfl

/-- Positive coefficient converting squared signed AIME gain to the reflected Peierls orbit cut. -/
def d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * (8 * (n : ℝ) + 5) *
    d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q

theorem d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility n q := by
  unfold d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility
  exact mul_pos (mul_pos (by norm_num) (by positivity))
    (d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility_pos n q)

/-- Exact temporal form of the polarized causal-current orbit: a negative positive-coefficient
square of the signed AIME horizon-history gain. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_gain_sq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -((d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility n q *
        d4BMXiAIMEHorizonGainDefect n q ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_density,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_susceptibility_mul_gain_sq]
  unfold d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility
  push_cast
  ring

/-- Positive coefficient converting squared moving-horizon third-mass defect to the reflected
Peierls orbit cut. -/
def d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility n q /
    d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q ^ (2 : ℕ)

theorem d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility n q := by
  unfold d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility
  exact div_pos
    (d4BMXiAIMEHorizonGainSquareToPeierlsOrbitSusceptibility_pos n q)
    (sq_pos_of_pos
      (d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility_pos n q))

/-- Exact radial form of the polarized causal-current orbit: a negative positive-coefficient square
of the physical moving-event-horizon third-mass defect. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_thirdMass_sq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q =
      -((d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility n q *
        d4BMXiEventHorizonThirdMassParityJetDefect q ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_gain_sq,
    d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain]
  unfold d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility
  have hs : d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q ≠ 0 :=
    ne_of_gt (d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility_pos n q)
  push_cast
  field_simp [hs]

/-- The reflected polarized causal-current orbit has nonpositive real orientation on every Xi
fibre. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonpos
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q).re ≤ 0 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_thirdMass_sq]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  exact mul_nonneg
    (le_of_lt (d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility_pos n q))
    (mul_self_nonneg _)

/-- Every tilted Xi fibre makes the reflected polarized causal-current orbit strictly negative. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_neg_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q).re < 0 := by
  rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_thirdMass_sq]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  exact mul_pos
    (d4BMXiEventHorizonThirdMassSquareToPeierlsOrbitSusceptibility_pos n q)
    (mul_self_pos.mpr
      ((d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).not.mpr htilt))

/-- Nonnegative orientation in the opposite convention is possible exactly on the critical line. -/
theorem d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff
    (n : ℕ) (q : XiZeroCopy) :
    0 ≤ (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q).re ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hnonneg
    by_contra htilt
    have hneg :=
      d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_neg_of_tilt
        n q htilt
    linarith
  · intro hline
    rw [d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_eq_neg_thirdMass_sq,
      (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2 hline]
    simp

/-- Universal nonnegative reflected Peierls-orbit orientation at one fixed QNM level is RH. -/
theorem forall_d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy,
      0 ≤ (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut n q).re) ↔
      RiemannHypothesis := by
  rw [← forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh]
  constructor
  · intro hall q
    apply (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2
    exact (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff
      n q).1 (hall q)
  · intro hall q
    apply (d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedOrbitCut_re_nonneg_iff
      n q).2
    exact (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).1 (hall q)

end

end RHTower
