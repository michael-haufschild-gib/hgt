import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEventHorizonThirdMassAIMEAntialignment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEHorizonReciprocity

/-!
# Moving-horizon/AIME temporal optical triangle

The physical moving-event-horizon third mass jet is compared exactly with the causal Duhamel
horizon-gain imbalance.  A positive radial-to-temporal susceptibility shows that these channels
reinforce off line, while HC64 supplies their unique opposite chiral AIME-kernel channel.

`[NEW] [THIRD-ORDER MASS JET] [AIME HORIZON HISTORY] [OPTICAL TRIANGLE] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Signed flux-normalized AIME horizon-history gain defect on an Xi fibre. -/
def d4BMXiAIMEHorizonGainDefect (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4AIMEHorizonGainPlus n (xiSpectralPoint q) -
    d4AIMEHorizonGainMinus n (xiSpectralPoint q)

theorem normSq_d4AIMEHorizonDenominatorPlus_xi_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < Complex.normSq (d4AIMEHorizonDenominatorPlus n (xiSpectralPoint q)) := by
  rw [normSq_d4AIMEHorizonDenominatorPlus]
  nlinarith [sq_pos_of_ne_zero
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)]

theorem normSq_d4AIMEHorizonDenominatorMinus_xi_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < Complex.normSq (d4AIMEHorizonDenominatorMinus n (xiSpectralPoint q)) := by
  rw [normSq_d4AIMEHorizonDenominatorMinus]
  nlinarith [sq_pos_of_ne_zero
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)]

/-- Positive radial-to-temporal coefficient comparing moving-horizon third mass response with
the flux-normalized AIME Duhamel gain defect. -/
def d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4BMXiEventHorizonThirdMassReflectionSusceptibility q *
      (Complex.normSq (d4AIMEHorizonDenominatorPlus n (xiSpectralPoint q)) *
        Complex.normSq (d4AIMEHorizonDenominatorMinus n (xiSpectralPoint q))) /
    (8 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n)

theorem d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q := by
  unfold d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility
  apply div_pos
  · exact mul_pos (d4BMXiEventHorizonThirdMassReflectionSusceptibility_pos q)
      (mul_pos (normSq_d4AIMEHorizonDenominatorPlus_xi_pos n q)
        (normSq_d4AIMEHorizonDenominatorMinus_xi_pos n q))
  · unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
    positivity

/-- Exact radial-to-temporal optical identity for the concrete cubic mass-memory channels. -/
theorem d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassParityJetDefect q =
      d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q *
        d4BMXiAIMEHorizonGainDefect n q := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq]
  unfold d4BMXiAIMEHorizonGainDefect
  rw [d4AIMEHorizonGain_sub_mirror n (xiSpectralPoint q)
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q),
    xiSpectralPoint_im_eq]
  unfold d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility
  have hp : Complex.normSq
      (d4AIMEHorizonDenominatorPlus n (xiSpectralPoint q)) ≠ 0 :=
    ne_of_gt (normSq_d4AIMEHorizonDenominatorPlus_xi_pos n q)
  have hm : Complex.normSq
      (d4AIMEHorizonDenominatorMinus n (xiSpectralPoint q)) ≠ 0 :=
    ne_of_gt (normSq_d4AIMEHorizonDenominatorMinus_xi_pos n q)
  have hd : thetaCuspHawkingTopologicalBlackHoleConformalDecay n ≠ 0 := by
    unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
    positivity
  field_simp [hp, hm, hd]
  ring

/-- Temporal AIME gain is reciprocal exactly at critical-line incidence. -/
theorem d4BMXiAIMEHorizonGainDefect_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiAIMEHorizonGainDefect n q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  unfold d4BMXiAIMEHorizonGainDefect
  rw [sub_eq_zero,
    xi_d4AIMEHorizonGain_eq_mirror_iff,
    xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- Off line, the moving-horizon radial third mass response and temporal horizon-history
imbalance strictly reinforce. -/
theorem d4BMXiEventHorizonThirdMassParityJetDefect_mul_horizonGain_pos_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiEventHorizonThirdMassParityJetDefect q *
      d4BMXiAIMEHorizonGainDefect n q := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain]
  have hs := d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility_pos n q
  have hg : d4BMXiAIMEHorizonGainDefect n q ≠ 0 :=
    (not_congr (d4BMXiAIMEHorizonGainDefect_eq_zero_iff n q)).2 htilt
  calc
    d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q *
          d4BMXiAIMEHorizonGainDefect n q *
        d4BMXiAIMEHorizonGainDefect n q =
      d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q *
        d4BMXiAIMEHorizonGainDefect n q ^ (2 : ℕ) := by ring
    _ > 0 := mul_pos hs (sq_pos_of_ne_zero hg)

/-- Exact three-channel optical balance: normalized temporal horizon gain plus the uniquely
normalized chiral AIME kernel cancels identically. -/
theorem d4BMXiAIMEHorizonGainChiralKernel_opticalTriangle
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q *
        d4BMXiAIMEHorizonGainDefect n q +
      d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q *
        d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 := by
  rw [← d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain,
    d4BMXiEventHorizonThirdMassParityJetDefect_eq_neg_susceptibility_mul_AIME]
  ring

/-- Off line, HC64's positive chiral susceptibility is the unique coefficient closing the
radial--temporal--chiral optical triangle. -/
theorem d4BMXiAIMEHorizonGain_add_coefficient_mul_chiralKernel_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (coefficient : ℝ) :
    d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility n q *
          d4BMXiAIMEHorizonGainDefect n q +
        coefficient * d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 ↔
      coefficient = d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q := by
  have hbase := d4BMXiAIMEHorizonGainChiralKernel_opticalTriangle n q
  have hA : d4BMXiThetaMirrorAIMEChiralKernelDefect q ≠ 0 :=
    (d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).2 htilt
  constructor
  · intro h
    have hfactor :
        (coefficient - d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q) *
          d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 := by
      linear_combination h - hbase
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hA)
  · intro h
    rw [h]
    exact hbase

/-- Universal extinction of the causal AIME horizon-gain defect at any fixed QNM level is RH. -/
theorem forall_d4BMXiAIMEHorizonGainDefect_eq_zero_iff_rh
    (n : ℕ) :
    (∀ q : XiZeroCopy, d4BMXiAIMEHorizonGainDefect n q = 0) ↔
      RiemannHypothesis := by
  rw [← forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh]
  constructor
  · intro hall q
    rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain,
      hall q, mul_zero]
  · intro hall q
    have h := hall q
    rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq_susceptibility_mul_horizonGain,
      mul_eq_zero] at h
    exact h.resolve_left
      (ne_of_gt (d4BMXiEventHorizonThirdMassToAIMEHorizonGainSusceptibility_pos n q))

end

end RHTower
