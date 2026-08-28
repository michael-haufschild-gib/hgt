import GaloisForLFunctions.RHTower.ThetaCuspHawkingMovingHorizonAIMETemporalOpticalTriangle
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicCarrierNormalizedReflectionObstruction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer
import GaloisForLFunctions.RHTower.ThetaCuspHawkingDarbouxHorizonPhaseMixingOpticalLaw

/-!
# Mixed-horizon causal optical square law

The causal optical Gram loses the signed horizontal orientation carried by the AIME horizon-history
defect.  After removal of its nonzero radial factors it is exactly a positive coefficient times the
square of that defect, hence reflection-even rather than reflection-odd.

`[NEW] [CAUSAL CUT] [OPTICAL GRAM] [REFLECTION PARITY] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Angular density inside the actual mixed-horizon causal optical section. -/
def d4BMXiMixedHorizonAngularCausalOpticalDensity (q : XiZeroCopy) : ℝ :=
  Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q)

theorem d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt
    (q : XiZeroCopy) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity q =
      (q.1 : ℂ).im ^ 2 * (1 - 2 * (q.1 : ℂ).re) ^ 2 := by
  exact normSq_d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_tilt q

theorem d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  unfold d4BMXiMixedHorizonAngularCausalOpticalDensity
  rw [Complex.normSq_eq_zero,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff]

theorem d4BMXiMixedHorizonAngularCausalOpticalDensity_reflect
    (q : XiZeroCopy) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity
        (xiZeroCopyReflectEquiv q) =
      d4BMXiMixedHorizonAngularCausalOpticalDensity q := by
  unfold d4BMXiMixedHorizonAngularCausalOpticalDensity
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]

/-- The optical Gram separates into angular density and squared horizon response. -/
theorem normSq_d4BMMixedHorizonOpticalSourceProjection_eq_angularDensity_mul_response
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q) =
      d4BMXiMixedHorizonAngularCausalOpticalDensity q *
        Complex.normSq
          ((d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
            amplitude orthogonalMixing q) 0) := by
  rw [d4BMMixedHorizonOpticalSourceProjection,
    Complex.normSq_mul]
  rfl

/-- The concrete Xi-fibre causal section is radial monodromy times angular density times the
squared physical horizon response. -/
theorem d4BMXiMixedHorizonCausalOpticalSection_eq_monodromy_mul_angularDensity_mul_response
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q =
      d4BMXiMixedHorizonComplexMonodromyJump n k q *
        ((d4BMXiMixedHorizonAngularCausalOpticalDensity q *
          Complex.normSq
            ((d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
              amplitude orthogonalMixing q) 0) : ℝ) : ℂ) := by
  rw [d4BMXiMixedHorizonCausalOpticalSection,
    normSq_d4BMMixedHorizonOpticalSourceProjection_eq_angularDensity_mul_response]

/-- Positive coefficient converting the square of signed AIME temporal gain into angular causal
optical density. -/
def d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  (xiSpectralPoint q).re ^ 2 *
      (Complex.normSq (d4AIMEHorizonDenominatorPlus n (xiSpectralPoint q)) *
        Complex.normSq (d4AIMEHorizonDenominatorMinus n (xiSpectralPoint q))) ^ 2 /
    (64 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n ^ 2)

theorem d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility_pos
    (n : ℕ) (q : XiZeroCopy) :
    0 < d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q := by
  unfold d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility
  apply div_pos
  · apply mul_pos
    · exact sq_pos_of_ne_zero
        (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)
    · exact sq_pos_of_ne_zero (mul_ne_zero
        (ne_of_gt (normSq_d4AIMEHorizonDenominatorPlus_xi_pos n q))
        (ne_of_gt (normSq_d4AIMEHorizonDenominatorMinus_xi_pos n q)))
  · unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
    positivity

/-- Exact order-two incidence: causal optical density is positive susceptibility times squared
signed AIME horizon-history gain. -/
theorem d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_susceptibility_mul_gain_sq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity q =
      d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q *
        d4BMXiAIMEHorizonGainDefect n q ^ 2 := by
  rw [d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_tilt]
  unfold d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility
    d4BMXiAIMEHorizonGainDefect
  rw [xiSpectralPoint_re_eq]
  rw [d4AIMEHorizonGain_sub_mirror n (xiSpectralPoint q)
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q),
    xiSpectralPoint_im_eq]
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

/-- Full concrete causal optical section inherits the exact AIME square law. -/
theorem d4BMXiMixedHorizonCausalOpticalSection_eq_monodromy_mul_gainSquare_response
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q =
      d4BMXiMixedHorizonComplexMonodromyJump n k q *
        (((d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q *
          d4BMXiAIMEHorizonGainDefect n q ^ 2) *
          Complex.normSq
            ((d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
              amplitude orthogonalMixing q) 0) : ℝ) : ℂ) := by
  rw [d4BMXiMixedHorizonCausalOpticalSection_eq_monodromy_mul_angularDensity_mul_response,
    d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_susceptibility_mul_gain_sq]

/-- Functional-equation reflection reverses signed AIME horizon-history gain. -/
theorem d4BMXiAIMEHorizonGainDefect_reflect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiAIMEHorizonGainDefect n (xiZeroCopyReflectEquiv q) =
      -d4BMXiAIMEHorizonGainDefect n q := by
  unfold d4BMXiAIMEHorizonGainDefect d4AIMEHorizonGainPlus
    d4AIMEHorizonGainMinus
  rw [xiSpectralPoint_reflect,
    normSq_d4AIMEHorizonDenominatorPlus,
    normSq_d4AIMEHorizonDenominatorMinus,
    normSq_d4AIMEHorizonDenominatorPlus,
    normSq_d4AIMEHorizonDenominatorMinus]
  simp only [Complex.neg_re, Complex.neg_im]
  ring

/-- The positive gain-square susceptibility is itself reflection-even. -/
theorem d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility_reflect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n
        (xiZeroCopyReflectEquiv q) =
      d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q := by
  unfold d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility
  rw [xiSpectralPoint_reflect,
    normSq_d4AIMEHorizonDenominatorPlus,
    normSq_d4AIMEHorizonDenominatorMinus,
    normSq_d4AIMEHorizonDenominatorPlus,
    normSq_d4AIMEHorizonDenominatorMinus]
  simp only [Complex.neg_re, Complex.neg_im]
  ring

/-- Canonical scalar that expresses the quadratic causal optical density as a linear multiple of
signed AIME gain on one fibre. Its extra gain factor is forced by the square law. -/
def d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient
    (n : ℕ) (q : XiZeroCopy) : ℝ :=
  d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility n q *
    d4BMXiAIMEHorizonGainDefect n q

theorem d4BMXiAngularOpticalDensity_eq_canonicalLinearizationCoefficient_mul_gain
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity q =
      d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient n q *
        d4BMXiAIMEHorizonGainDefect n q := by
  rw [d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_susceptibility_mul_gain_sq]
  unfold d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient
  ring

/-- The unique off-line linearization coefficient is reflection-odd. -/
theorem d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient_reflect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient n
        (xiZeroCopyReflectEquiv q) =
      -d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient n q := by
  unfold d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient
  rw [d4BMXiAIMEHorizonGainSquareToAngularOpticalSusceptibility_reflect,
    d4BMXiAIMEHorizonGainDefect_reflect]
  ring

/-- Off line, the square law forces one and only one scalar linearization coefficient. -/
theorem d4BMXiAngularOpticalDensity_eq_coefficient_mul_gain_iff
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (coefficient : ℝ) :
    d4BMXiMixedHorizonAngularCausalOpticalDensity q =
        coefficient * d4BMXiAIMEHorizonGainDefect n q ↔
      coefficient =
        d4BMXiAIMEHorizonGainToAngularOpticalLinearizationCoefficient n q := by
  have hgain : d4BMXiAIMEHorizonGainDefect n q ≠ 0 :=
    (d4BMXiAIMEHorizonGainDefect_eq_zero_iff n q).not.mpr htilt
  have hbase :=
    d4BMXiAngularOpticalDensity_eq_canonicalLinearizationCoefficient_mul_gain n q
  constructor
  · intro h
    apply (mul_right_cancel₀ hgain)
    exact h.symm.trans hbase
  · intro h
    rw [h]
    exact hbase

/-- A single reflection-even linear coefficient fits both members of an Xi reflection orbit exactly
on the critical line. -/
theorem d4BMXiAngularOpticalDensity_reflectionEven_linearization_iff
    (n : ℕ) (q : XiZeroCopy) (coefficient : ℝ) :
    (d4BMXiMixedHorizonAngularCausalOpticalDensity q =
          coefficient * d4BMXiAIMEHorizonGainDefect n q ∧
        d4BMXiMixedHorizonAngularCausalOpticalDensity
            (xiZeroCopyReflectEquiv q) =
          coefficient * d4BMXiAIMEHorizonGainDefect n
            (xiZeroCopyReflectEquiv q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiMixedHorizonAngularCausalOpticalDensity_reflect,
    d4BMXiAIMEHorizonGainDefect_reflect]
  constructor
  · rintro ⟨hforward, hreflected⟩
    apply (d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_zero_iff q).mp
    have htwo :
        2 * d4BMXiMixedHorizonAngularCausalOpticalDensity q = 0 := by
      linear_combination hforward + hreflected
    linarith
  · intro hline
    have hdensity :=
      (d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_zero_iff q).2 hline
    have hgain := (d4BMXiAIMEHorizonGainDefect_eq_zero_iff n q).2 hline
    rw [hdensity, hgain]
    simp

/-- A globally reflection-even linear susceptibility between causal optical density and signed AIME
gain exists exactly under RH. -/
theorem exists_reflectionEven_AIMEGain_linearizes_angularCausalOpticalDensity_iff_rh
    (n : ℕ) :
    (∃ coefficient : XiZeroCopy → ℝ,
        (∀ q : XiZeroCopy,
          coefficient (xiZeroCopyReflectEquiv q) = coefficient q) ∧
        ∀ q : XiZeroCopy,
          d4BMXiMixedHorizonAngularCausalOpticalDensity q =
            coefficient q * d4BMXiAIMEHorizonGainDefect n q) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨coefficient, heven, hlinear⟩
    apply (forall_d4BMXiAIMEHorizonGainDefect_eq_zero_iff_rh n).mp
    intro q
    apply (d4BMXiAIMEHorizonGainDefect_eq_zero_iff n q).2
    apply (d4BMXiAngularOpticalDensity_reflectionEven_linearization_iff
      n q (coefficient q)).mp
    refine ⟨hlinear q, ?_⟩
    simpa [heven q] using hlinear (xiZeroCopyReflectEquiv q)
  · intro hrh
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro q
    have hgain := (forall_d4BMXiAIMEHorizonGainDefect_eq_zero_iff_rh n).2 hrh q
    have hline := (d4BMXiAIMEHorizonGainDefect_eq_zero_iff n q).1 hgain
    rw [(d4BMXiMixedHorizonAngularCausalOpticalDensity_eq_zero_iff q).2 hline]
    simp

end

end RHTower
