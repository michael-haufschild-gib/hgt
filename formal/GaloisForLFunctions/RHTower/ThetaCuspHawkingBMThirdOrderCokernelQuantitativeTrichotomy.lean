import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMThirdOrderCokernelNecessity

/-!
# Quantitative third-order Einstein--Teukolsky cokernel trichotomy

Critical-line unit BM incidence fixes the aggregate projection of the three non-AIME third-order
`++-` channels to the negative AIME numerator.  Triangle inequality upgrades the corpus's
qualitative nonexact-channel obstruction to a sharp norm budget: their projected norms sum to at
least the AIME norm, so one channel carries at least one third of it.

The constant `1/3` is optimal for three unconstrained complex channels.  For a nonzero absorbed
seed, the channel attaining this lower bound is also outside the range of the linearized
Einstein--Teukolsky operator, since a left resonant state annihilates that range.  Thus a literal
gauge-fixed third-order computation must exhibit a quantitatively large cokernel class in the
charge-orthogonal stationary cascade, second-harmonic cascade, or direct third variation.

`[NEW] [QUANTITATIVE COKERNEL] [SHARP ONE-THIRD] [HB BURDEN REDUCTION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Three complex channels summing to a negative target have aggregate norm at least the target
norm. -/
theorem d4ThreeChannelResonantNormBudget
    (a b c target : ℂ) (hsum : a + b + c = -target) :
    ‖target‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖target‖ = ‖-target‖ := by rw [norm_neg]
    _ = ‖a + b + c‖ := congrArg norm hsum.symm
    _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = ‖a‖ + ‖b‖ + ‖c‖ := rfl

/-- Sharp three-channel pigeonhole law: one channel carries at least one third of the target
norm. -/
theorem d4ThreeChannelResonantNormPigeonhole
    (a b c target : ℂ) (hsum : a + b + c = -target) :
    ‖target‖ / 3 ≤ ‖a‖ ∨ ‖target‖ / 3 ≤ ‖b‖ ∨ ‖target‖ / 3 ≤ ‖c‖ := by
  by_contra h
  push Not at h
  have hbudget := d4ThreeChannelResonantNormBudget a b c target hsum
  linarith

/-- The factor `1/3` is optimal: equal aligned channels attain it simultaneously. -/
theorem d4ThreeChannelResonantNormPigeonhole_sharp (target : ℂ) :
    ∃ a b c : ℂ,
      a + b + c = -target ∧
      ‖a‖ = ‖target‖ / 3 ∧ ‖b‖ = ‖target‖ / 3 ∧ ‖c‖ = ‖target‖ / 3 := by
  refine ⟨-(1 / 3 : ℂ) * target, -(1 / 3 : ℂ) * target,
    -(1 / 3 : ℂ) * target, ?_, ?_, ?_, ?_⟩
  · ring
  all_goals
    rw [norm_mul, norm_neg]
    norm_num
    ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private lemma largeResonantProjection_not_linearizedExact
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0) (source : V) (target : ℂ)
    (htarget : target ≠ 0) (hlarge : ‖target‖ / 3 ≤ ‖ell source‖) :
    ¬ ∃ gauge, source = L gauge := by
  rintro ⟨gauge, rfl⟩
  rw [hleft] at hlarge
  simp only [norm_zero] at hlarge
  have hpos : 0 < ‖target‖ := norm_pos_iff.mpr htarget
  linarith

/-- Actual critical-line BM incidence forces total non-AIME resonant norm at least the exact AIME
norm. -/
theorem d4EinsteinThirdOrder_nonAIMEProjection_normBudget_of_unitBMTarget_of_criticalLine
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    ‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ ≤
      ‖ell (B hPlus (hPlusMinus - P hPlusMinus))‖ +
      ‖ell (B hMinus hPlusPlus)‖ +
      ‖ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)‖ := by
  have hsum :=
    d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
      ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
  apply d4ThreeChannelResonantNormBudget
    (ell (B hPlus (hPlusMinus - P hPlusMinus)))
    (ell (B hMinus hPlusPlus))
    (ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
    (d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q))
  simpa only [map_add] using hsum

/-- Quantitative cokernel trichotomy for the actual three non-AIME `++-` Einstein channels.
One channel carries at least one third of exact AIME norm and is not linearized-operator exact. -/
theorem d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_forces_quantitative_nonexact_channel
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 ≤
        ‖ell (B hPlus (hPlusMinus - P hPlusMinus))‖ ∧
      ¬ ∃ gauge, B hPlus (hPlusMinus - P hPlusMinus) = L gauge) ∨
    (‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 ≤
        ‖ell (B hMinus hPlusPlus)‖ ∧
      ¬ ∃ gauge, B hMinus hPlusPlus = L gauge) ∨
    (‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 ≤
        ‖ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)‖ ∧
      ¬ ∃ gauge,
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus = L gauge) := by
  let orthogonal := B hPlus (hPlusMinus - P hPlusMinus)
  let secondHarmonic := B hMinus hPlusPlus
  let direct := d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus
  let aime := d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)
  have hsum : ell orthogonal + ell secondHarmonic + ell direct = -aime := by
    have h :=
      d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
        ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
    simpa only [orthogonal, secondHarmonic, direct, aime, map_add] using h
  have htarget : aime ≠ 0 :=
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr hamplitude
  rcases d4ThreeChannelResonantNormPigeonhole
      (ell orthogonal) (ell secondHarmonic) (ell direct) aime hsum with
      hOrthogonal | hSecondHarmonic | hDirect
  · left
    exact ⟨hOrthogonal,
      largeResonantProjection_not_linearizedExact L ell hleft orthogonal aime
        htarget hOrthogonal⟩
  · right; left
    exact ⟨hSecondHarmonic,
      largeResonantProjection_not_linearizedExact L ell hleft secondHarmonic aime
        htarget hSecondHarmonic⟩
  · right; right
    exact ⟨hDirect,
      largeResonantProjection_not_linearizedExact L ell hleft direct aime
        htarget hDirect⟩

end

end RHTower
