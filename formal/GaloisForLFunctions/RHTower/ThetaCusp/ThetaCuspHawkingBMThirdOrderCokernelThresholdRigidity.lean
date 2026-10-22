import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelQuantitativeTrichotomy

/-!
# Sharp threshold rigidity of the third-order Einstein--Teukolsky cokernel split

HC45 proves that one of the three non-AIME third-order `++-` channels carries at least one third
of exact AIME resonant norm.  Equality is rigid.  If every channel stays at or below the threshold,
every nested complex triangle inequality is saturated.  Strict convexity forces a common ray,
equal norms force equal channels, and their prescribed sum fixes each value to `-AIME/3`.

Thus critical-line unit BM incidence has exactly two possibilities for a nonzero absorbed seed:
one physical channel strictly exceeds the one-third threshold and is nonexact, or all three
channels are exactly phase-locked at `-AIME/3` and all three are nonexact.  There is no diffuse
subthreshold configuration.

`[NEW] [THRESHOLD RIGIDITY] [EXACT EQUIPARTITION] [COKERNEL DICHOTOMY] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

private theorem eq_of_sameRay_of_norm_eq {x y : ℂ}
    (hray : SameRay ℝ x y) (hnorm : ‖x‖ = ‖y‖) : x = y := by
  rcases hray with hzero | hzero | ⟨r, s, hr, hs, hrs⟩
  · have hy : y = 0 := norm_eq_zero.mp (by simpa [hzero] using hnorm.symm)
    exact hzero.trans hy.symm
  · have hx : x = 0 := norm_eq_zero.mp (by simpa [hzero] using hnorm)
    exact hx.trans hzero.symm
  · by_cases hxnorm : ‖x‖ = 0
    · have hx : x = 0 := norm_eq_zero.mp hxnorm
      have hy : y = 0 := norm_eq_zero.mp (hnorm ▸ hxnorm)
      exact hx.trans hy.symm
    · have hxr : ‖r • x‖ = r * ‖x‖ := by
        rw [norm_smul]
        simp [abs_of_pos hr]
      have hys : ‖s • y‖ = s * ‖y‖ := by
        rw [norm_smul]
        simp [abs_of_pos hs]
      have hrs' : r = s := by
        have hn := congrArg norm hrs
        rw [hxr, hys, ← hnorm] at hn
        exact mul_right_cancel₀ hxnorm hn
      subst hrs'
      exact smul_right_injective ℂ (ne_of_gt hr) hrs

/-- If all three channels are at most the sharp one-third threshold, they are exactly the aligned
equal partition of the prescribed negative target. -/
theorem d4ThreeChannelResonantNormThresholdRigidity
    (a b c target : ℂ) (hsum : a + b + c = -target)
    (ha : ‖a‖ ≤ ‖target‖ / 3)
    (hb : ‖b‖ ≤ ‖target‖ / 3)
    (hc : ‖c‖ ≤ ‖target‖ / 3) :
    a = -target / 3 ∧ b = -target / 3 ∧ c = -target / 3 := by
  have hbudget := d4ThreeChannelResonantNormBudget a b c target hsum
  have hnorma : ‖a‖ = ‖target‖ / 3 := by linarith
  have hnormb : ‖b‖ = ‖target‖ / 3 := by linarith
  have hnormc : ‖c‖ = ‖target‖ / 3 := by linarith
  have htotal : ‖a + b + c‖ = ‖target‖ := by rw [hsum, norm_neg]
  have habLe := norm_add_le a b
  have habcLe := norm_add_le (a + b) c
  have habEq : ‖a + b‖ = ‖a‖ + ‖b‖ := by
    linarith [htotal, habLe, habcLe, hnorma, hnormb, hnormc]
  have habcEq : ‖a + b + c‖ = ‖a + b‖ + ‖c‖ := by
    linarith [htotal, habcLe, habEq, hnorma, hnormb, hnormc]
  have habRay : SameRay ℝ a b := sameRay_iff_norm_add.mpr habEq
  have habcRay : SameRay ℝ (a + b) c := sameRay_iff_norm_add.mpr habcEq
  have hab : a = b := eq_of_sameRay_of_norm_eq habRay (hnorma.trans hnormb.symm)
  have haaRay : SameRay ℝ a (a + a) :=
    (SameRay.refl a).add_right (SameRay.refl a)
  have hacRay : SameRay ℝ a c := by
    rw [← hab] at habcRay
    exact haaRay.trans habcRay (by
      intro hzero
      left
      linear_combination (1 / 2 : ℂ) * hzero)
  have hac : a = c := eq_of_sameRay_of_norm_eq hacRay (hnorma.trans hnormc.symm)
  have haValue : a = -target / 3 := by
    rw [← hab, ← hac] at hsum
    linear_combination (1 / 3 : ℂ) * hsum
  exact ⟨haValue, hab ▸ haValue, hac ▸ haValue⟩

/-- Exact alternative: strict dominance by one channel or unique aligned equipartition. -/
theorem d4ThreeChannelResonantNormThresholdDichotomy
    (a b c target : ℂ) (hsum : a + b + c = -target) :
    (‖target‖ / 3 < ‖a‖ ∨ ‖target‖ / 3 < ‖b‖ ∨ ‖target‖ / 3 < ‖c‖) ∨
      (a = -target / 3 ∧ b = -target / 3 ∧ c = -target / 3) := by
  by_cases ha : ‖a‖ ≤ ‖target‖ / 3
  · by_cases hb : ‖b‖ ≤ ‖target‖ / 3
    · by_cases hc : ‖c‖ ≤ ‖target‖ / 3
      · exact Or.inr (d4ThreeChannelResonantNormThresholdRigidity a b c target
          hsum ha hb hc)
      · exact Or.inl (Or.inr (Or.inr (lt_of_not_ge hc)))
    · exact Or.inl (Or.inr (Or.inl (lt_of_not_ge hb)))
  · exact Or.inl (Or.inl (lt_of_not_ge ha))

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private lemma resonantProjection_not_linearizedExact_of_ne_zero
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0) (source : V) (hprojection : ell source ≠ 0) :
    ¬ ∃ gauge, source = L gauge := by
  rintro ⟨gauge, rfl⟩
  exact hprojection (hleft gauge)

/-- In the actual Einstein split, simultaneous one-third upper bounds force all three projections
to equal the exact negative AIME third. -/
theorem d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_thresholdRigidity
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
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q)
    (hOrthogonal :
      ‖ell (B hPlus (hPlusMinus - P hPlusMinus))‖ ≤
        ‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3)
    (hSecondHarmonic :
      ‖ell (B hMinus hPlusPlus)‖ ≤
        ‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3)
    (hDirect :
      ‖ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)‖ ≤
        ‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3) :
    ell (B hPlus (hPlusMinus - P hPlusMinus)) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 ∧
      ell (B hMinus hPlusPlus) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 ∧
      ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 := by
  apply d4ThreeChannelResonantNormThresholdRigidity
  · have hsum :=
      d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
        ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
    simpa only [map_add] using hsum
  · exact hOrthogonal
  · exact hSecondHarmonic
  · exact hDirect

/-- For nonzero seed, actual channels obey a sharp cokernel alternative: strict dominance by one
nonexact channel, or exact equipartition with all three channels nonexact. -/
theorem d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_strictOrEquipartitionCokernel
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
    ((‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 <
          ‖ell (B hPlus (hPlusMinus - P hPlusMinus))‖ ∧
        ¬ ∃ gauge, B hPlus (hPlusMinus - P hPlusMinus) = L gauge) ∨
      (‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 <
          ‖ell (B hMinus hPlusPlus)‖ ∧
        ¬ ∃ gauge, B hMinus hPlusPlus = L gauge) ∨
      (‖d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)‖ / 3 <
          ‖ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)‖ ∧
        ¬ ∃ gauge,
          d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus = L gauge)) ∨
    ((ell (B hPlus (hPlusMinus - P hPlusMinus)) =
          -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 ∧
        ¬ ∃ gauge, B hPlus (hPlusMinus - P hPlusMinus) = L gauge) ∧
      (ell (B hMinus hPlusPlus) =
          -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 ∧
        ¬ ∃ gauge, B hMinus hPlusPlus = L gauge) ∧
      (ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) =
          -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) / 3 ∧
        ¬ ∃ gauge,
          d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus = L gauge)) := by
  let orthogonal := B hPlus (hPlusMinus - P hPlusMinus)
  let secondHarmonic := B hMinus hPlusPlus
  let direct := d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus
  let aime := d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)
  have hsum : ell orthogonal + ell secondHarmonic + ell direct = -aime := by
    have h :=
      d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
        ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
    simpa only [orthogonal, secondHarmonic, direct, aime, map_add] using h
  have haime : aime ≠ 0 :=
    (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr hamplitude
  have hstrictNotExact : ∀ source : V,
      ‖aime‖ / 3 < ‖ell source‖ → ¬ ∃ gauge, source = L gauge := by
    intro source hstrict
    apply resonantProjection_not_linearizedExact_of_ne_zero L ell hleft source
    intro hzero
    rw [hzero, norm_zero] at hstrict
    have hpos : 0 < ‖aime‖ := norm_pos_iff.mpr haime
    linarith
  rcases d4ThreeChannelResonantNormThresholdDichotomy
      (ell orthogonal) (ell secondHarmonic) (ell direct) aime hsum with
      hstrict | hequal
  · left
    rcases hstrict with hOrthogonal | hSecondHarmonic | hDirect
    · exact Or.inl ⟨hOrthogonal, hstrictNotExact orthogonal hOrthogonal⟩
    · exact Or.inr (Or.inl ⟨hSecondHarmonic,
        hstrictNotExact secondHarmonic hSecondHarmonic⟩)
    · exact Or.inr (Or.inr ⟨hDirect, hstrictNotExact direct hDirect⟩)
  · right
    rcases hequal with ⟨hOrthogonal, hSecondHarmonic, hDirect⟩
    have hnonzero : -aime / 3 ≠ 0 := div_ne_zero (neg_ne_zero.mpr haime) (by norm_num)
    have hOrthogonalNe : ell orthogonal ≠ 0 := hOrthogonal.symm ▸ hnonzero
    have hSecondHarmonicNe : ell secondHarmonic ≠ 0 := hSecondHarmonic.symm ▸ hnonzero
    have hDirectNe : ell direct ≠ 0 := hDirect.symm ▸ hnonzero
    exact ⟨⟨hOrthogonal,
        resonantProjection_not_linearizedExact_of_ne_zero L ell hleft orthogonal
          hOrthogonalNe⟩,
      ⟨⟨hSecondHarmonic,
          resonantProjection_not_linearizedExact_of_ne_zero L ell hleft secondHarmonic
            hSecondHarmonicNe⟩,
        ⟨hDirect,
          resonantProjection_not_linearizedExact_of_ne_zero L ell hleft direct hDirectNe⟩⟩⟩

end

end RHTower
