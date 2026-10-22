import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedPropagatorGlobalRigidity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue

/-!
# HB AIME/BM global source incompatibility

The fundamental absorption-induced mode-excitation (AIME) residue is a literal nonlinear
gravitational source already derived in the HB corpus.  Nevertheless no fixed nonzero
normalization of a nonzero AIME channel can equal the exact unit-seed BM Peierls boundary target
on every Xi fibre.

Precisely, global equality holds exactly when the normalization or absorbed seed vanishes and RH
holds.  Hardy's unconditional critical-line divisor forces source degeneracy, because the BM
target vanishes there while the AIME residue does not.  Global equality then makes every BM target
zero and hence gives RH.

The full same-pole residue also yields an exact positive survivor: on a critical Xi fibre, any
successful third-order `++-` remainder must equal the negative AIME numerator.  For nonzero seed
this forced counterterm is nonzero.  Thus AIME-only dynamics is closed, while the remaining HB PDE
burden is an explicit nonvanishing same-pole source identity.

`[NEW] [SOURCE NO-GO] [EXACT CORRECTION LAW] [RH RECEIVER] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- A fixed scalar multiple of the fundamental AIME residue matches every unit-seed BM target
exactly in the degenerate-source RH case. -/
theorem forall_normalizedAIMEResidue_eq_unitBMTarget_iff
    (n : ℕ) (normalization amplitude : ℂ) :
    (∀ q : XiZeroCopy,
      normalization * d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) ↔
      (normalization = 0 ∨ amplitude = 0) ∧ RiemannHypothesis := by
  constructor
  · intro h
    obtain ⟨rho, hrho⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
    have hpos := xi_divisor_pos_on_support rho
    have hnat : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    let q0 : XiZeroCopy := ⟨rho, ⟨0, hnat⟩⟩
    have htarget0 :
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q0 = 0 := by
      exact (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q0
        (z := 1 / 2) (by norm_num) (by norm_num)).mpr hrho
    have hproduct0 :
        normalization *
            d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q0) = 0 :=
      (h q0).trans htarget0
    have hdegenerate : normalization = 0 ∨ amplitude = 0 := by
      by_cases hnormalization : normalization = 0
      · exact Or.inl hnormalization
      · right
        by_contra hamplitude
        have hresidue :
            d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q0) ≠ 0 :=
          (d4FundamentalQNMCrossBranchAIMEResidue_xi_ne_zero_iff amplitude q0).mpr
            hamplitude
        exact hresidue ((mul_eq_zero.mp hproduct0).resolve_left hnormalization)
    refine ⟨hdegenerate, ?_⟩
    have htargetAll : ∀ q : XiZeroCopy,
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q = 0 := by
      intro q
      rw [← h q]
      rcases hdegenerate with hnormalization | hamplitude
      · simp [hnormalization]
      · simp [hamplitude, d4FundamentalQNMCrossBranchAIMEResidue,
          d4FundamentalQNMCrossBranchAIMENumerator]
    apply
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q
      (z := 1 / 2) (by norm_num) (by norm_num)).mp (htargetAll q)
  · rintro ⟨hdegenerate, hRH⟩ q
    have hleft :
        normalization *
            d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q) = 0 := by
      rcases hdegenerate with hnormalization | hamplitude
      · simp [hnormalization]
      · simp [hamplitude, d4FundamentalQNMCrossBranchAIMEResidue,
          d4FundamentalQNMCrossBranchAIMENumerator]
    calc
      normalization *
          d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q) = 0 := hleft
      _ = d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
        symm
        apply (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q
          (z := 1 / 2) (by norm_num) (by norm_num)).mpr
        exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- No nonzero fixed normalization of a nonzero AIME residue can realize global BM incidence. -/
theorem not_exists_nonzero_normalizedAIMEResidue_global_unitBMTarget
    (n : ℕ) :
    ¬ ∃ normalization amplitude : ℂ,
      normalization ≠ 0 ∧ amplitude ≠ 0 ∧
      ∀ q : XiZeroCopy,
        normalization *
            d4FundamentalQNMCrossBranchAIMEResidue amplitude (xiSpectralPoint q) =
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  rintro ⟨normalization, amplitude, hnormalization, hamplitude, hglobal⟩
  have hdegenerate :=
    (forall_normalizedAIMEResidue_eq_unitBMTarget_iff n normalization amplitude).mp hglobal
  exact hdegenerate.1.elim hnormalization hamplitude

/-- Exact third-order same-pole source value required for the full projected residue to equal the
unit-seed BM boundary target on one Xi fibre. -/
theorem d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource
    (n : ℕ) (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy) :
    d4FullCrossBranchProjectedResidue amplitude samePoleSourceRemainder
        (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q ↔
      samePoleSourceRemainder (xiSpectralPoint q) =
        d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus 0 (xiSpectralPoint q) *
            d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q -
          d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  have hderivative :=
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero 0 q
  unfold d4FullCrossBranchProjectedResidue d4FullCrossBranchPoleNumerator
  rw [div_eq_iff hderivative]
  constructor <;> intro h <;> linear_combination h

/-- At a critical Xi fibre the BM target vanishes, so successful same-pole dynamics must supply
exactly the negative AIME numerator. -/
theorem d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
    (n : ℕ) (amplitude : ℂ) (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    d4FullCrossBranchProjectedResidue amplitude samePoleSourceRemainder
        (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q ↔
      samePoleSourceRemainder (xiSpectralPoint q) =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource]
  have htarget :
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q = 0 :=
    (hbUniversalPeierlsBMTarget_eq_zero_iff one_ne_zero n q
      (z := 1 / 2) (by norm_num) (by norm_num)).mpr hline
  rw [htarget]
  ring

/-- For nonzero absorbed seed, any third-order remainder matching BM incidence at a critical Xi
fibre is necessarily nonzero. -/
theorem d4FullCrossBranch_samePoleSourceRemainder_ne_zero_of_unitBMTarget_of_criticalLine
    (n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (samePoleSourceRemainder : ℂ → ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude samePoleSourceRemainder
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    samePoleSourceRemainder (xiSpectralPoint q) ≠ 0 := by
  have hremainder :=
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n amplitude samePoleSourceRemainder q hline).mp hmatch
  rw [hremainder, neg_ne_zero]
  exact (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr hamplitude

end

end RHTower
