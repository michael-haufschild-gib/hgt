import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation

/-!
# Transverse escape cone for Möbius Gamma--Hankel covariance

One off-critical zeta zero already forces the finite Möbius Gamma--Hankel off-diagonal covariance
to escape on every strict-right line below that zero.  This module takes the supremum over the
actual right-half Xi divisor and proves the maximal open interval forced by those zeros.

It also proves the quantitative contrapositive: bounded returns on one line bound the right-zero
transverse supremum by that line's displacement from `1/2`.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- The covariance escapes on every line below the rightmost transverse Xi-zero supremum. -/
def MobiusGammaHankelTransverseEscapeCone : Prop :=
  ∀ sigma : ℝ, 1 / 2 < sigma →
    sigma < 1 / 2 + xiRightTransverseSup →
    Tendsto
      (fun N : ℕ =>
        finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma))
      atTop atTop

/-- **Maximal open Gamma--Hankel escape cone.**  A nonempty right-half Xi divisor forces covariance
escape at every abscissa strictly below `1/2 + xiRightTransverseSup`.  The supremum need not be
attained, so no upper-endpoint assertion is made. -/
theorem mobiusGammaHankelTransverseEscapeCone_of_nonempty_xiRightZeroCopy
    (hne : Nonempty XiRightZeroCopy) :
    MobiusGammaHankelTransverseEscapeCone := by
  intro sigma hsigmaHalf hsigmaSup
  have halphaSup : sigma - 1 / 2 < xiRightTransverseSup := by
    linarith
  have hsetNonempty : xiRightTransverseSet.Nonempty := by
    obtain ⟨q⟩ := hne
    exact ⟨(xiRightCenteredZero q).re, ⟨q, rfl⟩⟩
  obtain ⟨x, hx, halphaX⟩ :=
    exists_lt_of_lt_csSup hsetNonempty (by
      simpa only [xiRightTransverseSup] using halphaSup)
  obtain ⟨q, rfl⟩ := hx
  have hrhoSigma : sigma ≤ (q.1.1 : ℂ).re := by
    change sigma - 1 / 2 < (xiRightCenteredZero q).re at halphaX
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at halphaX
    norm_num at halphaX
    linarith
  have hstrip := xi_divisor_support_re_mem_open_unit q.1.1
  have hrhoOne : (q.1.1 : ℂ) ≠ 1 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hxi : xi (q.1.1 : ℂ) = 0 :=
    xi_eq_zero_of_mem_divisor_support q.1.1
  have hzeta : riemannZeta (q.1.1 : ℂ) = 0 :=
    (xi_eq_zero_iff hstrip.1 hrhoOne).mp hxi
  exact tendsto_finiteMobiusGammaHankelOffDiagonalCovariance_atTop_of_riemannZeta_zero
    hsigmaHalf (lt_of_le_of_lt hrhoSigma hstrip.2) hrhoSigma hrhoOne hzeta

/-- Failure of RH activates the entire maximal open Gamma--Hankel escape cone. -/
theorem not_riemannHypothesis_implies_mobiusGammaHankelTransverseEscapeCone
    (hRH : ¬RiemannHypothesis) :
    MobiusGammaHankelTransverseEscapeCone :=
  mobiusGammaHankelTransverseEscapeCone_of_nonempty_xiRightZeroCopy
    (nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH)

/-- **Single-line zero-abscissa detector.**  Frequently bounded covariance returns at
`sigma > 1/2` force every right-half Xi zero to lie strictly left of, or on, that line. -/
theorem xiRightTransverseSup_le_sub_half_of_frequently_bounded_mobiusGammaHankel
    {sigma C : ℝ} (hsigmaHalf : 1 / 2 < sigma)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ C) :
    xiRightTransverseSup ≤ sigma - 1 / 2 := by
  by_cases hne : Nonempty XiRightZeroCopy
  · by_contra hnot
    have hsigmaSup : sigma < 1 / 2 + xiRightTransverseSup := by
      rw [not_le] at hnot
      linarith
    have hescape :=
      mobiusGammaHankelTransverseEscapeCone_of_nonempty_xiRightZeroCopy
        hne sigma hsigmaHalf hsigmaSup
    have hevent : ∀ᶠ N : ℕ in atTop,
        C < finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) :=
      (tendsto_atTop.1 hescape (C + 1)).mono (by
        intro N hN
        linarith)
    obtain ⟨N, hle, hlt⟩ := (hfreq.and_eventually hevent).exists
    exact (not_lt_of_ge hle) hlt
  · letI : IsEmpty XiRightZeroCopy := ⟨fun q => hne ⟨q⟩⟩
    have hrange : xiRightTransverseSet = ∅ := by
      exact Set.range_eq_empty_iff.mpr inferInstance
    rw [xiRightTransverseSup, hrange, Real.sSup_empty]
    linarith

end

end RHTower
