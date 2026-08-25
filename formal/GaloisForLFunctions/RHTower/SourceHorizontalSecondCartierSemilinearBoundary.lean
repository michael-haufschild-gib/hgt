import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierHermitianIncidencePolarization

/-!
# One-leg semilinear boundary for the source-horizontal Cartier ghost

The reciprocal-star source character cannot be converted to the unit-anchor character by changing
from complex-linear to conjugate-homogeneous scalar readout.  Nonzero covariance still forces the
transfer character to be unitary.  Thus every actual strict-right Xi fibre rejects both one-leg
linear and conjugate-semilinear reporters, while the paired Hermitian incidence remains exactly
transfer-invariant.

This is a framework boundary, not an RH endpoint: horizontal cancellation must pair the reciprocal
and unit character legs before scalarization.
-/

open Complex

namespace RHTower

noncomputable section

/-- Conjugate homogeneity alone, without additivity, is already too rigid for a nonzero
one-leg reporter intertwining the reciprocal-star ghost with the unit-anchor character. -/
theorem sourceHorizontalSecondCartierPointedKrein_starHomogeneous_anchor_covariance_norm_eq_one
    {lam : ℂ} (hlam : lam ≠ 0)
    (A : SourceHorizontalBilateralSecondJetSource → ℂ)
    (hstar : ∀ z v, A (z • v) = star z * A v)
    (hA : A sourceHorizontalBilateralSecondJetGhost ≠ 0)
    (hcov : A (sourceHorizontalSecondCartierKreinSourceTransfer lam
        sourceHorizontalBilateralSecondJetGhost) =
      lam * A sourceHorizontalBilateralSecondJetGhost) :
    ‖lam‖ = 1 := by
  have hsource : sourceHorizontalSecondCartierKreinSourceTransfer lam
        sourceHorizontalBilateralSecondJetGhost =
      (star lam)⁻¹ • sourceHorizontalBilateralSecondJetGhost := by
    ext <;> simp [sourceHorizontalSecondCartierKreinSourceTransfer,
      sourceHorizontalBilateralSecondJetGhost] <;> ring
  rw [hsource, hstar] at hcov
  simp only [star_inv₀, star_star] at hcov
  have hcoeff : lam⁻¹ = lam := mul_right_cancel₀ hA hcov
  have hmul : lam * lam = 1 := by
    calc
      lam * lam = lam * lam⁻¹ := by rw [hcoeff]
      _ = 1 := mul_inv_cancel₀ hlam
  have hnorm := congrArg norm hmul
  simp only [norm_mul, norm_one] at hnorm
  nlinarith [norm_nonneg lam]

/-- Strict-right Xi fibres admit no nonzero conjugate-homogeneous one-leg reporter with the
unit-anchor covariance law. Additivity is not assumed. -/
theorem sourceHorizontalSecondCartierPointedKrein_strictRight_no_starHomogeneous_transverse_anchor
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    ¬ ∃ A : SourceHorizontalBilateralSecondJetSource → ℂ,
      (∀ z v, A (z • v) = star z * A v) ∧
      A sourceHorizontalBilateralSecondJetGhost ≠ 0 ∧
        A (sourceHorizontalSecondCartierKreinSourceTransfer
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
            sourceHorizontalBilateralSecondJetGhost) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p *
            A sourceHorizontalBilateralSecondJetGhost := by
  rintro ⟨A, hstar, hA, hcov⟩
  have hnorm :
      ‖sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p‖ = 1 :=
    sourceHorizontalSecondCartierPointedKrein_starHomogeneous_anchor_covariance_norm_eq_one
      (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)
      A hstar hA hcov
  have hline := (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le
    (q.1.1 : XiDivisorSupport)).1 hnorm
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  exact (ne_of_gt hright) hline

/-- Sharp morphism boundary on an actual strict-right Xi fibre: neither complex-linear nor
conjugate-homogeneous one-leg covariance exists, but paired Hermitian incidence is invariant. -/
theorem sourceHorizontalSecondCartierPointedKrein_strictRight_oneLeg_noGo_twoLeg_survival
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    (¬ ∃ A : SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] ℂ,
      A sourceHorizontalBilateralSecondJetGhost ≠ 0 ∧
        A (sourceHorizontalSecondCartierKreinSourceTransfer
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
            sourceHorizontalBilateralSecondJetGhost) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p *
            A sourceHorizontalBilateralSecondJetGhost) ∧
    (¬ ∃ A : SourceHorizontalBilateralSecondJetSource → ℂ,
      (∀ z v, A (z • v) = star z * A v) ∧
      A sourceHorizontalBilateralSecondJetGhost ≠ 0 ∧
        A (sourceHorizontalSecondCartierKreinSourceTransfer
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
            sourceHorizontalBilateralSecondJetGhost) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p *
            A sourceHorizontalBilateralSecondJetGhost) ∧
    ∀ w : SourceHorizontalSecondCartierKreinJet,
      sourceHorizontalSecondCartierKreinHermitianIncidence
          (sourceHorizontalSecondCartierKreinJetTransfer
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) w) =
        sourceHorizontalSecondCartierKreinHermitianIncidence w := by
  refine ⟨sourceHorizontalSecondCartierPointedKrein_strictRight_no_linear_transverse_anchor q p,
    sourceHorizontalSecondCartierPointedKrein_strictRight_no_starHomogeneous_transverse_anchor
      q p, ?_⟩
  exact sourceHorizontalSecondCartierKreinHermitianIncidence_transfer
    (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)

end

end RHTower
