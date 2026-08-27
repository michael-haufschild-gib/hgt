import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue

/-!
# Cubic phase covariance and optical-work no-go

A physical `++-` coefficient has amplitude dependence `A * |A|² * c`.  It is therefore
equivariant, rather than invariant, under a common `U(1)` phase.  In particular, its bare
imaginary part cannot be strictly positive for every nonzero complex seed: changing `A` to `-A`
reverses that sign.

The Hermitian modal work `conj(A) * Sigma(A)` removes exactly this charge.  It equals
`|A|⁴ * c`, is invariant under every unit phase, and has positive imaginary part exactly when the
phase-normalized coefficient `c` does.  Any phase-sensitive nonlinear optical theorem for the
theta-cusp Birmingham--Mokhtari `++-` return must use this modal work, an equivalent quotient by
`A`, or a phase-fixed source normalization.  It cannot equate the bare cokernel coordinate to a
positive radiation flux for arbitrary nonzero seed phase.

`[NO-GO] [PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Universal amplitude law of a cubic `++-` scalar section. -/
def d4CubicPlusPlusMinusPhaseSection (coefficient amplitude : ℂ) : ℂ :=
  amplitude * (Complex.normSq amplitude : ℂ) * coefficient

/-- Hermitian modal work associated with a cubic `++-` scalar section. -/
def d4CubicPlusPlusMinusModalWork (coefficient amplitude : ℂ) : ℂ :=
  (starRingEnd ℂ) amplitude * d4CubicPlusPlusMinusPhaseSection coefficient amplitude

/-- Reversing seed phase reverses the bare cubic section. -/
theorem d4CubicPlusPlusMinusPhaseSection_neg
    (coefficient amplitude : ℂ) :
    d4CubicPlusPlusMinusPhaseSection coefficient (-amplitude) =
      -d4CubicPlusPlusMinusPhaseSection coefficient amplitude := by
  simp [d4CubicPlusPlusMinusPhaseSection]

/-- Cubic `++-` sections carry one unit of common phase charge. -/
theorem d4CubicPlusPlusMinusPhaseSection_mul_unitPhase
    (coefficient amplitude phase : ℂ) (hphase : Complex.normSq phase = 1) :
    d4CubicPlusPlusMinusPhaseSection coefficient (phase * amplitude) =
      phase * d4CubicPlusPlusMinusPhaseSection coefficient amplitude := by
  rw [d4CubicPlusPlusMinusPhaseSection, d4CubicPlusPlusMinusPhaseSection,
    Complex.normSq_mul, hphase]
  norm_num
  ring

/-- Bare imaginary part of a cubic `++-` section cannot be positive for every nonzero phase. -/
theorem not_d4CubicPlusPlusMinusPhaseSection_im_pos_for_all_nonzero
    (coefficient : ℂ) :
    ¬ ∀ amplitude : ℂ, amplitude ≠ 0 →
      0 < (d4CubicPlusPlusMinusPhaseSection coefficient amplitude).im := by
  intro h
  have hpos := h 1 (by norm_num)
  have hneg := h (-1) (by norm_num)
  rw [d4CubicPlusPlusMinusPhaseSection_neg] at hneg
  simp only [Complex.neg_im] at hneg
  linarith

/-- Hermitian pairing removes the one-unit cubic phase charge exactly. -/
theorem d4CubicPlusPlusMinusModalWork_eq
    (coefficient amplitude : ℂ) :
    d4CubicPlusPlusMinusModalWork coefficient amplitude =
      (Complex.normSq amplitude : ℂ) ^ 2 * coefficient := by
  rw [d4CubicPlusPlusMinusModalWork, d4CubicPlusPlusMinusPhaseSection]
  calc
    (starRingEnd ℂ) amplitude *
        (amplitude * ↑(Complex.normSq amplitude) * coefficient) =
      ((starRingEnd ℂ) amplitude * amplitude) *
        ↑(Complex.normSq amplitude) * coefficient := by ring
    _ = _ := by
      rw [← Complex.normSq_eq_conj_mul_self]
      ring

/-- Hermitian cubic modal work is invariant under common unit phase. -/
theorem d4CubicPlusPlusMinusModalWork_mul_unitPhase
    (coefficient amplitude phase : ℂ) (hphase : Complex.normSq phase = 1) :
    d4CubicPlusPlusMinusModalWork coefficient (phase * amplitude) =
      d4CubicPlusPlusMinusModalWork coefficient amplitude := by
  rw [d4CubicPlusPlusMinusModalWork_eq, d4CubicPlusPlusMinusModalWork_eq,
    Complex.normSq_mul, hphase]
  norm_num

/-- Imaginary modal work is the phase-normalized imaginary coefficient times `|A|⁴`. -/
theorem d4CubicPlusPlusMinusModalWork_im
    (coefficient amplitude : ℂ) :
    (d4CubicPlusPlusMinusModalWork coefficient amplitude).im =
      Complex.normSq amplitude ^ 2 * coefficient.im := by
  rw [d4CubicPlusPlusMinusModalWork_eq]
  calc
    ((↑(Complex.normSq amplitude) : ℂ) ^ 2 * coefficient).im =
        ((((Complex.normSq amplitude) ^ 2 : ℝ) : ℂ) * coefficient).im := by
      rw [Complex.ofReal_pow]
    _ = _ := by
      norm_num [Complex.normSq_apply, Complex.mul_im, pow_two]

/-- For nonzero seed, modal-work sign is exactly phase-normalized coefficient sign. -/
theorem d4CubicPlusPlusMinusModalWork_im_pos_iff
    (coefficient amplitude : ℂ) (ha : amplitude ≠ 0) :
    0 < (d4CubicPlusPlusMinusModalWork coefficient amplitude).im ↔
      0 < coefficient.im := by
  rw [d4CubicPlusPlusMinusModalWork_im]
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos (Complex.normSq_pos.mpr ha))

/-- Corpus AIME numerator is exactly a cubic phase section. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_eq_phaseSection
    (amplitude z : ℂ) :
    d4FundamentalQNMCrossBranchAIMENumerator amplitude z =
      d4CubicPlusPlusMinusPhaseSection
        (d4FundamentalQNMCrossBranchChiralMassJetNumerator z) amplitude := by
  rfl

/-- Exact AIME return reverses under the half-turn seed phase. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_neg
    (amplitude z : ℂ) :
    d4FundamentalQNMCrossBranchAIMENumerator (-amplitude) z =
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude z := by
  rw [d4FundamentalQNMCrossBranchAIMENumerator_eq_phaseSection,
    d4FundamentalQNMCrossBranchAIMENumerator_eq_phaseSection,
    d4CubicPlusPlusMinusPhaseSection_neg]

end

end RHTower
