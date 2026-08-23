/-
# Chen--Gupta--Li horizontal-collision no-go

The standard CGL packet cannot be the finite carrier of horizontal reflection
charge.  Functional-equation reflection preserves the ordinate, whereas a
fibre-separated CGL packet makes `(character, ordinate)` injective.  Thus two
distinct reflected divisor points cannot survive as two packet rows.

Independently, the explicit Proposition 4.6 envelope has a source-range floor
of `288`: its positive trace-mass term cannot certify the strict bound below
the first horizontal-collision quantum `2`, regardless of how sharply the
nonzero-frequency strata are estimated.

Together these statements rule out closing the horizontal-collision endpoint
by merely finishing the standard CGL `S₂/S₃` estimates.  A surviving merger
must add a confluent horizontal channel (for example a reflection divided
difference or logarithmic derivative) before applying packet separation.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition46

noncomputable section

namespace RHTower

/-- Functional-equation reflection preserves imaginary part.  Consequently,
two CGL rows carrying one character and a reflected pair of ordinates must be
the same row. -/
theorem cglFibreSeparatedPacket_reflection_rows_collapse
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R) (r s : Fin R) (z : ℂ)
    (hchar : P.character r = P.character s)
    (hr : P.ordinate r = z.im)
    (hs : P.ordinate s = ((1 : ℂ) - (starRingEnd ℂ) z).im) :
    r = s := by
  by_contra hrs
  apply cglFibreSeparatedPacket_ordinate_ne P r s hrs hchar
  rw [hr, hs]
  simp

/-- In the source range `σ ≤ 1`, the explicit Proposition 4.6 right-hand side
is at least `288`.  This floor is present before any estimate of `S₁`, `S₂`, or
`S₃`. -/
theorem cglProposition46_rhs_ge_288
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) (hsigma : S.sigma ≤ 1) :
    288 ≤
      288 * (cglProposition46ZeroFrequencyNumerator S ^ (1 / 3 : ℝ) + 1) *
          (N.value : ℝ) ^ (2 - 2 * S.sigma) +
        288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
          (max 0 (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) := by
  have hN : (1 : ℝ) ≤ N.value := by
    exact_mod_cast Nat.succ_le_iff.mpr N.positive
  have hexp : 0 ≤ 2 - 2 * S.sigma := by linarith
  have hNpow : 1 ≤ (N.value : ℝ) ^ (2 - 2 * S.sigma) :=
    Real.one_le_rpow hN hexp
  have hK : 0 ≤ cglProposition46ZeroFrequencyNumerator S ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (cglProposition46_zeroFrequencyNumerator_nonneg S) _
  have hfirst : 288 ≤
      288 * (cglProposition46ZeroFrequencyNumerator S ^ (1 / 3 : ℝ) + 1) *
        (N.value : ℝ) ^ (2 - 2 * S.sigma) := by
    nlinarith
  have hsecond : 0 ≤
      288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
        (max 0 (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) := by
    positivity
  linarith

/-- The certified Proposition 4.6 envelope is never below the first
horizontal-collision quantum in the source range. -/
theorem cglProposition46_rhs_not_lt_two
    {q R : ℕ} {P : CGLFibreSeparatedPacket q (R + 1)} {N : CGLPositiveLength}
    (S : CGLProposition46Packet P N) (hsigma : S.sigma ≤ 1) :
    ¬ (288 * (cglProposition46ZeroFrequencyNumerator S ^ (1 / 3 : ℝ) + 1) *
          (N.value : ℝ) ^ (2 - 2 * S.sigma) +
        288 * (N.value : ℝ) ^ (1 - 2 * S.sigma) *
          (max 0 (cglProposition46NonzeroFrequencySum S).re) ^ (1 / 3 : ℝ) < 2) := by
  intro h
  have hfloor := cglProposition46_rhs_ge_288 S hsigma
  linarith

end RHTower
