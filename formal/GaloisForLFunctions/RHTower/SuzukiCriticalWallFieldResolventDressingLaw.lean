import GaloisForLFunctions.RHTower.SuzukiCriticalWallFieldSquareRootWeld
import GaloisForLFunctions.RHTower.SuzukiAffineResolventKreinDefect

/-!
# Suzuki critical wall-field resolvent dressing law

The bare critical wall amplitude is a source coordinate, not a deficiency endpoint response.
At one restricted-Weil spectral level it must first be dressed by the shifted scalar resolvent.
This file proves exact interaction of that dressing with two-shift affine sewing.

Self-pairing the affine residual with the same wall field closes through the previously proved
symmetric-square weld.  Every negative spectral level then carries an exact
von-Mangoldt-weighted compensation debt at zero height.  No RH premise, estimate, computation, or
claim about the full restricted-Weil spectral measure is used.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## One-mode resolvent dressing -/

/-- One spectral coordinate of critical wall source after shifted-resolvent dressing. -/
def suzukiCriticalWallResolventDressedField
    (lambda spectralLevel t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (suzukiPointSpectralResolvent lambda spectralLevel : ℂ) *
    suzukiCriticalWallField t p e

/-- Affine two-shift extrapolation of one dressed wall coordinate to shift zero. -/
def suzukiCriticalWallAffineDressedField
    (alpha beta spectralLevel t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (suzukiAffineResolventExtrapolation alpha beta spectralLevel : ℂ) *
    suzukiCriticalWallField t p e

/-- Dressed affine residual factors through exactly the existing scalar Krein defect. -/
theorem suzukiCriticalWallDressedResidual_eq_kreinDefect_mul_wallField
    (alpha beta spectralLevel t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallResolventDressedField 0 spectralLevel t p e -
        suzukiCriticalWallAffineDressedField alpha beta spectralLevel t p e =
      (suzukiAffineResolventKreinDefect alpha beta spectralLevel : ℂ) *
        suzukiCriticalWallField t p e := by
  simp only [suzukiCriticalWallResolventDressedField,
    suzukiCriticalWallAffineDressedField,
    suzukiAffineResolventKreinDefect]
  push_cast
  ring

/-- Away from three poles and coincident shifts, dressed residual has explicit rational weight. -/
theorem suzukiCriticalWallDressedResidual_eq_rational_mul_wallField
    {alpha beta spectralLevel : ℝ} (t : ℝ) (p : Nat.Primes) (e : ℕ)
    (hab : alpha ≠ beta) (hs : spectralLevel ≠ 0)
    (hsa : spectralLevel ≠ alpha) (hsb : spectralLevel ≠ beta) :
    suzukiCriticalWallResolventDressedField 0 spectralLevel t p e -
        suzukiCriticalWallAffineDressedField alpha beta spectralLevel t p e =
      (alpha * beta /
          (spectralLevel * (spectralLevel - alpha) * (spectralLevel - beta)) : ℂ) *
        suzukiCriticalWallField t p e := by
  rw [suzukiCriticalWallDressedResidual_eq_kreinDefect_mul_wallField,
    suzukiAffineResolventKreinDefect_eq hab hs hsa hsb]
  push_cast
  ring_nf

/-! ## Symmetric-square closure and sign -/

/-- Self-pairing the dressed residual with its source field closes through the exact far-hinge
numerator.  This is a bilinear square, retaining full prime-power delay phase. -/
theorem suzukiCriticalWallField_mul_dressedResidual_eq_kreinDefect_mul_farHingeNumerator
    (alpha beta spectralLevel t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField t p e *
        (suzukiCriticalWallResolventDressedField 0 spectralLevel t p e -
          suzukiCriticalWallAffineDressedField alpha beta spectralLevel t p e) =
      (suzukiAffineResolventKreinDefect alpha beta spectralLevel : ℂ) *
        ((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
            Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
          suzukiOscillatoryKernel (t : ℂ)
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) := by
  rw [suzukiCriticalWallDressedResidual_eq_kreinDefect_mul_wallField]
  calc
    suzukiCriticalWallField t p e *
        ((suzukiAffineResolventKreinDefect alpha beta spectralLevel : ℂ) *
          suzukiCriticalWallField t p e) =
      (suzukiAffineResolventKreinDefect alpha beta spectralLevel : ℂ) *
        suzukiCriticalWallField t p e ^ 2 := by ring
    _ = _ := by rw [sq_suzukiCriticalWallField_eq_farHingeNumerator]

/-- At zero height, self-paired affine residual is scalar Krein defect times exact positive
von-Mangoldt prime-power weight. -/
theorem re_suzukiCriticalWallField_mul_dressedResidual_zero_eq
    (alpha beta spectralLevel : ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallField 0 p e *
        (suzukiCriticalWallResolventDressedField 0 spectralLevel 0 p e -
          suzukiCriticalWallAffineDressedField alpha beta spectralLevel 0 p e)).re =
      suzukiAffineResolventKreinDefect alpha beta spectralLevel *
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) := by
  rw [suzukiCriticalWallField_mul_dressedResidual_eq_kreinDefect_mul_farHingeNumerator]
  simp [suzukiOscillatoryKernel]

/-- Every negative spectral level above two negative shifts creates strict source-weighted
compensation debt. -/
theorem re_suzukiCriticalWallField_mul_dressedResidual_zero_neg
    {alpha beta spectralLevel : ℝ}
    (hab : alpha < beta) (hb0 : beta < 0) (hbs : beta < spectralLevel)
    (hs0 : spectralLevel < 0) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallField 0 p e *
        (suzukiCriticalWallResolventDressedField 0 spectralLevel 0 p e -
          suzukiCriticalWallAffineDressedField alpha beta spectralLevel 0 p e)).re < 0 := by
  rw [re_suzukiCriticalWallField_mul_dressedResidual_zero_eq]
  exact mul_neg_of_neg_of_pos
    ((suzukiAffineResolventKreinDefect_neg_iff hab hb0 hbs (ne_of_lt hs0)).mpr hs0)
    (suzukiCriticalFarHingeWeight_pos p e)

/-- Positive spectral levels give strict positive source-weighted residual under same shifts. -/
theorem re_suzukiCriticalWallField_mul_dressedResidual_zero_pos
    {alpha beta spectralLevel : ℝ}
    (hab : alpha < beta) (hb0 : beta < 0) (hbs : beta < spectralLevel)
    (hs0 : 0 < spectralLevel) (p : Nat.Primes) (e : ℕ) :
    0 < (suzukiCriticalWallField 0 p e *
        (suzukiCriticalWallResolventDressedField 0 spectralLevel 0 p e -
          suzukiCriticalWallAffineDressedField alpha beta spectralLevel 0 p e)).re := by
  rw [re_suzukiCriticalWallField_mul_dressedResidual_zero_eq]
  exact mul_pos
    ((suzukiAffineResolventKreinDefect_pos_iff hab hb0 hbs (ne_of_gt hs0)).mpr hs0)
    (suzukiCriticalFarHingeWeight_pos p e)

end

end RHTower
