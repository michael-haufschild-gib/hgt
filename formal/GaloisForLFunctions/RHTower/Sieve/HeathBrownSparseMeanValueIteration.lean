import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSelfBound
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueArbitraryScale

/-!
# Two-step closure of the Heath--Brown sparse mean value

The outer collision recurrence lands at the half-height unit interval of length `N0`. Its divisor
square lift lands at length `N0^2`; the existing one-step self-bound closes that inner integral.
This retains arbitrary sparse phases and every dense coefficient in `[0,1]` at the outer source.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

private theorem le_sqrt_of_sq_le_nonneg {x K : ℝ}
    (_hx : 0 ≤ x) (hK : 0 ≤ K) (h : x ^ 2 ≤ K) : x ≤ Real.sqrt K := by
  nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K]

/-- Coefficient-faithful two-step Heath--Brown iteration. The first recurrence/square lift lands at
`N0²`; the second recurrence is absorbed there by the existing one-step theorem. -/
theorem integral_Icc_normSq_heathBrown_factors_le_twoStepSelfBound
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    {X : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    {N N0 : ℕ} (hB : ∀ n ∈ B, (n : ℕ) ≤ N)
    (hN0 : 1 ≤ N0)
    {eta : ℝ} (heta : 0 < eta) :
    let a0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
    let b0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (((N / N0 + 1 : ℕ) : ℝ) * (5 / (2 * (T : ℝ))))
    let k : ℝ :=
      ((5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
        (heathBrownSquareDivisorScale N0 eta ^ 2 * (25 * Real.pi / 8) *
          (25 * Real.pi / 8))
    let a1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (15 * (T : ℝ)⁻¹ * ((N0 * N0 : ℕ) : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        ((2 * ((N0 * N0) / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
    let b1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (((((N0 * N0) / N0 + 1 : ℕ) : ℝ)) * (5 / (2 * (T : ℝ))))
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      a0 + b0 * Real.sqrt (k * (2 * a1 + b1 ^ 2 * k)) := by
  dsimp only
  let J : ℝ := ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
      (heathBrownHalfHeight T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N0 hN0)
        heathBrownDenseUnitWeight t‖ ^ 2
  let I1 : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval (N0 * N0)
        (by simpa using Nat.mul_le_mul hN0 hN0)) heathBrownDenseUnitWeight t‖ ^ 2
  let a0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
      ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
  let b0 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (((N / N0 + 1 : ℕ) : ℝ) * (5 / (2 * (T : ℝ))))
  let k : ℝ :=
    ((5 * Real.pi * Real.exp 1 * X +
        (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
      (heathBrownSquareDivisorScale N0 eta ^ 2 * (25 * Real.pi / 8) *
        (25 * Real.pi / 8))
  let a1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (15 * (T : ℝ)⁻¹ * ((N0 * N0 : ℕ) : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
      ((2 * ((N0 * N0) / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
  let b1 : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (((((N0 * N0) / N0 + 1 : ℕ) : ℝ)) * (5 / (2 * (T : ℝ))))
  have hN0sq : 1 ≤ N0 * N0 := by simpa using Nat.mul_le_mul hN0 hN0
  have hinner := integral_Icc_normSq_heathBrown_fullUnit_le_oneStepSelfBound
    A T hT hA hN0 hN0sq (le_refl _) heta
  have hI1 : I1 ≤ 2 * a1 + b1 ^ 2 * k := by
    simpa only [I1, a1, b1, k] using hinner
  have hhalf : 1 ≤ (heathBrownHalfHeight T : ℝ) := by
    change 1 ≤ (T : ℝ) / 2
    linarith
  have hlift := integral_Icc_normSq_heathBrown_fullUnit_sq_le_ambientSquareLift
    A (heathBrownHalfHeight T) hhalf hA hN0 hN0sq (le_refl _) heta
  have hheight := integral_Icc_normSq_heathBrown_fullUnit_height_mono
    A (N0 * N0) hN0sq
      (V := (heathBrownHalfHeight T : ℝ)) (W := (T : ℝ))
      (by
        change (T : ℝ) / 2 ≤ (T : ℝ)
        linarith [T.property])
  have hMS0 : 0 ≤
      (5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ) :=
    heathBrownSparseMeanSquareEnvelope_nonneg A hA
      (heathBrownHalfHeight T).property.le
  have hk0 : 0 ≤ k := by
    dsimp only [k]
    positivity
  have hJ2I1 : J ^ 2 ≤ k * I1 := by
    calc
      J ^ 2 ≤
          ((5 * Real.pi * Real.exp 1 * X +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) *
            (A.card : ℝ)) *
          (heathBrownSquareDivisorScale N0 eta ^ 2 * (25 * Real.pi / 8) *
            ((25 * Real.pi / 8) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval (N0 * N0) hN0sq)
                    heathBrownDenseUnitWeight t‖ ^ 2)) := by
        simpa only [J] using hlift
      _ ≤ ((5 * Real.pi * Real.exp 1 * X +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) *
            (A.card : ℝ)) *
          (heathBrownSquareDivisorScale N0 eta ^ 2 * (25 * Real.pi / 8) *
            ((25 * Real.pi / 8) * I1)) := by
        gcongr
      _ = k * I1 := by dsimp only [k]; ring
  have hF0 : 0 ≤ 2 * a1 + b1 ^ 2 * k := by
    have hI10 : 0 ≤ I1 := by
      dsimp only [I1]
      exact integral_nonneg fun _ => by positivity
    exact hI10.trans hI1
  have hJ2 : J ^ 2 ≤ k * (2 * a1 + b1 ^ 2 * k) :=
    hJ2I1.trans (mul_le_mul_of_nonneg_left hI1 hk0)
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => by positivity
  have hJ := le_sqrt_of_sq_le_nonneg hJ0 (mul_nonneg hk0 hF0) hJ2
  have hTone : 1 ≤ (T : ℝ) := by linarith
  have hrec := integral_Icc_normSq_heathBrown_factors_le_twoScaleIntegral_arbitrary
    A B eps q T hTone hB hN0
  have houter :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
        a0 + b0 * J := by
    calc
      _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
          (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            ((N / N0 + 1 : ℕ) : ℝ) * ((5 / (2 * (T : ℝ))) * J) +
            ((2 * (N / N0) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
        simpa only [J] using hrec
      _ = a0 + b0 * J := by dsimp only [a0, b0]; ring
  have hb0 : 0 ≤ b0 := by dsimp only [b0]; positivity
  exact houter.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ hb0))

end

end RHTower.Sieve
