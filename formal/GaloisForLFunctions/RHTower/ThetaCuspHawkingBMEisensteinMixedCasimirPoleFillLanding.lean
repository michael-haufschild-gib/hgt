import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualUnfoldedScalarNormalizationNoGo

/-!
# Mixed-Casimir pole-fill landing for the actual HB scalar source

The literal repeated-leg triple-Eisenstein unfolding produces four completed-Lambda channels with
spectral parameters

```text
2P+Q-1, Q, Q, 2P-Q.
```

Turning each completed-Lambda factor into the corpus canonical Xi factor forces multiplication by
the product of half-Casimir weights `s(s-1)/2` in these four channels.  This module proves three
new structural facts about that correction.

First, the multiplier is the mixed discriminant

```text
Q²(Q-1)²/16 * ((2P-1)²-Q²) * ((2P-1)²-(Q-1)²).
```

Second, its exact external-leg separation rank is three.  An explicit three-channel decomposition
gives the upper bound.  A closed `3 x 3` determinant obstruction at nine points of the strict
absolute-convergence chamber rules out every sum of at most two arbitrary separated channels.
Thus neither independent external-leg normalization nor any two-channel boundary repair can
produce the canonical pole fill.

Third, the forced mixed correction equals `2800` at the actual audit point `(P,Q)=(2,5)`.  Dressing
the literal unfolded source, or any allowed diagonal analytic-family regularized value, then lands
exactly on the canonical four-Xi scalar vertex.  Nonvanishing of the literal source makes this
correction unique.

This discharges the corrected scalar-normalization premise at the honest chamber point in the HB
chain

```text
mixed source Casimir dressing -> canonical scalar landing -> C-A.9u
  -> negative BM -> left QNM -> HC94 source/clock
  -> horizon-boundary cocycle -> source-global gain equality -> RH.
```

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HB] [C-A.9x-e]`
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- Half the centered Eisenstein Casimir eigenvalue: the elementary factor that turns a completed
Lambda channel into its pole-filled Xi channel. -/
def d4BMPoleFillCasimirWeight (s : ℂ) : ℂ := s * (s - 1) / 2

/-- Four-channel pole-fill multiplier forced by the diagonal triple-Eisenstein spectrum. -/
def d4BMMixedCasimirPoleFillMultiplier (P Q : ℂ) : ℂ :=
  d4BMPoleFillCasimirWeight (2 * P + Q - 1) *
    d4BMPoleFillCasimirWeight Q ^ (2 : ℕ) *
    d4BMPoleFillCasimirWeight (2 * P - Q)

/-- Strict absolute-convergence chamber used by the repeated-leg unfolding. -/
def d4BMStrictTripleUnfoldingChamber (P Q : ℂ) : Prop :=
  1 < P.re ∧ 2 * P.re < Q.re

/-- The pole-fill weight is literally half the geometric Casimir eigenvalue. -/
theorem d4BMPoleFillCasimirWeight_eq_geometricEigenvalue (s : ℂ) :
    d4BMPoleFillCasimirWeight s =
      thetaCuspHawkingEisensteinGeometricEigenvalue (s - 1 / 2) / 2 := by
  rw [thetaCuspHawkingEisensteinGeometricEigenvalue_centered]
  rfl

/-- Exact mixed-discriminant factorization of the forced four-channel multiplier. -/
theorem d4BMMixedCasimirPoleFillMultiplier_eq_mixedDiscriminants (P Q : ℂ) :
    d4BMMixedCasimirPoleFillMultiplier P Q =
      Q ^ (2 : ℕ) * (Q - 1) ^ (2 : ℕ) / 16 *
        ((2 * P - 1) ^ (2 : ℕ) - Q ^ (2 : ℕ)) *
        ((2 * P - 1) ^ (2 : ℕ) - (Q - 1) ^ (2 : ℕ)) := by
  simp only [d4BMMixedCasimirPoleFillMultiplier, d4BMPoleFillCasimirWeight]
  ring

/-- Three separated source channels suffice for the forced mixed counterterm. -/
theorem d4BMMixedCasimirPoleFillMultiplier_threeChannel (P Q : ℂ) :
    d4BMMixedCasimirPoleFillMultiplier P Q =
      (2 * P - 1) ^ (4 : ℕ) * (Q ^ (2 : ℕ) * (Q - 1) ^ (2 : ℕ) / 16) +
      (2 * P - 1) ^ (2 : ℕ) *
        (-(Q ^ (2 : ℕ) * (Q - 1) ^ (2 : ℕ) / 16 * (Q ^ (2 : ℕ) + (Q - 1) ^ (2 : ℕ)))) +
      1 * (Q ^ (2 : ℕ) * (Q - 1) ^ (2 : ℕ) / 16 * (Q ^ (2 : ℕ) * (Q - 1) ^ (2 : ℕ))) := by
  rw [d4BMMixedCasimirPoleFillMultiplier_eq_mixedDiscriminants]
  ring

/-- Explicit determinant used to detect separation rank at least three. -/
def d4BMThreeByThreeDet
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : ℂ) : ℂ :=
  a₀₀ * (a₁₁ * a₂₂ - a₁₂ * a₂₁) -
    a₀₁ * (a₁₀ * a₂₂ - a₁₂ * a₂₀) +
    a₀₂ * (a₁₀ * a₂₁ - a₁₁ * a₂₀)

private theorem d4BMThreeByThreeDet_twoSeparated_eq_zero
    (f₀ f₁ g₀ g₁ : ℂ → ℂ) (P₀ P₁ P₂ Q₀ Q₁ Q₂ : ℂ) :
    d4BMThreeByThreeDet
      (f₀ P₀ * g₀ Q₀ + f₁ P₀ * g₁ Q₀)
      (f₀ P₀ * g₀ Q₁ + f₁ P₀ * g₁ Q₁)
      (f₀ P₀ * g₀ Q₂ + f₁ P₀ * g₁ Q₂)
      (f₀ P₁ * g₀ Q₀ + f₁ P₁ * g₁ Q₀)
      (f₀ P₁ * g₀ Q₁ + f₁ P₁ * g₁ Q₁)
      (f₀ P₁ * g₀ Q₂ + f₁ P₁ * g₁ Q₂)
      (f₀ P₂ * g₀ Q₀ + f₁ P₂ * g₁ Q₀)
      (f₀ P₂ * g₀ Q₁ + f₁ P₂ * g₁ Q₁)
      (f₀ P₂ * g₀ Q₂ + f₁ P₂ * g₁ Q₂) = 0 := by
  simp only [d4BMThreeByThreeDet]
  ring

/-- No correction with at most two arbitrary separated external-leg channels can implement the
forced four-Xi pole fill throughout the actual unfolding chamber. -/
theorem no_d4BMTwoChannelLegwisePoleFillNormalization :
    ¬ ∃ f₀ f₁ g₀ g₁ : ℂ → ℂ,
      ∀ P Q : ℂ, d4BMStrictTripleUnfoldingChamber P Q →
        d4BMMixedCasimirPoleFillMultiplier P Q =
          f₀ P * g₀ Q + f₁ P * g₁ Q := by
  rintro ⟨f₀, f₁, g₀, g₁, h⟩
  have h₀₀ := h (3 / 2) 6 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₀₁ := h (3 / 2) 7 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₀₂ := h (3 / 2) 8 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₁₀ := h 2 6 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₁₁ := h 2 7 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₁₂ := h 2 8 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₂₀ := h (5 / 2) 6 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₂₁ := h (5 / 2) 7 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have h₂₂ := h (5 / 2) 8 (by norm_num [d4BMStrictTripleUnfoldingChamber])
  have hdet := d4BMThreeByThreeDet_twoSeparated_eq_zero f₀ f₁ g₀ g₁
    (3 / 2) 2 (5 / 2) 6 7 8
  rw [← h₀₀, ← h₀₁, ← h₀₂,
    ← h₁₀, ← h₁₁, ← h₁₂,
    ← h₂₀, ← h₂₁, ← h₂₂] at hdet
  norm_num [d4BMThreeByThreeDet, d4BMMixedCasimirPoleFillMultiplier,
    d4BMPoleFillCasimirWeight] at hdet

/-- The source-derived mixed Casimir correction has the forced calibration `2800`. -/
theorem d4BMMixedCasimirPoleFillMultiplier_two_five :
    d4BMMixedCasimirPoleFillMultiplier 2 5 = 2800 := by
  norm_num [d4BMMixedCasimirPoleFillMultiplier, d4BMPoleFillCasimirWeight]

/-- The same law recovers the earlier diagonal audit ratio `10`. -/
theorem d4BMMixedCasimirPoleFillMultiplier_two_two :
    d4BMMixedCasimirPoleFillMultiplier 2 2 = 10 := by
  norm_num [d4BMMixedCasimirPoleFillMultiplier, d4BMPoleFillCasimirWeight]

/-- The mixed Casimir dressing of the literal source lands exactly on the canonical vertex. -/
theorem d4BM_mixedCasimirCorrectedActualUnfoldedSource_two_five_eq_canonical :
    d4BMMixedCasimirPoleFillMultiplier 2 5 *
        d4BMActualTwoFiveUnfoldedScalarSource =
      d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BMMixedCasimirPoleFillMultiplier_two_five]
  exact d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five.symm

/-- Mixed Casimir correction of every allowed analytic-family scalar value. -/
def d4BMTwoFiveMixedCasimirCorrectedScalarValue
    (coefficient : Bool → Bool → Bool → ℂ) : ℂ :=
  d4BMMixedCasimirPoleFillMultiplier 2 5 *
    d4BMTwoFiveAnalyticFamilyRegularizedScalarValue coefficient

/-- Corrected scalar landing is independent of every allowed boundary-family coefficient. -/
theorem d4BM_twoFiveMixedCasimirCorrectedScalarValue_eq_canonical
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMTwoFiveMixedCasimirCorrectedScalarValue coefficient =
      d4BMActualCanonicalScalarTripleVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BMTwoFiveMixedCasimirCorrectedScalarValue,
    d4BMMixedCasimirPoleFillMultiplier_two_five]
  exact
    (d4BM_canonicalScalarVertex_eq_2800_mul_analyticFamilyRegularizedScalarValue_two_five
      coefficient).symm

/-- The corrected scalar source closes the boundary-free C-A.9u balanced landing at `(2,5)`. -/
theorem d4BM_mixedCasimirCorrectedActualUnfoldedSource_balanced_eq_canonical :
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (d4BMEisensteinAbsoluteConvergenceParameterTwo.s *
            (d4BMEisensteinAbsoluteConvergenceParameterTwo.s - 1))
          (d4BMEisensteinAbsoluteConvergenceParameterFive.s *
            (d4BMEisensteinAbsoluteConvergenceParameterFive.s - 1)) *
        (d4BMMixedCasimirPoleFillMultiplier 2 5 *
          d4BMActualTwoFiveUnfoldedScalarSource) =
      d4BMActualCanonicalBalancedSpinTwoVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BM_mixedCasimirCorrectedActualUnfoldedSource_two_five_eq_canonical]
  exact
    (d4BM_actualCanonicalBalancedSpinTwoVertex_eq
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterFive).symm

/-- Every corrected analytic-family scalar value closes the same boundary-free C-A.9u landing. -/
theorem d4BM_twoFiveMixedCasimirCorrectedBalancedValue_eq_canonical
    (coefficient : Bool → Bool → Bool → ℂ) :
    d4BMHyperbolicBalancedSpinTwoBochnerCoefficient
          (d4BMEisensteinAbsoluteConvergenceParameterTwo.s *
            (d4BMEisensteinAbsoluteConvergenceParameterTwo.s - 1))
          (d4BMEisensteinAbsoluteConvergenceParameterFive.s *
            (d4BMEisensteinAbsoluteConvergenceParameterFive.s - 1)) *
        d4BMTwoFiveMixedCasimirCorrectedScalarValue coefficient =
      d4BMActualCanonicalBalancedSpinTwoVertex
        d4BMEisensteinAbsoluteConvergenceParameterTwo
        d4BMEisensteinAbsoluteConvergenceParameterFive := by
  rw [d4BM_twoFiveMixedCasimirCorrectedScalarValue_eq_canonical]
  exact
    (d4BM_actualCanonicalBalancedSpinTwoVertex_eq
      d4BMEisensteinAbsoluteConvergenceParameterTwo
      d4BMEisensteinAbsoluteConvergenceParameterFive).symm

/-- Nonvanishing makes `2800` the unique multiplicative correction of the literal source. -/
theorem d4BM_actualUnfoldedSource_correction_eq_canonical_iff (c : ℂ) :
    c * d4BMActualTwoFiveUnfoldedScalarSource =
        d4BMActualCanonicalScalarTripleVertex
          d4BMEisensteinAbsoluteConvergenceParameterTwo
          d4BMEisensteinAbsoluteConvergenceParameterFive ↔
      c = 2800 := by
  constructor
  · intro h
    rw [d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five] at h
    exact mul_right_cancel₀ d4BM_actualTwoFiveUnfoldedScalarSource_ne_zero h
  · intro h
    rw [h]
    exact d4BM_canonicalScalarVertex_eq_2800_mul_actualUnfoldedSource_two_five.symm

end RHTower
