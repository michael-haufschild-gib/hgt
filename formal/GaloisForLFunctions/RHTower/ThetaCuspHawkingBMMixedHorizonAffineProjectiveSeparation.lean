import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMProjectiveCausalResponse
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy

/-!
# Affine/projective separation of the mixed BM horizon resonance

At the mixed Hawking--Matsubara frequency, the physical BM boundary response is a strictly
negative real projective ratio. Its conjugation cut therefore vanishes. The resonant Frobenius
horizon normalization instead has a nonzero, purely imaginary oriented monodromy.

Thus projectivizing the boundary coefficients deletes the causal variant: both oriented affine
lifts have the same boundary ratio, while their horizon-normalization coordinates differ by the
full monodromy jump. Any nonlinear optical producer must use the augmented bulk-plus-horizon
response, not only a projective Jost ratio.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Physical mixed BM projective boundary response on the real momentum line. -/
def d4BMMixedHorizonProjectiveResponse
    (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMCausalProjectiveBoundaryResponse
    (d4BMCausalPlusMinusFrequency n k (chi : ℂ)) (chi : ℂ)

/-- Conjugation-odd part visible after projectivizing the two boundary coefficients. -/
def d4BMMixedHorizonProjectiveConjugationCut
    (n k : ℕ) (chi : ℝ) : ℂ :=
  d4BMMixedHorizonProjectiveResponse n k chi -
    starRingEnd ℂ (d4BMMixedHorizonProjectiveResponse n k chi)

/-- Projective boundary response deletes the mixed-horizon causal variant. -/
theorem d4BMMixedHorizonProjectiveConjugationCut_eq_zero
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonProjectiveConjugationCut n k chi = 0 := by
  rw [d4BMMixedHorizonProjectiveConjugationCut,
    d4BMMixedHorizonProjectiveResponse,
    d4BMCausalProjectiveBoundaryResponse_plusMinus_real]
  norm_num [map_mul, map_neg, map_ofNat]

/-- Affine horizon monodromy is not the projective conjugation cut. -/
theorem d4BMMixedHorizonMonodromy_ne_projectiveConjugationCut
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi ≠
      d4BMMixedHorizonProjectiveConjugationCut n k chi := by
  rw [d4BMMixedHorizonProjectiveConjugationCut_eq_zero]
  exact d4BMMixedHorizonCounterclockwiseMonodromyJump_ne_zero n k chi

/-- No nonzero affine horizon mode can realize its monodromy through the scalar projective cut. -/
theorem d4BMMixedHorizon_no_projective_monodromy_incidence
    (n k : ℕ) (chi : ℝ) (u : ℂ) (hu : u ≠ 0) :
    d4BMMixedHorizonProjectiveConjugationCut n k chi ≠
      d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi * u := by
  rw [d4BMMixedHorizonProjectiveConjugationCut_eq_zero]
  exact (mul_ne_zero
    (d4BMMixedHorizonCounterclockwiseMonodromyJump_ne_zero n k chi) hu).symm

/-- Centered retarded affine lift: common projective response plus half the oriented horizon
normalization. -/
def d4BMMixedHorizonCenteredRetardedAffineResponse
    (n k : ℕ) (chi : ℝ) : ℂ × ℂ :=
  (d4BMMixedHorizonProjectiveResponse n k chi,
    d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi / 2)

/-- Centered advanced affine lift with the opposite horizon-normalization orientation. -/
def d4BMMixedHorizonCenteredAdvancedAffineResponse
    (n k : ℕ) (chi : ℝ) : ℂ × ℂ :=
  (d4BMMixedHorizonProjectiveResponse n k chi,
    -d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi / 2)

/-- Both affine causal lifts project to the same physical boundary ratio. -/
theorem d4BMMixedHorizonCenteredAffineResponse_fst_eq
    (n k : ℕ) (chi : ℝ) :
    (d4BMMixedHorizonCenteredRetardedAffineResponse n k chi).1 =
      (d4BMMixedHorizonCenteredAdvancedAffineResponse n k chi).1 := by
  rfl

/-- Retarded-minus-advanced affine lift is exactly the vertical horizon monodromy. -/
theorem d4BMMixedHorizonCenteredAffineResponse_sub_eq
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonCenteredRetardedAffineResponse n k chi -
        d4BMMixedHorizonCenteredAdvancedAffineResponse n k chi =
      (0, d4BMMixedHorizonCounterclockwiseMonodromyJump n k chi) := by
  ext <;>
    simp [d4BMMixedHorizonCenteredRetardedAffineResponse,
      d4BMMixedHorizonCenteredAdvancedAffineResponse]
  ring

/-- The augmented affine causal cut is nonzero although its boundary projection is zero. -/
theorem d4BMMixedHorizonCenteredAffineResponse_sub_ne_zero
    (n k : ℕ) (chi : ℝ) :
    d4BMMixedHorizonCenteredRetardedAffineResponse n k chi -
        d4BMMixedHorizonCenteredAdvancedAffineResponse n k chi ≠ 0 := by
  rw [d4BMMixedHorizonCenteredAffineResponse_sub_eq]
  intro hzero
  have hsnd := congrArg Prod.snd hzero
  simp at hsnd
  exact d4BMMixedHorizonCounterclockwiseMonodromyJump_ne_zero n k chi hsnd

end
end RHTower
