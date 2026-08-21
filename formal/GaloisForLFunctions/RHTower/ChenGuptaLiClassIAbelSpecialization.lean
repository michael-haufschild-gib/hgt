/-
# Chen--Gupta--Li Class-I Abel specialization

Places CGL's literal finite dyadic weighted block into the exact finite Abel
identity.  The oscillatory sequence is separated from its positive real
`n^{-Re rho} exp(-n/Y)` weight, but no common-block conclusion is asserted.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIWeightFactor

open Complex

noncomputable section

namespace RHTower

/-- The zero-independent oscillatory part of the finite Class-I block,
extended by zero beyond its dyadic length. -/
def cglShiftedTailDyadicOscillatorySequence (X N q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) (k : ℕ) : ℂ :=
  if hk : k < N then
    cglShiftedTailDyadicOscillatoryTerm X N q χ s ⟨k, hk⟩
  else 0

/-- The literal positive real weight of the finite Class-I block,
extended by zero beyond its dyadic length. -/
def cglShiftedTailDyadicRealWeightSequence (N : ℕ)
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (k : ℕ) : ℝ :=
  if hk : k < N then
    cglShiftedTailDyadicRealWeight N s x ⟨k, hk⟩
  else 0

/-- The finite Class-I weighted block is its range-indexed sequence form. -/
theorem cglShiftedTailDyadicWeightedBlock_eq_range
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    (∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
      (cglShiftedTailDyadicRealWeight N s x j : ℂ)) =
      ∑ k ∈ Finset.range N,
        cglShiftedTailDyadicOscillatorySequence X N q χ s k *
          (cglShiftedTailDyadicRealWeightSequence N s x k : ℂ) := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [cglShiftedTailDyadicOscillatorySequence,
    cglShiftedTailDyadicRealWeightSequence, Finset.mem_range.mp hk]

/-- Exact finite Abel identity for CGL's literal Class-I weighted block. -/
theorem cglShiftedTailDyadicWeightedBlock_abel
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    (∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
      (cglShiftedTailDyadicRealWeight N s x j : ℂ)) =
      (cglShiftedTailDyadicRealWeightSequence N s x (N - 1) : ℂ) *
        cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) N -
        ∑ k ∈ Finset.range (N - 1),
          ((cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
            cglShiftedTailDyadicRealWeightSequence N s x k : ℝ) : ℂ) *
            cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) (k + 1) := by
  rw [cglShiftedTailDyadicWeightedBlock_eq_range]
  exact cglComplexAbelSummation
    (cglShiftedTailDyadicOscillatorySequence X N q χ s)
    (cglShiftedTailDyadicRealWeightSequence N s x) N

/-- Norm envelope from Abel summation for CGL's literal Class-I block. -/
theorem norm_cglShiftedTailDyadicWeightedBlock_le_abelEnvelope
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ‖∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
      (cglShiftedTailDyadicRealWeight N s x j : ℂ)‖ ≤
      |cglShiftedTailDyadicRealWeightSequence N s x (N - 1)| *
        ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) N‖ +
        ∑ k ∈ Finset.range (N - 1),
          |cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
            cglShiftedTailDyadicRealWeightSequence N s x k| *
            ‖cglComplexPartialSum
              (cglShiftedTailDyadicOscillatorySequence X N q χ s) (k + 1)‖ := by
  rw [cglShiftedTailDyadicWeightedBlock_eq_range]
  exact norm_cglComplexAbelSummation_le
    (cglShiftedTailDyadicOscillatorySequence X N q χ s)
    (cglShiftedTailDyadicRealWeightSequence N s x) N

/-- Exact Abel representation of the normalized literal Class-I polynomial. -/
theorem cglShiftedTailDyadicScaledPolynomial_abel
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    cglShiftedTailDyadicScaledPolynomial X N q χ s x =
      (cglShiftedTailDyadicCoefficientScale X N s x : ℂ) *
        ((cglShiftedTailDyadicRealWeightSequence N s x (N - 1) : ℂ) *
          cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) N -
          ∑ k ∈ Finset.range (N - 1),
            ((cglShiftedTailDyadicRealWeightSequence N s x (k + 1) -
              cglShiftedTailDyadicRealWeightSequence N s x k : ℝ) : ℂ) *
              cglComplexPartialSum
                (cglShiftedTailDyadicOscillatorySequence X N q χ s) (k + 1)) := by
  rw [cglShiftedTailDyadicScaledPolynomial_factor,
    cglShiftedTailDyadicWeightedBlock_abel]

end RHTower
