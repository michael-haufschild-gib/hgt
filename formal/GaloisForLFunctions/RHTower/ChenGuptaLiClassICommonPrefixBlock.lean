/-
# Chen--Gupta--Li Class-I common prefix block

Materializes every finite oscillatory prefix as a zero-padded vector of the
source-common Möbius coefficients `c_n`, with a common deterministic scale.
This is the finite carrier produced by Abel deweighting before the remaining
packet grouping step.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIWeightVariation
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIRescaling

open Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Zero-padded initial segment of the source Class-I coefficient block. -/
def cglClassIPrefixDetectorCoefficients (X N : ℕ) (K : Fin (N + 1)) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    if j.1 < K.1 then
      (zeroDetectionMobiusCoefficient X (cglCharacterDyadicIndex N j) : ℂ)
    else 0)

/-- The source character polynomial with a zero-padded common-coefficient prefix. -/
def cglClassIPrefixDetectorPolynomial (X N q : ℕ) (K : Fin (N + 1))
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) : ℂ :=
  cglCharacterDyadicPolynomial N (q + 1) (cglShiftedTailDyadicRow χ s)
    (cglClassIPrefixDetectorCoefficients X N K)

/-- Exact identification of a prefix common-coefficient polynomial with the
corresponding oscillatory partial sum. -/
theorem cglClassIPrefixDetectorPolynomial_eq_partialSum (X N q : ℕ)
    (K : Fin (N + 1)) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) :
    cglClassIPrefixDetectorPolynomial X N q K χ s =
      cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K.1 := by
  unfold cglClassIPrefixDetectorPolynomial cglCharacterDyadicPolynomial
    cglClassIPrefixDetectorCoefficients cglComplexPartialSum
  rw [Finset.sum_fin_eq_sum_range]
  symm
  refine Finset.sum_subset_zero_on_sdiff
    (Finset.range_subset_range.mpr (Nat.lt_succ_iff.mp K.2)) ?_ ?_
  · intro k hk
    rw [Finset.mem_sdiff] at hk
    simp only [Finset.mem_range] at hk
    simp [hk.1, hk.2]
  · intro k hk
    simp only [Finset.mem_range] at hk
    have hkN : k < N := lt_of_lt_of_le hk (Nat.lt_succ_iff.mp K.2)
    simp [cglShiftedTailDyadicOscillatorySequence, hkN, hk,
      cglShiftedTailDyadicOscillatoryTerm, cglShiftedTailDyadicRow]

/-- The common deterministic scaling applied to a zero-padded Class-I prefix. -/
def cglClassIPrefixScaledCoefficients (X N : ℕ) (K : Fin (N + 1)) :
    EuclideanSpace ℂ (Fin N) :=
  (cglClassIDyadicCoefficientScale X N : ℂ) • cglClassIPrefixDetectorCoefficients X N K

/-- The bounded-coefficient prefix polynomial used by later large-value layers. -/
def cglClassIPrefixScaledDetectorPolynomial (X N q : ℕ) (K : Fin (N + 1))
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) : ℂ :=
  cglCharacterDyadicPolynomial N (q + 1) (cglShiftedTailDyadicRow χ s)
    (cglClassIPrefixScaledCoefficients X N K)

/-- Every scaled zero-padded Class-I prefix coefficient is bounded by one. -/
theorem norm_cglClassIPrefixScaledCoefficient_le_one (X N : ℕ)
    (K : Fin (N + 1)) (j : Fin N) :
    ‖(cglClassIPrefixScaledCoefficients X N K) j‖ ≤ 1 := by
  by_cases hj : j.1 < K.1
  · simpa [cglClassIPrefixScaledCoefficients, cglClassIPrefixDetectorCoefficients,
      cglClassIDyadicScaledCoefficients, cglClassIDyadicDetectorCoefficients,
      hj, cglCharacterDyadicIndex, smul_eq_mul] using
      norm_cglClassIDyadicScaledCoefficient_le_one X N j
  · simp [cglClassIPrefixScaledCoefficients, cglClassIPrefixDetectorCoefficients, hj]

/-- Scaling relation for the common Class-I prefix polynomial. -/
theorem cglClassIPrefixScaledDetectorPolynomial_eq_scale_mul (X N q : ℕ)
    (K : Fin (N + 1)) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) :
    cglClassIPrefixScaledDetectorPolynomial X N q K χ s =
      (cglClassIDyadicCoefficientScale X N : ℂ) *
        cglClassIPrefixDetectorPolynomial X N q K χ s := by
  simp only [cglClassIPrefixScaledDetectorPolynomial,
    cglClassIPrefixDetectorPolynomial, cglCharacterDyadicPolynomial,
    cglClassIPrefixScaledCoefficients, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Scaling relation directly to the common oscillatory partial sum. -/
theorem cglClassIPrefixScaledDetectorPolynomial_eq_scale_mul_partialSum (X N q : ℕ)
    (K : Fin (N + 1)) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) :
    cglClassIPrefixScaledDetectorPolynomial X N q K χ s =
      (cglClassIDyadicCoefficientScale X N : ℂ) *
        cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K.1 := by
  rw [cglClassIPrefixScaledDetectorPolynomial_eq_scale_mul,
    cglClassIPrefixDetectorPolynomial_eq_partialSum]

/-- A certified prefix attains the finite common-oscillatory maximum. -/
theorem exists_cglClassIPrefixDetectorPolynomial_norm_eq_prefixNormMaximum
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    ∃ K : Fin (N + 1),
      ‖cglClassIPrefixDetectorPolynomial X N q K χ s‖ =
        cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
  let S : Finset ℕ := Finset.range (N + 1)
  let H : S.Nonempty := ⟨0, by
    simp only [S, Finset.mem_range]
    omega⟩
  let f : ℕ → ℝ := fun K =>
    ‖cglComplexPartialSum (cglShiftedTailDyadicOscillatorySequence X N q χ s) K‖
  obtain ⟨K, hK, hmax⟩ := Finset.exists_mem_eq_sup' H f
  refine ⟨⟨K, by
    simpa [S] using hK⟩, ?_⟩
  rw [cglClassIPrefixDetectorPolynomial_eq_partialSum]
  simpa [cglShiftedTailDyadicPrefixNormMaximum, S, H, f] using hmax.symm

/-- The corresponding scaled common prefix attains scaled finite maximum. -/
theorem exists_cglClassIPrefixScaledDetectorPolynomial_norm_eq_scale_mul_prefixNormMaximum
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    ∃ K : Fin (N + 1),
      ‖cglClassIPrefixScaledDetectorPolynomial X N q K χ s‖ =
        cglClassIDyadicCoefficientScale X N *
          cglShiftedTailDyadicPrefixNormMaximum X N q χ s := by
  obtain ⟨K, hK⟩ :=
    exists_cglClassIPrefixDetectorPolynomial_norm_eq_prefixNormMaximum X N q χ s
  refine ⟨K, ?_⟩
  rw [cglClassIPrefixScaledDetectorPolynomial_eq_scale_mul,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by
      unfold cglClassIDyadicCoefficientScale
      positivity), hK]

/-- A selected bounded common-coefficient prefix dominates the normalized
literal weighted tail after multiplication by only closed nonnegative factors. -/
theorem exists_cglClassIPrefixScaledDetectorPolynomial_weighted_dominates_tail
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ∃ K : Fin (N + 1),
      cglClassIDyadicCoefficientScale X N *
        ‖cglShiftedTailDyadicScaledPolynomial X N q χ s x‖ ≤
        cglShiftedTailDyadicCoefficientScale X N s x *
          cglShiftedTailDyadicRealWeightSequence N s x 0 *
            ‖cglClassIPrefixScaledDetectorPolynomial X N q K χ s‖ := by
  obtain ⟨K, hK⟩ :=
    exists_cglClassIPrefixScaledDetectorPolynomial_norm_eq_scale_mul_prefixNormMaximum X N q χ s
  refine ⟨K, ?_⟩
  have hfull : 0 ≤ cglClassIDyadicCoefficientScale X N := by
    unfold cglClassIDyadicCoefficientScale
    positivity
  have hshift : 0 ≤ cglShiftedTailDyadicCoefficientScale X N s x := by
    unfold cglShiftedTailDyadicCoefficientScale
    positivity
  have hweight : 0 ≤ cglShiftedTailDyadicRealWeightSequence N s x 0 :=
    cglShiftedTailDyadicRealWeightSequence_nonneg N s x 0
  rw [cglShiftedTailDyadicScaledPolynomial_factor, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hshift]
  calc
    cglClassIDyadicCoefficientScale X N *
        (cglShiftedTailDyadicCoefficientScale X N s x *
          ‖∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
            (cglShiftedTailDyadicRealWeight N s x j : ℂ)‖) ≤
        cglClassIDyadicCoefficientScale X N *
          (cglShiftedTailDyadicCoefficientScale X N s x *
            (cglShiftedTailDyadicRealWeightSequence N s x 0 *
              cglShiftedTailDyadicPrefixNormMaximum X N q χ s)) := by
      gcongr
      exact norm_cglShiftedTailDyadicWeightedBlock_le_initial_mul_prefixNormMaximum X N q χ s x
    _ = cglShiftedTailDyadicCoefficientScale X N s x *
          cglShiftedTailDyadicRealWeightSequence N s x 0 *
            ‖cglClassIPrefixScaledDetectorPolynomial X N q K χ s‖ := by
      rw [hK]
      ring

end RHTower
