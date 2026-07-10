import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryExtrapolation

/-!
# Polynomial parameter family for Baker extrapolation

The exponents are chosen so the auxiliary matrix has more columns than rows while the Schwarz
denominator lives at scale `t ^ (12 * n)` and every positive analytic or height contribution lives
at least one full power of `t` lower.  This strict scale gap drives the final smallness argument.
-/

open scoped Classical
open NumberField

namespace GaloisForLFunctions.RHTower.BakerProof.BakerParameters

/-- Width of the auxiliary exponent box. -/
def exponentWidth (n t : ℕ) : ℕ := t ^ (8 * n - 2)

/-- Number of initial integer samples. -/
def sampleCount (n t : ℕ) : ℕ := t ^ (4 * n)

/-- Multiplicity used in one extrapolation step. -/
def extrapolationOrder (n t : ℕ) : ℕ := t ^ (8 * n)

/-- Multiindex cutoff, leaving half the box available for shifts. -/
def derivativeCutoff (n t : ℕ) : ℕ := 2 * extrapolationOrder n t

/-- Schwarz-disc radius. -/
def extrapolationRadius (n t : ℕ) : ℕ := t ^ (4 * n + 1)

/-- The complete positive factor in the first extrapolation step after the Schwarz node ratio has
been separated off. -/
noncomputable def firstStepGrowth (R : Relation) (c : ℤ) (t : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let T := derivativeCutoff R.n t
  let radius := extrapolationRadius R.n t
  let Hη := R.auxiliaryCoefficientBoundClosed c L S T
  ((L ^ R.n : ℕ) : ℝ) *
      (Hη * Real.exp ((L * R.primeLogWeight) * radius)) *
    (((L ^ R.n : ℕ) : ℝ) *
      (Hη * (R.primeProduct : ℝ) ^ (L * S))) ^
        (Module.finrank ℚ R.CoefficientField - 1)

theorem firstStepGrowth_nonneg (R : Relation) (c : ℤ) (t : ℕ) :
    0 ≤ firstStepGrowth R c t := by
  unfold firstStepGrowth
  dsimp only
  have hH := R.auxiliaryCoefficientBoundClosed_nonneg c
    (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hH (Real.exp_nonneg _)))
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hH (pow_nonneg (Nat.cast_nonneg _) _))) _)

/-- The polynomial parameter family always gives fewer matrix rows than columns once the reduced
relation has arity at least three. -/
theorem dimension_inequality {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    sampleCount n t * derivativeCutoff n t ^ (n - 1) <
      exponentWidth n t ^ n := by
  unfold sampleCount derivativeCutoff extrapolationOrder exponentWidth
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hexp : (8 * n - 2) * n =
      (4 * n + (8 * n) * (n - 1)) + 2 * n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h₁ : 8 * (3 + k) - 2 = 22 + 8 * k := by omega
    have h₂ : 3 + k - 1 = 2 + k := by omega
    rw [h₁, h₂]
    ring
  rw [hexp, pow_add, pow_add]
  have hsmall : 2 ^ (n - 1) < t ^ (2 * n) := by
    apply lt_of_le_of_lt (Nat.pow_le_pow_left ht (n - 1))
    exact Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) ht) (by omega)
  have hpos : 0 < t ^ (4 * n + (8 * n) * (n - 1)) :=
    pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hmul := (Nat.mul_lt_mul_left hpos).2 hsmall
  simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using hmul

@[simp] theorem extrapolationRadius_eq_mul_sampleCount (n t : ℕ) :
    extrapolationRadius n t = t * sampleCount n t := by
  simp [extrapolationRadius, sampleCount, pow_succ, mul_comm]

theorem sampleCount_lt_extrapolationRadius {n t : ℕ} (ht : 2 ≤ t) :
    sampleCount n t < extrapolationRadius n t := by
  unfold sampleCount extrapolationRadius
  exact Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) ht) (by omega)

theorem extrapolationOrder_lt_derivativeCutoff {n t : ℕ} (ht : 2 ≤ t) :
    extrapolationOrder n t < derivativeCutoff n t := by
  simp only [extrapolationOrder, derivativeCutoff]
  have hq : 0 < t ^ (8 * n) := pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  omega

theorem exponentWidth_mul_extrapolationRadius {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t * extrapolationRadius n t = t ^ (12 * n - 1) := by
  unfold exponentWidth extrapolationRadius
  rw [← pow_add]
  congr 1
  omega

theorem extrapolationOrder_mul_sampleCount {n t : ℕ} :
    extrapolationOrder n t * sampleCount n t = t ^ (12 * n) := by
  unfold extrapolationOrder sampleCount
  rw [← pow_add]
  congr 1
  omega

theorem exponentWidth_mul_sampleCount {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t * sampleCount n t = t ^ (12 * n - 2) := by
  unfold exponentWidth sampleCount
  rw [← pow_add]
  congr 1
  omega

/-- The first sample beyond the interpolation set lies in the Schwarz disc. -/
theorem firstNewSample_mem_closedBall {n t : ℕ} (ht : 2 ≤ t) :
    ((sampleCount n t : ℕ) : ℂ) ∈
      Metric.closedBall 0 (extrapolationRadius n t : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Complex.norm_natCast]
  exact_mod_cast (sampleCount_lt_extrapolationRadius ht).le

/-- At the first new sample, the complete Schwarz node ratio is bounded by `(2/3)^(qS)` once
`t ≥ 4`.  Its exponent is exactly the dominant scale `t^(12n)`. -/
theorem firstNewSample_node_ratio_le_two_thirds {n t : ℕ} (ht : 4 ≤ t) :
    let N := extrapolationOrder n t * sampleCount n t
    (((sampleCount n t + sampleCount n t : ℕ) : ℝ) ^ N /
      ((extrapolationRadius n t : ℝ) - sampleCount n t) ^ N) ≤
        ((2 : ℝ) / 3) ^ N := by
  dsimp only
  have hspos : (0 : ℝ) < sampleCount n t := by
    exact_mod_cast (show 0 < sampleCount n t by
      unfold sampleCount
      exact pow_pos (by omega) _)
  have hrpos : (0 : ℝ) < (extrapolationRadius n t : ℝ) - sampleCount n t := by
    exact sub_pos.mpr (by
      exact_mod_cast sampleCount_lt_extrapolationRadius (show 2 ≤ t by omega))
  rw [← div_pow]
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hrpos.le)
  rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 3)]
  rw [extrapolationRadius_eq_mul_sampleCount]
  push_cast
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  nlinarith

/-- With a common integral coefficient scale fixed once and for all, every parameter base produces
a nonzero bounded auxiliary kernel vector. -/
theorem Relation.exists_parameterized_auxiliary_coefficients_of_scale
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    ∃ η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField,
      η ≠ 0 ∧
        Matrix.mulVec (R.auxiliaryMatrix c hint pivot
          (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0 ∧
        ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
          R.auxiliaryCoefficientBoundClosed c
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) := by
  have hL : 0 < exponentWidth R.n t := by
    unfold exponentWidth
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hS : 0 < sampleCount R.n t := by
    unfold sampleCount
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hT : 0 < derivativeCutoff R.n t := by
    unfold derivativeCutoff extrapolationOrder
    positivity
  have hcard := dimension_inequality hn ht
  have hcard' : Fintype.card
      (R.Row pivot (sampleCount R.n t) (derivativeCutoff R.n t)) <
      Fintype.card (R.Column (exponentWidth R.n t)) := by
    simpa using hcard
  obtain ⟨η, hη, hker, hbound⟩ :=
    R.exists_auxiliary_coefficients c hint pivot
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)
      hL hS hT hcard'
  refine ⟨η, hη, hker, fun m => (hbound m).trans ?_⟩
  exact R.auxiliaryCoefficientBound_le_closed c hc hint pivot
    (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) hL hcard

/-- The parameter family discharges every dimension and positivity premise of the Siegel-kernel
construction, including its explicit coefficient-house estimate. -/
theorem Relation.exists_parameterized_auxiliary_coefficients
    (R : Relation) (hn : 3 ≤ R.n) (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    ∃ c : ℤ, c ≠ 0 ∧
      ∃ (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
        (η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField),
        η ≠ 0 ∧
          Matrix.mulVec (R.auxiliaryMatrix c hint pivot
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0 ∧
          ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
            R.auxiliaryCoefficientBoundClosed c
              (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) := by
  obtain ⟨c, hc, hint⟩ := R.exists_common_integer_scale
  have hint' : ∀ i, IsIntegral ℤ (R.scaledCoeff c i) := by
    simpa [Relation.scaledCoeff] using hint
  obtain ⟨η, hη, hker, hbound⟩ :=
    Relation.exists_parameterized_auxiliary_coefficients_of_scale
      R hn c hc hint' pivot t ht
  exact ⟨c, hc, hint', η, hη, hker, hbound⟩

end GaloisForLFunctions.RHTower.BakerProof.BakerParameters
