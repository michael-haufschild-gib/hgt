import GaloisForLFunctions.RHTower.SymmetricPowerArchimedeanExponents

/-!
# Rank-one complementary-series positivity bound

For the spherical `K`-type, the first raising-operator norm identity has scalar factor
`1/4 - ν²`.  Its factorization has linear factors `1 + 2ν` and `1 - 2ν`.  This file packages both
factors in a two-variable quadratic form and proves that positivity is equivalent to
`|ν| < 1/2`.

This is the local rank-one positivity calculation behind the generic-unitary exponent strip.  It
does not classify all irreducible generic unitary representations or identify their invariant
forms with this model.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Quadratic form packaging the two linear factors in the first spherical `K`-type norm
obstruction. -/
def rankOneKTypeForm (ν : ℝ) (v : ℝ × ℝ) : ℝ :=
  (1 + 2 * ν) * v.1 ^ 2 + (1 - 2 * ν) * v.2 ^ 2

/-- Positive-definiteness of the factorized rank-one form. -/
def RankOneKTypePositive (ν : ℝ) : Prop :=
  ∀ v : ℝ × ℝ, v ≠ 0 → 0 < rankOneKTypeForm ν v

/-- Scalar factor in the first spherical raising-operator norm identity. -/
def sphericalRaisingNormFactor (ν : ℝ) : ℝ :=
  1 / 4 - ν ^ 2

/-- Factorization of the spherical raising-operator norm coefficient. -/
theorem four_mul_sphericalRaisingNormFactor (ν : ℝ) :
    4 * sphericalRaisingNormFactor ν = (1 + 2 * ν) * (1 - 2 * ν) := by
  simp only [sphericalRaisingNormFactor]
  ring

/-- Exact positivity range of the spherical raising-operator norm coefficient. -/
theorem sphericalRaisingNormFactor_pos_iff (ν : ℝ) :
    0 < sphericalRaisingNormFactor ν ↔ |ν| < 1 / 2 := by
  simp only [sphericalRaisingNormFactor]
  rw [abs_lt]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (ν - 1 / 2), sq_nonneg (ν + 1 / 2)]
  · rintro ⟨hleft, hright⟩
    nlinarith

/-- Exact positivity criterion for the factorized rank-one form. -/
theorem rankOneKTypePositive_iff (ν : ℝ) :
    RankOneKTypePositive ν ↔ |ν| < 1 / 2 := by
  constructor
  · intro h
    have hplus := h (1, 0) (by norm_num)
    have hminus := h (0, 1) (by norm_num)
    simp only [rankOneKTypeForm] at hplus hminus
    norm_num at hplus hminus
    rw [abs_lt]
    constructor <;> linarith
  · intro h v hv
    have hb := abs_lt.mp h
    have hplus : 0 < 1 + 2 * ν := by linarith
    have hminus : 0 < 1 - 2 * ν := by linarith
    by_cases hx : v.1 = 0
    · have hy : v.2 ≠ 0 := by
        intro hy
        apply hv
        ext <;> simp [hx, hy]
      simp only [rankOneKTypeForm, hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
        zero_add]
      exact mul_pos hminus (sq_pos_of_ne_zero hy)
    · have hx2 : 0 < v.1 ^ 2 := sq_pos_of_ne_zero hx
      have hy2 : 0 ≤ v.2 ^ 2 := sq_nonneg v.2
      simp only [rankOneKTypeForm]
      positivity

/-- The factorized two-variable form and spherical raising coefficient have the same positivity
locus. -/
theorem rankOneKTypePositive_iff_sphericalRaisingNormFactor (ν : ℝ) :
    RankOneKTypePositive ν ↔ 0 < sphericalRaisingNormFactor ν := by
  rw [rankOneKTypePositive_iff, sphericalRaisingNormFactor_pos_iff]

/-- In Selberg normalization, the spherical raising coefficient is the complementary spectral
eigenvalue. -/
theorem sphericalRaisingNormFactor_eq_eigenvalue (ν : ℝ) :
    sphericalRaisingNormFactor ν = eigenvalueOfComplementaryExponent ν :=
  rfl

/-- Positivity of the factorized rank-one form is equivalent to positivity of the corresponding
Selberg-normalized complementary eigenvalue. -/
theorem rankOneKTypePositive_iff_eigenvalue_pos (ν : ℝ) :
    RankOneKTypePositive ν ↔ 0 < eigenvalueOfComplementaryExponent ν := by
  rw [← sphericalRaisingNormFactor_eq_eigenvalue,
    rankOneKTypePositive_iff_sphericalRaisingNormFactor]

/-- Positivity locus of the rank-one form. -/
theorem rankOneKTypePositive_locus :
    {ν : ℝ | RankOneKTypePositive ν} = Set.Ioo (-1 / 2) (1 / 2) := by
  ext ν
  rw [Set.mem_setOf_eq, rankOneKTypePositive_iff, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The rank-one positivity locus is exactly the degree-one generic-unitary exponent locus. -/
theorem rankOneKTypePositive_locus_eq_degreeOne :
    {ν : ℝ | RankOneKTypePositive ν} = genericUnitarySymPowerLocus 1 := by
  ext ν
  rw [Set.mem_setOf_eq, rankOneKTypePositive_iff,
    mem_genericUnitarySymPowerLocus_succ_iff ν 0]
  norm_num

end

end GaloisForLFunctions.RHTower
