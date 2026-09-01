import GaloisForLFunctions.HTGeometry.LiteralSourceReflectionDeterminantCocycle

/-!
# Literal-source reflection rank-gauge linearization

The raw marked-edge reflection cocycle has a quadratic block exponent.  Multiplication at rank `m`
by the source-visible character monomial `(z⁻¹)^m` puts every edge in the constant normal form
`1-z`.  In that rank frame, reflection has constant multiplier `-z⁻¹`; the quadratic rate is an
exact gauge coboundary rather than invariant reflection curvature.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower

/-- Source edge after removal of its predictable rank-character transport. -/
def rankAnchoredComplexCharacterEdge (z : ℂ) (m : ℕ) : ℂ :=
  (z⁻¹) ^ m * complexCharacterEdge z m

/-- Rank normalization puts every nonzero-character edge in the constant normal form `1-z`. -/
theorem rankAnchoredComplexCharacterEdge_eq
    {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    rankAnchoredComplexCharacterEdge z m = 1 - z := by
  have hcancel : (z⁻¹) ^ m * z ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  rw [rankAnchoredComplexCharacterEdge, complexCharacterEdge,
    show z ^ (m + 1) = z ^ m * z by rw [pow_succ]]
  calc
    (z⁻¹) ^ m * (z ^ m - z ^ m * z) =
        ((z⁻¹) ^ m * z ^ m) * (1 - z) := by ring
    _ = 1 - z := by rw [hcancel, one_mul]

/-- The rank-anchored edge is independent of the source rank. -/
theorem rankAnchoredComplexCharacterEdge_rank_independent
    {z : ℂ} (hz : z ≠ 0) (m n : ℕ) :
    rankAnchoredComplexCharacterEdge z m =
      rankAnchoredComplexCharacterEdge z n := by
  rw [rankAnchoredComplexCharacterEdge_eq hz,
    rankAnchoredComplexCharacterEdge_eq hz]

/-- Residual reflection character in the rank-normal frame. -/
def rankAnchoredReflectionMultiplier (z : ℂ) : ℂ := -z⁻¹

/-- Reflection of a rank-normal edge has the constant multiplier `-z⁻¹`. -/
theorem rankAnchoredComplexCharacterEdge_inv_eq
    {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    rankAnchoredComplexCharacterEdge z⁻¹ m =
      rankAnchoredReflectionMultiplier z * rankAnchoredComplexCharacterEdge z m := by
  rw [rankAnchoredComplexCharacterEdge_eq (inv_ne_zero hz),
    rankAnchoredComplexCharacterEdge_eq hz, rankAnchoredReflectionMultiplier]
  field_simp [hz]
  ring

/-- Exact pointwise change-of-frame identity: the odd-power multiplier is conjugated to the
rank-independent residual character. -/
theorem complexCharacterEdgeReflectionMultiplier_rankGaugeConjugation
    {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    z ^ m * complexCharacterEdgeReflectionMultiplier z m * z ^ m =
      rankAnchoredReflectionMultiplier z := by
  have hcancelLeft : z ^ m * (z⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have hcancelRight : (z⁻¹) ^ m * z ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  rw [complexCharacterEdgeReflectionMultiplier, rankAnchoredReflectionMultiplier,
    show 2 * m + 1 = m + (m + 1) by omega, pow_add, pow_succ]
  calc
    z ^ m * (-((z⁻¹) ^ m * ((z⁻¹) ^ m * z⁻¹))) * z ^ m =
        -(z ^ m * (z⁻¹) ^ m) * ((z⁻¹) ^ m * z ^ m) * z⁻¹ := by ring
    _ = -z⁻¹ := by rw [hcancelLeft, hcancelRight]; ring

/-- Accumulated residual reflection character after rank normalization. -/
def rankAnchoredReflectionBlockMultiplier (z : ℂ) (n : ℕ) : ℂ :=
  rankAnchoredReflectionMultiplier z ^ n

/-- Rank-normal reflected blocks accumulate linearly in block length, independently of base rank. -/
theorem prod_rankAnchoredComplexCharacterEdge_inv_eq
    {z : ℂ} (hz : z ≠ 0) (M n : ℕ) :
    (∏ j ∈ Finset.range n,
        rankAnchoredComplexCharacterEdge z⁻¹ (M + j)) =
      rankAnchoredReflectionBlockMultiplier z n *
        ∏ j ∈ Finset.range n, rankAnchoredComplexCharacterEdge z (M + j) := by
  simp_rw [rankAnchoredComplexCharacterEdge_inv_eq hz]
  rw [Finset.prod_mul_distrib]
  simp [rankAnchoredReflectionBlockMultiplier]

/-- Product of the two rank-frame factors used to conjugate a raw reflection block. -/
def complexCharacterRankGaugeBlock (z : ℂ) (M n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, z ^ (M + j)

/-- Exact block coboundary identity: quadratic raw accumulation becomes a linear residual power. -/
theorem reflectionBlockMultiplier_rankGaugeConjugation
    {z : ℂ} (hz : z ≠ 0) (M n : ℕ) :
    complexCharacterRankGaugeBlock z M n *
        complexCharacterEdgeReflectionBlockMultiplier z M n *
        complexCharacterRankGaugeBlock z M n =
      rankAnchoredReflectionBlockMultiplier z n := by
  rw [complexCharacterRankGaugeBlock,
    complexCharacterEdgeReflectionBlockMultiplier,
    rankAnchoredReflectionBlockMultiplier]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ j ∈ Finset.range n,
        z ^ (M + j) * complexCharacterEdgeReflectionMultiplier z (M + j) *
          z ^ (M + j)) =
        ∏ _j ∈ Finset.range n, rankAnchoredReflectionMultiplier z := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact complexCharacterEdgeReflectionMultiplier_rankGaugeConjugation hz (M + j)
    _ = rankAnchoredReflectionMultiplier z ^ n := by simp

/-- Rank-normal marked execution of one actual normalized depth-12 source channel. -/
def rankTwelveLiteralSourceRankAnchoredExecution
    (p : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  (z⁻¹) ^ (12 + j) * rankTwelveLiteralSourceMarkedExecution p z j

/-- Every actual marked source channel has the same rank-normal execution `1-z`. -/
theorem rankTwelveLiteralSourceRankAnchoredExecution_eq
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ≠ 0) (j : ℕ) :
    rankTwelveLiteralSourceRankAnchoredExecution p z j = 1 - z := by
  rw [rankTwelveLiteralSourceRankAnchoredExecution,
    rankTwelveLiteralSourceMarkedExecution_eq hp]
  exact rankAnchoredComplexCharacterEdge_eq hz (12 + j)

/-- Actual rank-growing source blocks obey the same linear residual reflection law. -/
theorem prod_rankTwelveLiteralSourceRankAnchoredExecution_inv_eq
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ≠ 0) (M n : ℕ) :
    (∏ j ∈ Finset.range n,
        rankTwelveLiteralSourceRankAnchoredExecution p z⁻¹ (M + j)) =
      rankAnchoredReflectionBlockMultiplier z n *
        ∏ j ∈ Finset.range n,
          rankTwelveLiteralSourceRankAnchoredExecution p z (M + j) := by
  simp_rw [rankTwelveLiteralSourceRankAnchoredExecution_eq hp (inv_ne_zero hz),
    rankTwelveLiteralSourceRankAnchoredExecution_eq hp hz]
  have hreflect :
      1 - z⁻¹ = rankAnchoredReflectionMultiplier z * (1 - z) := by
    rw [rankAnchoredReflectionMultiplier]
    field_simp [hz]
    ring
  simp_rw [hreflect]
  rw [Finset.prod_mul_distrib]
  simp [rankAnchoredReflectionBlockMultiplier]

/-- Nonempty residual reflection block is unitary exactly on the unit circle. -/
theorem norm_rankAnchoredReflectionBlockMultiplier_eq_one_iff
    {z : ℂ} {n : ℕ} (hn : 0 < n) :
    ‖rankAnchoredReflectionBlockMultiplier z n‖ = 1 ↔ ‖z‖ = 1 := by
  rw [rankAnchoredReflectionBlockMultiplier, norm_pow]
  simp only [rankAnchoredReflectionMultiplier, norm_neg, norm_inv]
  rw [pow_eq_one_iff_of_nonneg (inv_nonneg.mpr (norm_nonneg z)) hn.ne']
  simp [inv_eq_one]

/-- For prime-radial characters, residual unitarity is exactly zero real drift. -/
theorem primeRadial_norm_rankAnchoredReflectionBlockMultiplier_eq_one_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖rankAnchoredReflectionBlockMultiplier
        ((Real.rpow (p : ℝ) ν : ℝ) : ℂ) n‖ = 1 ↔ ν = 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  calc
    ‖rankAnchoredReflectionBlockMultiplier
        ((Real.rpow (p : ℝ) ν : ℝ) : ℂ) n‖ = 1 ↔
        ‖((Real.rpow (p : ℝ) ν : ℝ) : ℂ)‖ = 1 :=
      norm_rankAnchoredReflectionBlockMultiplier_eq_one_iff hn
    _ ↔ ν = 0 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < Real.rpow (p : ℝ) ν :=
        Real.rpow_pos_of_pos hp0 ν
      have habs : |Real.rpow (p : ℝ) ν| = Real.rpow (p : ℝ) ν :=
        abs_of_pos hpos
      rw [habs]
      simpa using (Real.rpow_right_inj hp0 hp1 (y := ν) (z := 0))

end


end GaloisForLFunctions.HTGeometry
