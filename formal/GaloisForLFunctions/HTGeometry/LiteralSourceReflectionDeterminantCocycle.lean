import GaloisForLFunctions.HTGeometry.LiteralSourceDeterminantRankTower

/-!
# Literal-source reflection determinant cocycle

The canonical new-channel representative at each literal source rank jump has a marked prime-edge
execution.  Character inversion multiplies one such execution by an exact odd inverse power.
Across a finite block these multipliers accumulate with quadratic exponent `n * (2*M+n)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower

/-- Reflection multiplier of one marked source edge. -/
def complexCharacterEdgeReflectionMultiplier (z : ℂ) (m : ℕ) : ℂ :=
  -((z⁻¹) ^ (2 * m + 1))

/-- Inversion acts on one source-edge execution by the exact odd-power multiplier. -/
theorem complexCharacterEdge_inv_eq_reflectionMultiplier_mul
    {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    complexCharacterEdge z⁻¹ m =
      complexCharacterEdgeReflectionMultiplier z m * complexCharacterEdge z m := by
  have hcancel : (z⁻¹) ^ m * z ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  have hmul : (z⁻¹) ^ (2 * m + 1) * z ^ m = (z⁻¹) ^ (m + 1) := by
    rw [show 2 * m + 1 = (m + 1) + m by omega, pow_add, mul_assoc,
      hcancel, mul_one]
  calc
    complexCharacterEdge z⁻¹ m = (z⁻¹) ^ (m + 1) * (z - 1) := by
      rw [complexCharacterEdge, pow_succ]
      calc
        (z⁻¹) ^ m - (z⁻¹) ^ m * z⁻¹ =
            (z⁻¹) ^ m * (1 - z⁻¹) := by ring
        _ = (z⁻¹) ^ m * (z⁻¹ * (z - 1)) := by
          congr 1
          field_simp [hz]
        _ = (z⁻¹) ^ (m + 1) * (z - 1) := by rw [pow_succ, mul_assoc]
    _ = complexCharacterEdgeReflectionMultiplier z m * complexCharacterEdge z m := by
      rw [complexCharacterEdgeReflectionMultiplier, complexCharacterEdge,
        show z ^ (m + 1) = z ^ m * z by rw [pow_succ], ← hmul]
      ring

/-- Total exponent created by a reflected block of `n` edges beginning at `M`. -/
def complexCharacterReflectionExponent (M n : ℕ) : ℕ :=
  n * (2 * M + n)

theorem complexCharacterReflectionExponent_succ (M n : ℕ) :
    complexCharacterReflectionExponent M (n + 1) =
      complexCharacterReflectionExponent M n + (2 * (M + n) + 1) := by
  simp only [complexCharacterReflectionExponent]
  ring

/-- Accumulated reflection multiplier across a finite source-edge block. -/
def complexCharacterEdgeReflectionBlockMultiplier (z : ℂ) (M n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, complexCharacterEdgeReflectionMultiplier z (M + j)

/-- Accumulated reflection multiplier has exact quadratic exponent. -/
theorem complexCharacterEdgeReflectionBlockMultiplier_eq
    (z : ℂ) (M n : ℕ) :
    complexCharacterEdgeReflectionBlockMultiplier z M n =
      (-1 : ℂ) ^ n * (z⁻¹) ^ complexCharacterReflectionExponent M n := by
  induction n with
  | zero => simp [complexCharacterEdgeReflectionBlockMultiplier,
      complexCharacterReflectionExponent]
  | succ n ih =>
      rw [complexCharacterEdgeReflectionBlockMultiplier,
        Finset.prod_range_succ]
      change complexCharacterEdgeReflectionBlockMultiplier z M n *
          complexCharacterEdgeReflectionMultiplier z (M + n) = _
      rw [ih, complexCharacterEdgeReflectionMultiplier,
        complexCharacterReflectionExponent_succ, pow_add, pow_succ]
      ring

/-- Product of reflected source edges differs by exact quadratic block multiplier. -/
theorem prod_complexCharacterEdge_inv_eq_reflectionBlockMultiplier_mul
    {z : ℂ} (hz : z ≠ 0) (M n : ℕ) :
    (∏ j ∈ Finset.range n, complexCharacterEdge z⁻¹ (M + j)) =
      complexCharacterEdgeReflectionBlockMultiplier z M n *
        ∏ j ∈ Finset.range n, complexCharacterEdge z (M + j) := by
  simp_rw [complexCharacterEdge_inv_eq_reflectionMultiplier_mul hz]
  rw [Finset.prod_mul_distrib]
  rfl

/-- Marked two-coefficient execution of one actual normalized depth-12 source channel. -/
def rankTwelveLiteralSourceMarkedExecution
    (p : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
        (p ^ (12 + j)) * z ^ (12 + j) +
    (completeResolutionNormalizedFiniteAbscissaSource 12 (j + 1)).1
        (p ^ (12 + j + 1)) * z ^ (12 + j + 1)

/-- Marked literal execution is the coherent character edge. -/
theorem rankTwelveLiteralSourceMarkedExecution_eq
    {p : ℕ} (hp : p.Prime) (z : ℂ) (j : ℕ) :
    rankTwelveLiteralSourceMarkedExecution p z j =
      complexCharacterEdge z (12 + j) := by
  exact rankTwelveSource_character_execution hp z j

/-- Actual rank-growing source executions obey quadratic reflected block law. -/
theorem prod_rankTwelveLiteralSourceMarkedExecution_inv_eq
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ≠ 0) (M n : ℕ) :
    (∏ j ∈ Finset.range n,
        rankTwelveLiteralSourceMarkedExecution p z⁻¹ (M + j)) =
      complexCharacterEdgeReflectionBlockMultiplier z (12 + M) n *
        ∏ j ∈ Finset.range n,
          rankTwelveLiteralSourceMarkedExecution p z (M + j) := by
  simp_rw [rankTwelveLiteralSourceMarkedExecution_eq hp]
  simpa only [Nat.add_assoc] using
    prod_complexCharacterEdge_inv_eq_reflectionBlockMultiplier_mul hz (12 + M) n

/-- Norm of accumulated multiplier is exact inverse radial power. -/
theorem norm_complexCharacterEdgeReflectionBlockMultiplier
    (z : ℂ) (M n : ℕ) :
    ‖complexCharacterEdgeReflectionBlockMultiplier z M n‖ =
      ‖z‖⁻¹ ^ complexCharacterReflectionExponent M n := by
  rw [complexCharacterEdgeReflectionBlockMultiplier_eq]
  simp [norm_pow, norm_inv]

/-- Every nonempty reflected block has unit multiplier exactly on unitary characters. -/
theorem norm_complexCharacterEdgeReflectionBlockMultiplier_eq_one_iff
    {z : ℂ} (M : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖complexCharacterEdgeReflectionBlockMultiplier z M n‖ = 1 ↔ ‖z‖ = 1 := by
  rw [norm_complexCharacterEdgeReflectionBlockMultiplier]
  have hExp : complexCharacterReflectionExponent M n ≠ 0 := by
    apply Nat.mul_ne_zero hn.ne'
    omega
  rw [pow_eq_one_iff_of_nonneg (inv_nonneg.mpr (norm_nonneg z)) hExp]
  simp [inv_eq_one]

/-- Prime-radial nonempty block is unitary exactly at zero real drift. -/
theorem primeRadial_norm_reflectionBlockMultiplier_eq_one_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} (M : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖complexCharacterEdgeReflectionBlockMultiplier
        ((Real.rpow (p : ℝ) ν : ℝ) : ℂ) M n‖ = 1 ↔ ν = 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  calc
    ‖complexCharacterEdgeReflectionBlockMultiplier
        ((Real.rpow (p : ℝ) ν : ℝ) : ℂ) M n‖ = 1 ↔
        ‖((Real.rpow (p : ℝ) ν : ℝ) : ℂ)‖ = 1 :=
      norm_complexCharacterEdgeReflectionBlockMultiplier_eq_one_iff M hn
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
