import GaloisForLFunctions.RHTower.ZetaHalfPlaneDiscJensen

/-!
# Exact trivial-zero products in the left-half-plane Jensen chart

The two telescoping cases of arXiv:2610.10584, Proposition 3.1 and
Remark 5.2, applied to the corpus's entire zeta function. Index `n = 0`
corresponds to the trivial zero `-2`. The finite products retain every
trivial zero and require no assumption about the nontrivial zeros.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- Left-half-plane chart with scale `a`. -/
def jensenLeftChart (a : ℝ) (z : ℂ) : ℂ :=
  1 / 2 - a * (1 + z) / (1 - z)

/-- The entire zeta function pulled back through the left chart. -/
def jensenLeftZeta (a : ℝ) (z : ℂ) : ℂ := zetaEntire (jensenLeftChart a z)

/-- Images of the trivial zeros at scale one. -/
def jensenTrivialRadius (n : ℕ) : ℝ := (4 * n + 3) / (4 * n + 7)

/-- Images of the same zeros at scale two. -/
def jensenTrivialRadiusTwo (n : ℕ) : ℝ := (4 * n + 1) / (4 * n + 9)

theorem jensenTrivialRadius_pos (n : ℕ) : 0 < jensenTrivialRadius n := by
  unfold jensenTrivialRadius
  positivity

theorem jensenTrivialRadius_lt_one (n : ℕ) : jensenTrivialRadius n < 1 := by
  unfold jensenTrivialRadius
  rw [div_lt_one (by positivity)]
  linarith

theorem jensenTrivialRadiusTwo_pos (n : ℕ) : 0 < jensenTrivialRadiusTwo n := by
  unfold jensenTrivialRadiusTwo
  positivity

theorem jensenTrivialRadiusTwo_lt_one (n : ℕ) : jensenTrivialRadiusTwo n < 1 := by
  unfold jensenTrivialRadiusTwo
  rw [div_lt_one (by positivity)]
  linarith

theorem jensenLeftChart_trivial (n : ℕ) :
    jensenLeftChart 1 (jensenTrivialRadius n) = -2 * ((n : ℂ) + 1) := by
  have h : (4 * (n : ℂ) + 7) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [jensenLeftChart, jensenTrivialRadius, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_one, one_mul]
  field_simp
  ring

theorem jensenLeftChartTwo_trivial (n : ℕ) :
    jensenLeftChart 2 (jensenTrivialRadiusTwo n) = -2 * ((n : ℂ) + 1) := by
  have h : (4 * (n : ℂ) + 9) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [jensenLeftChart, jensenTrivialRadiusTwo, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  field_simp
  ring

/-- Every listed point is a genuine zero of the pulled-back entire zeta function. -/
theorem jensenLeftZeta_trivial (n : ℕ) : jensenLeftZeta 1 (jensenTrivialRadius n) = 0 := by
  rw [jensenLeftZeta, jensenLeftChart_trivial, zetaEntire_eq]
  · rw [riemannZeta_neg_two_mul_nat_add_one, mul_zero]
  · intro h
    have := congrArg Complex.re h
    simp at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem jensenLeftZetaTwo_trivial (n : ℕ) :
    jensenLeftZeta 2 (jensenTrivialRadiusTwo n) = 0 := by
  rw [jensenLeftZeta, jensenLeftChartTwo_trivial, zetaEntire_eq]
  · rw [riemannZeta_neg_two_mul_nat_add_one, mul_zero]
  · intro h
    have := congrArg Complex.re h
    simp at this
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Exact product of reciprocal trivial-zero radii at scale one. -/
theorem prod_jensenTrivialRadius_inv (N : ℕ) :
    (∏ n ∈ Finset.range N, (jensenTrivialRadius n)⁻¹) = (4 * N + 3) / 3 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, jensenTrivialRadius, inv_div]
    push_cast
    have h : (4 * (N : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring

/-- Scale two telescopes across two adjacent factors. -/
theorem prod_jensenTrivialRadiusTwo_inv (N : ℕ) :
    (∏ n ∈ Finset.range N, (jensenTrivialRadiusTwo n)⁻¹) =
      (4 * N + 1) * (4 * N + 5) / 5 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, jensenTrivialRadiusTwo, inv_div]
    push_cast
    have h : (4 * (N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- The finite Jensen product for the first `N` trivial zeros. -/
theorem prod_div_jensenTrivialRadius (N : ℕ) (r : ℝ) :
    (∏ n ∈ Finset.range N, r / jensenTrivialRadius n) =
      r ^ N * ((4 * N + 3) / 3) := by
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, prod_jensenTrivialRadius_inv]

theorem prod_div_jensenTrivialRadiusTwo (N : ℕ) (r : ℝ) :
    (∏ n ∈ Finset.range N, r / jensenTrivialRadiusTwo n) =
      r ^ N * ((4 * N + 1) * (4 * N + 5) / 5) := by
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, prod_jensenTrivialRadiusTwo_inv]

end RHTower
