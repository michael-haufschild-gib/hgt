import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationConvolution

/-!
# Valuation twists of the convolution exponential

The twist is multiplicative on nonzero divisor pairs. The coefficient
sequence being twisted need not be multiplicative.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic
open GaloisForLFunctions.HTGeometry

def valuationTwist (p : ℕ) (z : ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  z ^ (n.factorization p) * f n

theorem valuationTwist_convolution (p : ℕ) (z : ℂ) (f g : ℕ → ℂ) :
    valuationTwist p z (LSeries.convolution f g) =
      LSeries.convolution (valuationTwist p z f) (valuationTwist p z g) := by
  funext n
  simp only [valuationTwist, LSeries.convolution_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  obtain ⟨hn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
  have hab0 : ab.1 * ab.2 ≠ 0 := by rwa [hn]
  have ha : ab.1 ≠ 0 := fun h => hab0 (by rw [h, zero_mul])
  have hb : ab.2 ≠ 0 := fun h => hab0 (by rw [h, mul_zero])
  rw [← hn, Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]
  ring

theorem valuationTwist_dirichletConvPow (p : ℕ) (z : ℂ) (f : ℕ → ℂ) (k : ℕ) :
    valuationTwist p z (dirichletConvPow f k) =
      dirichletConvPow (valuationTwist p z f) k := by
  induction k with
  | zero =>
    funext n
    by_cases hn : n = 1
    · subst n
      simp [valuationTwist, dirichletConvPow]
    · simp [valuationTwist, dirichletConvPow, hn]
  | succ k ih =>
    rw [dirichletConvPow_succ, valuationTwist_convolution, ih, dirichletConvPow_succ]

theorem valuationTwist_dirichletExp (p : ℕ) (z : ℂ) (f : ℕ → ℂ) :
    valuationTwist p z (dirichletExp f) = dirichletExp (valuationTwist p z f) := by
  funext n
  have h (k : ℕ) := congrFun (valuationTwist_dirichletConvPow p z f k) n
  change z ^ (n.factorization p) *
    (∑ k ∈ Finset.range (n + 1), dirichletConvPow f k n / (k.factorial : ℂ)) = _
  rw [Finset.mul_sum]
  unfold dirichletExp
  apply Finset.sum_congr rfl
  intro k _
  rw [← h k]
  dsimp only [valuationTwist]
  ring

/-- Exact regrouping by valuation, including the zero-index convention. -/
theorem valuationTwist_eq_tsum {p : ℕ} (hp : p.Prime) (z : ℂ)
    {f : ℕ → ℂ} (h0 : f 0 = 0) (n : ℕ) :
    valuationTwist p z f n = ∑' k : ℕ, z ^ k * valuationPart p k f n := by
  by_cases hn : n = 0
  · subst n
    simp [valuationTwist, h0, valuationPart_zero]
  · rw [tsum_eq_single (n.factorization p)]
    · simp [valuationTwist, valuationPart, valuationMask_eq_factorization hp hn]
    · intro k hk
      simp [valuationPart, valuationMask_eq_factorization hp hn, Ne.symm hk]

/-- Absolute convergence of the twisted logarithm produces the actual
twisted exponential identity. Source summability is paid separately. -/
theorem LSeries_valuationTwist_dirichletExp (p : ℕ) (z : ℂ) {f : ℕ → ℂ}
    (h0 : f 0 = 0) (h1 : f 1 = 0) {s : ℂ}
    (hf : LSeriesSummable (valuationTwist p z f) s) :
    LSeriesSummable (valuationTwist p z (dirichletExp f)) s ∧
      LSeries (valuationTwist p z (dirichletExp f)) s =
        Complex.exp (LSeries (valuationTwist p z f) s) := by
  rw [valuationTwist_dirichletExp]
  exact LSeries_dirichletExp (by simp [valuationTwist, h0])
    (by simp [valuationTwist, h1]) hf

end RHTower.WeilSingularArithmetic
