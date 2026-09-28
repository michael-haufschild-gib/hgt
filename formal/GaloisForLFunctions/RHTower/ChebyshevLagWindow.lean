import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-!
# Short windows of `ψ` from the genus-kernel explicit formula

Put `S(X) = Σ_{n ≤ X} Λ(n)/n` and, for `1 ≤ a ≤ b`, the discrete window statistic

`J(a, b) = S(b) - S(a) - ψ(b)/b + ψ(a)/a = Σ_{a < n ≤ b} Λ(n)(1/n - 1/b) + ψ(a)(1/a - 1/b)`.

Because `1/b ≤ 1/n ≤ 1/a` on the window, `J` is squeezed:

`ψ(a)(1/a - 1/b) ≤ J(a, b) ≤ ψ(b)(1/a - 1/b)`.

The genus-kernel explicit formula `lag_explicit_formula` evaluates `J` exactly:

`J(a, b) = log(b/a) + Re(Z(b)/b - Z(a)/a) + log(2π)(1/b - 1/a) - E(b)/b + E(a)/a`,

with `Z(X) = Σ_ρ X^ρ/(ρ(1-ρ))` over the zeros of `ξ` and the trivial-zero series
`0 ≤ E(X) ≤ 2/X²`.  Two adjacent window averages therefore bound `ψ(x+h) - ψ(x)` from below by
`h - 2h'` plus a difference of zero sums, with no integral and no truncation.
-/

namespace RHTower

noncomputable section

open Complex Finset ArithmeticFunction

/-- `S(X) = Σ_{n ≤ X} Λ(n)/n`. -/
def lagPsiSum (X : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, vonMangoldt n / (n : ℝ)

/-- The genus-kernel zero sum `Z(X) = Σ_ρ X^ρ/(ρ(1-ρ))`. -/
def lagZeroSum (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (X : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

/-- The window statistic `J(a, b)`. -/
def chebyshevLagWindow (a b : ℝ) : ℝ := lagPsiSum b - lagPsiSum a - Chebyshev.psi b / b + Chebyshev.psi a / a

theorem sum_Icc_floor_sub {f : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, f n - ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, f n
      = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : Finset.Icc 1 ⌊b⌋₊ = Finset.Icc 1 ⌊a⌋₊ ∪ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

theorem psi_sub_psi_eq_sum {a b : ℝ} (hab : a ≤ b) :
    Chebyshev.psi b - Chebyshev.psi a = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have h := sum_Icc_floor_sub (f := fun n => vonMangoldt n) hab
  have e1 : ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, vonMangoldt n = ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, vonMangoldt n := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
    simp
    rfl
  have e2 : ∑ n ∈ Finset.Icc 0 ⌊a⌋₊, vonMangoldt n = ∑ n ∈ Finset.Icc 1 ⌊a⌋₊, vonMangoldt n := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
    simp
    rfl
  rw [e1, e2]
  exact h

/-- **The squeeze.**  `ψ(a)(1/a - 1/b) ≤ J(a, b) ≤ ψ(b)(1/a - 1/b)` for `0 < a ≤ b`. -/
theorem chebyshevLagWindow_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Chebyshev.psi a * (1 / a - 1 / b) ≤ chebyshevLagWindow a b ∧
      chebyshevLagWindow a b ≤ Chebyshev.psi b * (1 / a - 1 / b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hS : lagPsiSum b - lagPsiSum a = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n / (n : ℝ) :=
    sum_Icc_floor_sub (f := fun n => vonMangoldt n / (n : ℝ)) hab
  have hP := psi_sub_psi_eq_sum hab
  have hrange : ∀ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, a < n ∧ (n : ℝ) ≤ b := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    refine ⟨?_, ?_⟩
    · have := Nat.lt_floor_add_one a
      have h1 : (⌊a⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      linarith
    · exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hb.le)
  have hlow : (Chebyshev.psi b - Chebyshev.psi a) / b ≤ lagPsiSum b - lagPsiSum a := by
    rw [hS, hP, Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, h2⟩ := hrange n hn
    have hn0 : (0 : ℝ) < n := lt_trans ha h1
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg hn0 h2
  have hup : lagPsiSum b - lagPsiSum a ≤ (Chebyshev.psi b - Chebyshev.psi a) / a := by
    rw [hS, hP, Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨h1, _⟩ := hrange n hn
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg ha h1.le
  unfold chebyshevLagWindow
  constructor
  · have : Chebyshev.psi a * (1 / a - 1 / b)
        = (Chebyshev.psi b - Chebyshev.psi a) / b - Chebyshev.psi b / b + Chebyshev.psi a / a := by
      field_simp
      ring
    linarith
  · have : Chebyshev.psi b * (1 / a - 1 / b)
        = (Chebyshev.psi b - Chebyshev.psi a) / a - Chebyshev.psi b / b + Chebyshev.psi a / a := by
      field_simp
      ring
    linarith

/-- The trivial-zero series is at most `2/X²` for `X ≥ 2`. -/
theorem trivialZeroSeriesReal_le_two_div_sq {X : ℝ} (hX : 2 ≤ X) :
    trivialZeroSeriesReal X ≤ 2 / X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hgeom : Summable (fun k : ℕ => (1 / X ^ 2) * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm : ∀ k : ℕ, (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))
      ≤ (1 / X ^ 2) * (1 / 4 : ℝ) ^ k := by
    intro k
    have hden : (1 : ℝ) ≤ 2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hpow : X ^ 2 * 4 ^ k ≤ X ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, pow_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by nlinarith) k)
        (by positivity)
    calc (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))
        ≤ (X ^ (2 * (k + 1)))⁻¹ := div_le_self (by positivity) hden
      _ ≤ (X ^ 2 * 4 ^ k)⁻¹ := inv_anti₀ (by positivity) hpow
      _ = (1 / X ^ 2) * (1 / 4 : ℝ) ^ k := by rw [mul_inv, one_div_pow]; ring
  unfold trivialZeroSeriesReal
  calc ∑' k : ℕ, (X ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))
      ≤ ∑' k : ℕ, (1 / X ^ 2) * (1 / 4 : ℝ) ^ k :=
        (summable_trivialZeroSeriesReal_term hX1).tsum_le_tsum hterm hgeom
    _ = (1 / X ^ 2) * (4 / 3) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
    _ ≤ 2 / X ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-- **The exact evaluation of the window statistic.** -/
theorem chebyshevLagWindow_eq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    chebyshevLagWindow a b = Real.log (b / a) + (lagZeroSum b / b - lagZeroSum a / a).re
      + Real.log (2 * Real.pi) * (1 / b - 1 / a)
      - trivialZeroSeriesReal b / b + trivialZeroSeriesReal a / a := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hla := lag_explicit_formula ha
  have hlb := lag_explicit_formula hb
  rw [trivialZeroSeries_eq_real] at hla hlb
  have hZa : lagZeroSum a = ((a - Chebyshev.psi a + a * (lagPsiSum a - Real.log a +
      Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) + trivialZeroSeriesReal a : ℝ) : ℂ) := by
    unfold lagZeroSum lagPsiSum
    rw [hla]
    push_cast
    ring
  have hZb : lagZeroSum b = ((b - Chebyshev.psi b + b * (lagPsiSum b - Real.log b +
      Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) + trivialZeroSeriesReal b : ℝ) : ℂ) := by
    unfold lagZeroSum lagPsiSum
    rw [hlb]
    push_cast
    ring
  rw [hZa, hZb, ← Complex.ofReal_div, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.ofReal_re, Real.log_div hb0.ne' ha0.ne']
  unfold chebyshevLagWindow
  field_simp
  ring

end

end RHTower
