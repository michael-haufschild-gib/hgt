import GaloisForLFunctions.RHTower.DirichletLUniformPartialFraction
import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform
import GaloisForLFunctions.RHTower.VisibleCoprimeDirichletZeroJet

/-!
# A zero-free region for Dirichlet `L`-functions, uniform in the modulus

**Theorem** (`uniform_zero_free_region`). There is an absolute `c > 0` such that for every modulus
`q`, every nonprincipal character `χ` modulo `q` and every zero `β + iγ` of `L(s, χ)`,
`β ≤ 1 − c / log²(q(|γ| + 3))`, unless `χ` is real and the zero is real.

The proof is the classical one, with conductor-uniform inputs. Put `L = log(q(|γ| + 3)) ≥ 1`.

* *Complex characters.* At `σ = 1 + ε/L` the `3-4-1` inequality (`three_four_one_logDeriv`) with the
  pole bound `Re(−L₀'/L₀)(σ) ≤ 1/(σ − 1)` and the partial fraction (`neg_re_logDeriv_LFunction_le`) at
  heights `γ` (keeping the zero) and `2γ` (keeping nothing) gives `1 − β ≥ 1/(84 A L)`.
* *Real characters, `|γ| ≥ ε/L²`.* Now `χ² = 1` and `L(s, χ²)` is the principal `L`-function, with a pole:
  `Re(−L₀'/L₀)(σ + 2iγ) ≤ Re 1/(σ − 1 + 2iγ) + O(L²)` (`neg_re_logDeriv_zeta_le_pole`), and the pole term
  is at most `(σ − 1)/(4γ²)`.
* *Real characters, `0 < |γ| < ε/L²`.* The conjugate `β − iγ` is a zero as well
  (`RHTower.LFunction_inv_conj`), and `Re(1 + χ(n)) ≥ 0` (`two_term_logDeriv`) at real `σ` with both zeros
  kept excludes the pair.

The real zeros of real characters are Siegel's (`RHTower.siegel_zero_free`).
-/

noncomputable section

open Complex Metric

namespace RHTower

/-- `1 < log 3`. -/
theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_d9.trans (by norm_num)

/-- **`ζ` near `Re s = 1`, with its pole.** -/
theorem exists_neg_re_logDeriv_zeta_le_pole : ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 9/8 →
    (-deriv riemannZeta s / riemannZeta s).re ≤ ((s - 1)⁻¹).re + D * Real.log (|s.im| + 3) ^ 2 := by
  obtain ⟨C, L₀, hC, hL₀, hbound⟩ := Sieve.exists_bound_zetaLogDerivReg_uniform
  refine ⟨2 * C * (L₀ ^ 2 + 1), by positivity, fun s hs1 hs2 => ?_⟩
  have hs1' : s ≠ 1 := by intro h; rw [h, one_re] at hs1; exact lt_irrefl _ hs1
  have hG : zetaResidueUnit s ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hs1']
    exact mul_ne_zero (sub_ne_zero.mpr hs1') (riemannZeta_ne_zero_of_one_lt_re hs1)
  have heq := Sieve.neg_logDeriv_riemannZeta_eq hs1' hG
  set K : ℝ := |s.im| + Real.exp L₀ with hKdef
  have hexpL : 1 ≤ Real.exp L₀ := Real.one_le_exp (by linarith)
  have hK : L₀ ≤ Real.log K := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [abs_nonneg s.im]
  have hKim : |s.im| ≤ K := by linarith
  have hlogK0 : 0 < Real.log K := by linarith
  have hlow : 1 - 1 / 40000 / Real.log K ≤ s.re := by
    have : 0 < 1 / 40000 / Real.log K := by positivity
    linarith
  have hreg := hbound s K hK hKim hlow hs2
  have hlogK : Real.log K ≤ L₀ + Real.log (|s.im| + 3) := by
    have hKle : K ≤ Real.exp L₀ * (|s.im| + 3) := by nlinarith [abs_nonneg s.im]
    calc Real.log K ≤ Real.log (Real.exp L₀ * (|s.im| + 3)) :=
          Real.log_le_log (by positivity) hKle
      _ = L₀ + Real.log (|s.im| + 3) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hl1 : 1 ≤ Real.log (|s.im| + 3) :=
    one_lt_log_three.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im]))
  have hsplit : -deriv riemannZeta s / riemannZeta s = (s - 1)⁻¹ + Sieve.zetaLogDerivReg s := by
    rw [← heq, logDeriv_apply, neg_div]
  rw [hsplit, add_re]
  have hre : (Sieve.zetaLogDerivReg s).re ≤ C * Real.log K ^ 2 := (re_le_norm _).trans hreg
  have hsq : Real.log K ^ 2 ≤ (L₀ ^ 2 + 1) * 2 * Real.log (|s.im| + 3) ^ 2 := by
    have h1 : Real.log K ^ 2 ≤ (L₀ + Real.log (|s.im| + 3)) ^ 2 :=
      pow_le_pow_left₀ hlogK0.le hlogK 2
    have hl2 : 1 ≤ Real.log (|s.im| + 3) ^ 2 := by nlinarith
    have h2 : (L₀ + Real.log (|s.im| + 3)) ^ 2 ≤ 2 * L₀ ^ 2 + 2 * Real.log (|s.im| + 3) ^ 2 := by
      nlinarith [sq_nonneg (L₀ - Real.log (|s.im| + 3))]
    have h3 : L₀ ^ 2 ≤ L₀ ^ 2 * Real.log (|s.im| + 3) ^ 2 := le_mul_of_one_le_right (sq_nonneg _) hl2
    linarith
  nlinarith

variable {q : ℕ} [NeZero q]

/-- `Re(1 + χ(n)) ≥ 0`: the two-term inequality at real points. -/
theorem two_term_logDeriv (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (-logDeriv (1 : DirichletCharacter ℂ q).LFunction σ).re + (-logDeriv χ.LFunction σ).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [neg_logDeriv_LFunction_eq_LSeries _ hs, neg_logDeriv_LFunction_eq_LSeries _ hs]
  have h0 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ q) hs).LSeriesHasSum
  have h1 := hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  refine (h0.add h1).nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  show 0 ≤ (LSeries.term (fun n => (1 : DirichletCharacter ℂ q) n *
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ n).re +
    (LSeries.term (fun n => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ n).re
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
  have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  set a : ℝ := ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ with hadef
  have ha : 0 ≤ a :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hform : ∀ c : ℂ, c * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ (σ : ℂ) =
      (a : ℂ) * c := by
    intro c
    have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) σ
    rw [hnσ, hadef, Complex.ofReal_div]
    field_simp
  rw [hform, hform, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hχ : -1 ≤ (χ n).re := by
    have h := Complex.abs_re_le_norm (χ n)
    linarith [neg_abs_le (χ n).re, χ.norm_le_one (n : ZMod q)]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu, one_re]
    nlinarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, zero_re]
    simp

/-- A zero `β + iγ` with `β > 1/2` lies in the partial-fraction disc about `2 + iγ`. -/
theorem mem_pfBall_self {β γ : ℝ} (hβ : 1/2 < β) (hβ1 : β < 1) :
    ((β : ℂ) + γ * I) ∈ closedBall (2 + (γ : ℂ) * I) (22/25 * (91/50)) := by
  rw [mem_closedBall, Complex.dist_eq]
  have : (β : ℂ) + γ * I - (2 + γ * I) = ((β - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- The kept zero contributes `1/(σ − β)` at height `γ`. -/
theorem re_inv_sub_zero_self (σ β γ : ℝ) :
    (((σ : ℂ) + γ * I - ((β : ℂ) + γ * I))⁻¹).re = 1 / (σ - β) := by
  have : (σ : ℂ) + γ * I - ((β : ℂ) + γ * I) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- `log(q(2|γ| + 3)) ≤ 2 log(q(|γ| + 3))`. -/
theorem log_conductor_double_le (γ : ℝ) :
    Real.log ((q : ℝ) * (|2 * γ| + 3)) ≤ 2 * Real.log ((q : ℝ) * (|γ| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  rw [← Real.log_rpow (by positivity), abs_mul, abs_two]
  refine Real.log_le_log (by positivity) ?_
  rw [show ((q : ℝ) * (|γ| + 3)) ^ (2 : ℝ) = ((q : ℝ) * (|γ| + 3)) ^ (2 : ℕ) by norm_cast]
  nlinarith [abs_nonneg γ, sq_nonneg (|γ| + 3)]

end RHTower
