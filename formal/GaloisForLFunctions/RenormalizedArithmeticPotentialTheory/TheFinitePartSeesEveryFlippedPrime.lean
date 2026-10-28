import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTwiceTheMertensLimit

/-!
# The finite part sees every flipped prime

A twin of `ζ` that flips the primes of a finite set `F`, `ε_F(n) = Π_{p ∈ F} (−1)^{v_p(n)}`, has
matching coefficient `1` (`finiteFlip_matching`): its polar divergence is that of `ζ`, so the
coupled renormalization does not separate the pair. This file computes the separation in the
finite part.

* **The flip deficit** (`finiteFlipDeficit`, `tendsto_finiteFlipDeficit`):
  `D_F(y) = Σ_{t ≤ y} (1 − ε_F(t))Λ(t)/t` counts the odd prime powers of `F` twice. It increases to a
  limit `δ_F`, mathematically `δ_F = 2 Σ_{p ∈ F} p log p/(p² − 1)`.
* **Every flipped prime counts** (`two_mul_log_div_le_finiteFlipLimit`): `δ_F ≥ 2 log p/p` for each
  `p ∈ F`, from the term `t = p`.
* **The Mertens limit of the twin** (`tendsto_finiteFlipMertensError`): `A_{ε_F}(y) = A(y) − D_F(y)`,
  so `A_{ε_F}(y) − log y → −γ − δ_F`.
* **Separation** (`exists_abs_finiteFlipForm_sub_zetaForm_add_le`): on every uniform step profile,
  `P_N(ε_F x) − P_N(x) = −2δ_F |x|² + o(mass)`. The divergences `ℓ²` cancel, and the finite part of
  the twin is lower by `2δ_F > 0` for every non-empty `F`.

So among the twins of `ζ` that flip finitely many primes, `ζ` has the largest finite part, and
each flipped prime lowers it by at least `4 log p/p`. Matching cannot select `ζ` within this
family, but the finite part does, with an explicit margin at every prime.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {F : Finset ℕ}

theorem abs_finiteFlip (F : Finset ℕ) (t : ℕ) : |finiteFlip F t| = 1 := by
  rw [finiteFlip, abs_prod]
  exact prod_eq_one fun p _ => by rw [abs_pow, abs_neg, abs_one, one_pow]

/-- The **flip deficit** `D_F(y) = Σ_{t ≤ y} (1 − ε_F(t))Λ(t)/t`. -/
def finiteFlipDeficit (F : Finset ℕ) (y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (1 - finiteFlip F t) * Λ t / t

theorem finiteFlipDeficit_term_nonneg (F : Finset ℕ) (t : ℕ) :
    0 ≤ (1 - finiteFlip F t) * Λ t / t := by
  have h := le_abs_self (finiteFlip F t)
  rw [abs_finiteFlip] at h
  exact div_nonneg (mul_nonneg (by linarith) vonMangoldt_nonneg) (Nat.cast_nonneg t)

theorem finiteFlipDeficit_mono (F : Finset ℕ) : Monotone (finiteFlipDeficit F) :=
  monotone_nat_of_le_succ fun y => by
    rw [finiteFlipDeficit, finiteFlipDeficit, sum_Icc_succ_top (by omega)]
    linarith [finiteFlipDeficit_term_nonneg F (y + 1)]

/-- `A_{ε_F}(y) = A(y) − D_F(y)`. -/
theorem gaugeMertensSum_finiteFlip_eq (F : Finset ℕ) (y : ℕ) :
    gaugeMertensSum (finiteFlip F) y = mertensSum y - finiteFlipDeficit F y := by
  rw [gaugeMertensSum, mertensSum, finiteFlipDeficit, ← sum_sub_distrib]
  exact sum_congr rfl fun t _ => by ring

/-- The flip deficit is bounded, since both Mertens sums are `log y + O(1)`. -/
theorem finiteFlipDeficit_le (hF : ∀ p ∈ F, p.Prime) (y : ℕ) :
    finiteFlipDeficit F y ≤
      2 * (Real.log 4 + 4) + 2 * ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · have : 0 ≤ ∑ p ∈ F, Real.log p / ((p : ℝ) - 1) := sum_nonneg fun p hp => by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
      exact div_nonneg (Real.log_nonneg hp1.le) (by linarith)
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [finiteFlipDeficit, Icc_self, Finset.Icc_eq_empty_of_lt zero_lt_one, sum_empty]
    linarith
  have h1 := RHTower.Mertens.mertens_first y hy
  have h2 := (finiteFlip_matching hF).2 y hy
  rw [gaugeMertensSum_finiteFlip_eq, one_mul] at h2
  have hm : mertensSum y = ∑ t ∈ Icc 1 y, Λ t / t := rfl
  rw [← hm] at h1
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The **flip limit** `δ_F = lim_y D_F(y)`. -/
def finiteFlipLimit (F : Finset ℕ) : ℝ := ⨆ y, finiteFlipDeficit F y

theorem tendsto_finiteFlipDeficit (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (finiteFlipDeficit F) atTop (𝓝 (finiteFlipLimit F)) :=
  tendsto_atTop_ciSup (finiteFlipDeficit_mono F)
    ⟨_, by rintro _ ⟨y, rfl⟩; exact finiteFlipDeficit_le hF y⟩

/-- A flipped prime is flipped: `ε_F(p) = −1` for `p ∈ F`. -/
theorem finiteFlip_prime (hF : ∀ p ∈ F, p.Prime) {p : ℕ} (hp : p ∈ F) : finiteFlip F p = -1 := by
  rw [finiteFlip, prod_eq_single p]
  · rw [(hF p hp).factorization_self, pow_one]
  · intro p' hp' hne
    rw [(hF p hp).factorization, Finsupp.single_eq_of_ne hne, pow_zero]
  · intro h
    exact absurd hp h

/-- **Every flipped prime counts**: `δ_F ≥ 2 log p/p` for each `p ∈ F`. -/
theorem two_mul_log_div_le_finiteFlipLimit (hF : ∀ p ∈ F, p.Prime) {p : ℕ} (hp : p ∈ F) :
    2 * Real.log p / p ≤ finiteFlipLimit F := by
  have hbdd : BddAbove (Set.range (finiteFlipDeficit F)) :=
    ⟨_, by rintro _ ⟨y, rfl⟩; exact finiteFlipDeficit_le hF y⟩
  refine le_trans ?_ (le_ciSup hbdd p)
  have hterm : (1 - finiteFlip F p) * Λ p / p = 2 * Real.log p / p := by
    rw [finiteFlip_prime hF hp, vonMangoldt_apply_prime (hF p hp)]
    ring
  rw [← hterm]
  exact single_le_sum (f := fun t => (1 - finiteFlip F t) * Λ t / t)
    (fun t _ => finiteFlipDeficit_term_nonneg F t)
    (mem_Icc.mpr ⟨(hF p hp).one_le, le_rfl⟩)

/-- **The Mertens limit of the twin**: `A_{ε_F}(y) − log y → −γ − δ_F`. -/
theorem tendsto_finiteFlipMertensError (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (gaugeMertensError (finiteFlip F) 1) atTop (𝓝 (-γ - finiteFlipLimit F)) := by
  refine (tendsto_mertensSum_sub_log.sub (tendsto_finiteFlipDeficit hF)).congr fun y => ?_
  rw [gaugeMertensError, gaugeMertensSum_finiteFlip_eq]
  ring

/-- **The finite part sees every flipped prime**: for every `η > 0` there is `C` such that every
uniform step profile has `|P_N(ε_F x) − P_N(x) + 2δ_F|x|²| ≤ 2 Σ_{i,j} |c_i| |c_j| (η H_{min} + C)`,
with `δ_F ≥ 2 log p/p` for each `p ∈ F`. -/
theorem exists_abs_finiteFlipForm_sub_zetaForm_add_le (hF : ∀ p ∈ F, p.Prime) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => finiteFlip F n * stepProfile c M n) -
          atomicWeilForm N (stepProfile c M) +
          2 * finiteFlipLimit F * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        2 * ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_gaugeForm_stepProfile_finitePart_le (finiteFlip_isSignGauge F)
    (by norm_num : |(1 : ℝ)| ≤ 1) (tendsto_finiteFlipMertensError hF) hη
  obtain ⟨C₂, hC₂⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨max C₁ C₂, fun c M hM1 hM => ?_⟩
  have h1 := hC₁ c M hM1 hM
  have h2 := hC₂ c M hM1 hM
  have hmono : ∀ C' : ℝ, C' ≤ max C₁ C₂ →
      ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C') ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + max C₁ C₂) :=
    fun C' hC' => sum_le_sum fun i _ => sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1' := h1.trans (hmono C₁ (le_max_left _ _))
  have h2' := h2.trans (hmono C₂ (le_max_right _ _))
  rw [abs_le] at h1' h2' ⊢
  constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
