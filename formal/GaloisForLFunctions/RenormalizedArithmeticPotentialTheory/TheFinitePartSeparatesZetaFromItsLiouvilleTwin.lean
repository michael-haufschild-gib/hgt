import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTwiceTheMertensLimit

/-!
# The finite part separates ζ from its Liouville twin

The Liouville twin has the opposite polar divergence, `P_N(λx) = −ℓ(x)² + O(mass)`
(`abs_liouvilleForm_stepProfile_add_le`). This file computes its finite part with the finite-part
law (`exists_abs_gaugeForm_stepProfile_finitePart_le`).

* **The even prime powers converge** (`tendsto_liouvilleEvenSum`, `liouvilleEvenLimit_pos`):
  `T(y) = Σ_{t ≤ y} (1 + λ(t))Λ(t)/t` counts the even prime powers twice; it increases to a limit
  `τ ≥ (log 2)/2 > 0` (mathematically `τ = 2 Σ_p log p/(p² − 1)`).
* **The Liouville Mertens limit** (`tendsto_liouvilleMertensError`): `A_λ(y) = −A(y) + T(y)`, so
  `A_λ(y) + log y → γ + τ`.
* **The Liouville finite part** (`exists_abs_liouvilleForm_stepProfile_finitePart_le`):
  `P_N(λx) = −ℓ(x)² + 2(γ + τ)|x|² + o(mass)` on uniform step profiles.
* **Separation** (`exists_abs_liouvilleForm_sub_zetaForm_sub_le`): on the polar hyperplane
  `ℓ(x) = 0`, `P_N(λx) − P_N(x) = 2(2γ + τ)|x|² + o(mass)`, with `2γ + τ > 0`.

The two forms have the same spectrum and opposite polar matching. On the survival cone of ζ the
twin's finite part is `+2(γ + τ)` against `−2γ` for ζ: the renormalized horizon separates the
pair with a definite sign, through Euler's constant and the even prime powers.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

/-- The **even prime-power sum** `T(y) = Σ_{t ≤ y} (1 + λ(t))Λ(t)/t`. -/
def liouvilleEvenSum (y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (1 + liouvilleSign t) * Λ t / t

theorem liouvilleEvenSum_term_nonneg (t : ℕ) : 0 ≤ (1 + liouvilleSign t) * Λ t / t := by
  refine div_nonneg (mul_nonneg ?_ vonMangoldt_nonneg) (Nat.cast_nonneg _)
  rcases neg_one_pow_eq_or ℝ (Ω t) with h | h <;> rw [liouvilleSign, h] <;> norm_num

theorem liouvilleEvenSum_mono : Monotone liouvilleEvenSum :=
  monotone_nat_of_le_succ fun y => by
    rw [liouvilleEvenSum, liouvilleEvenSum, sum_Icc_succ_top (by omega)]
    linarith [liouvilleEvenSum_term_nonneg (y + 1)]

/-- The **even prime-power limit** `τ = lim_y T(y)`. -/
def liouvilleEvenLimit : ℝ := ⨆ y, liouvilleEvenSum y

theorem tendsto_liouvilleEvenSum : Tendsto liouvilleEvenSum atTop (𝓝 liouvilleEvenLimit) :=
  tendsto_atTop_ciSup liouvilleEvenSum_mono
    ⟨tameConstant, by rintro _ ⟨y, rfl⟩; exact sum_one_add_liouville_le y⟩

/-- `τ ≥ (log 2)/2`: the prime power `4 = 2²` alone contributes `2 log 2/4`. -/
theorem liouvilleEvenLimit_pos : Real.log 2 / 2 ≤ liouvilleEvenLimit := by
  have hbdd : BddAbove (Set.range liouvilleEvenSum) :=
    ⟨tameConstant, by rintro _ ⟨y, rfl⟩; exact sum_one_add_liouville_le y⟩
  refine le_trans ?_ (le_ciSup hbdd 4)
  have h4 : (1 + liouvilleSign 4) * Λ 4 / (4 : ℕ) = Real.log 2 / 2 := by
    have hl : liouvilleSign 4 = 1 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, liouvilleSign_prime_pow Nat.prime_two]
      norm_num
    rw [hl, show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_prime_pow Nat.prime_two (by norm_num)]
    push_cast
    ring
  rw [← h4]
  exact single_le_sum (f := fun t => (1 + liouvilleSign t) * Λ t / t)
    (fun t _ => liouvilleEvenSum_term_nonneg t) (by simp)

/-- **The Liouville Mertens limit**: `A_λ(y) + log y → γ + τ`. -/
theorem tendsto_liouvilleMertensError :
    Tendsto (gaugeMertensError liouvilleSign (-1)) atTop (𝓝 (γ + liouvilleEvenLimit)) := by
  have h := (tendsto_mertensSum_sub_log.neg).add tendsto_liouvilleEvenSum
  rw [neg_neg] at h
  refine h.congr fun y => ?_
  -- `A_λ = −A + T`
  have hsplit : gaugeMertensSum liouvilleSign y = -mertensSum y + liouvilleEvenSum y := by
    rw [gaugeMertensSum, mertensSum, liouvilleEvenSum, ← sum_neg_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  rw [gaugeMertensError, hsplit]
  ring

/-- **The Liouville finite part**: for every `η > 0` there is `C` with
`|P_N(λx) + ℓ(x)² − 2(γ + τ)|x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)`. -/
theorem exists_abs_liouvilleForm_stepProfile_finitePart_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      |atomicWeilForm N (fun n => liouvilleSign n * stepProfile c M n) +
          polarFunctional N (stepProfile c M) ^ 2 -
          2 * (γ + liouvilleEvenLimit) * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  obtain ⟨C, hC⟩ := exists_abs_gaugeForm_stepProfile_finitePart_le liouville_matching.1
    (by norm_num : |(-1 : ℝ)| ≤ 1) tendsto_liouvilleMertensError hη
  refine ⟨C, fun c M hM1 hM => ?_⟩
  have h := hC c M hM1 hM
  rwa [neg_one_mul, sub_neg_eq_add] at h

/-- **The finite part separates ζ from its Liouville twin**: for every `η > 0` there is `C` such
that every polar-neutral uniform step profile has
`|P_N(λx) − P_N(x) − 2(2γ + τ)|x|²| ≤ 2 Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)`, and
`2γ + τ > 0`. -/
theorem exists_abs_liouvilleForm_sub_zetaForm_sub_le {η : ℝ} (hη : 0 < η) :
    0 < 2 * γ + liouvilleEvenLimit ∧
    ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) → (∀ i, M i ≤ N) →
      polarFunctional N (stepProfile c M) = 0 →
      |atomicWeilForm N (fun n => liouvilleSign n * stepProfile c M n) -
          atomicWeilForm N (stepProfile c M) -
          2 * (2 * γ + liouvilleEvenLimit) * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
        2 * ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  refine ⟨?_, ?_⟩
  · have hγ : 0 < γ := (by norm_num : (0 : ℝ) < 1 / 2).trans
      Real.one_half_lt_eulerMascheroniConstant
    have hτ := liouvilleEvenLimit_pos
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  obtain ⟨C₁, hC₁⟩ := exists_abs_liouvilleForm_stepProfile_finitePart_le hη
  obtain ⟨C₂, hC₂⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨max C₁ C₂, fun c M hM1 hM hpolar => ?_⟩
  have h1 := hC₁ c M hM1 hM
  have h2 := hC₂ c M hM1 hM
  rw [hpolar] at h1 h2
  -- both errors are dominated by the larger constant
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
