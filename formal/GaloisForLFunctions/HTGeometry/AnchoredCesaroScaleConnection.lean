import GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence

/-!
# Anchored Cesàro scale connections

An anchored Cesàro formation potential has an exact logarithmic-scale current: terminal value
minus formed history.  The current is the scaled successor increment of the potential, its
harmonic holonomy reconstructs every later potential, and its kernel consists exactly of constant
tail gauges.  A bounded potential therefore cannot support an eventual one-sided current separated
from zero.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Anchored formation potential.  The weight three matches the literal Suzuki checkpoint
endpoint multiplicity. -/
def anchoredCesaroPotential (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (3 * a 2 + ∑ j ∈ Finset.Ico 3 (N + 1), a j) / (N + 1 : ℕ)

/-- Terminal formation value minus its anchored history. -/
def anchoredCesaroHighPass (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  a (N + 1) - anchoredCesaroPotential a N

/-- The high-pass is exactly the logarithmic-scale successor current of the formation
potential. -/
theorem anchoredCesaroPotential_succ_sub
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential a (N + 1) - anchoredCesaroPotential a N =
      anchoredCesaroHighPass a N / (N + 2 : ℕ) := by
  simp only [anchoredCesaroHighPass, anchoredCesaroPotential]
  rw [show N + 1 + 1 = (N + 1) + 1 by omega,
    Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 1)]
  have hN1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hN2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hN1, hN2]
  push_cast
  ring

/-- The base potential is the anchored value. -/
theorem anchoredCesaroPotential_two (a : ℕ → ℝ) :
    anchoredCesaroPotential a 2 = a 2 := by
  unfold anchoredCesaroPotential
  norm_num

/-- Adding a constant tail gauge translates the potential by that constant. -/
theorem anchoredCesaroPotential_add_const
    (a : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential (fun k => a k + c) N =
      anchoredCesaroPotential a N + c := by
  simp only [anchoredCesaroPotential, Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico,
    Nat.cast_sub (by omega : 3 ≤ N + 1)]
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  push_cast
  ring

/-- The connection current is invariant under constant tail gauge. -/
theorem anchoredCesaroHighPass_add_const
    (a : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass (fun k => a k + c) N =
      anchoredCesaroHighPass a N := by
  rw [anchoredCesaroHighPass, anchoredCesaroHighPass,
    anchoredCesaroPotential_add_const a c hN]
  ring

/-- Potential plus connection current reconstructs the next terminal value. -/
theorem anchoredCesaro_terminal_reconstruction (a : ℕ → ℝ) (N : ℕ) :
    a (N + 1) =
      anchoredCesaroPotential a N + anchoredCesaroHighPass a N := by
  rw [anchoredCesaroHighPass]
  ring

/-- Harmonic holonomy reconstructs the formation potential from its base and currents. -/
theorem anchoredCesaroPotential_reconstruction
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential a N =
      a 2 + ∑ k ∈ Finset.Ico 2 N,
        anchoredCesaroHighPass a k / (k + 2 : ℕ) := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [anchoredCesaroPotential_two]
      norm_num
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ N)]
      calc
        anchoredCesaroPotential a (N + 1) =
            anchoredCesaroPotential a N +
              anchoredCesaroHighPass a N / (N + 2 : ℕ) := by
          linarith [anchoredCesaroPotential_succ_sub a hN]
        _ = a 2 +
            (∑ k ∈ Finset.Ico 2 N,
              anchoredCesaroHighPass a k / (k + 2 : ℕ) +
                anchoredCesaroHighPass a N / (N + 2 : ℕ)) := by
          rw [ih]
          ring

/-- The high-pass is the scale-weighted potential increment. -/
theorem anchoredCesaroHighPass_eq_scaled_potentialIncrement
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass a N =
      (N + 2 : ℕ) *
        (anchoredCesaroPotential a (N + 1) - anchoredCesaroPotential a N) := by
  rw [anchoredCesaroPotential_succ_sub a hN]
  have hN2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hN2]

/-- Exact finite-window connection holonomy. -/
theorem anchoredCesaroPotential_windowHolonomy
    (a : ℕ → ℝ) {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N) :
    anchoredCesaroPotential a N - anchoredCesaroPotential a K =
      ∑ k ∈ Finset.Ico K N,
        anchoredCesaroHighPass a k / (k + 2 : ℕ) := by
  induction N, hKN using Nat.le_induction with
  | base => simp
  | succ N hKN ih =>
      rw [Finset.sum_Ico_succ_top hKN]
      have hN : 2 ≤ N := hK.trans hKN
      linarith [anchoredCesaroPotential_succ_sub a hN]

/-- A one-sided current spends harmonic potential budget exactly. -/
theorem anchoredCesaroHarmonicBudget
    (a : ℕ → ℝ) {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N)
    {c B : ℝ}
    (hhigh : ∀ k ∈ Finset.Ico K N, c ≤ anchoredCesaroHighPass a k)
    (hpotK : -B ≤ anchoredCesaroPotential a K)
    (hpotN : anchoredCesaroPotential a N ≤ B) :
    c * ∑ k ∈ Finset.Ico K N, (1 / ((k + 2 : ℕ) : ℝ)) ≤ 2 * B := by
  have hterm : ∀ k ∈ Finset.Ico K N,
      c * (1 / ((k + 2 : ℕ) : ℝ)) ≤
        anchoredCesaroHighPass a k / (k + 2 : ℕ) := by
    intro k hk
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (hhigh k hk)
        (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ)))
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← anchoredCesaroPotential_windowHolonomy a hK hKN] at hsum
  linarith

/-- Every fixed shifted harmonic window has infinite scale length. -/
theorem tendsto_anchoredCesaroHarmonicWindow_atTop (K : ℕ) :
    Tendsto
      (fun N => ∑ k ∈ Finset.Ico K N, (1 / ((k + 2 : ℕ) : ℝ)))
      atTop atTop := by
  have hfull : Tendsto
      (fun N => ∑ k ∈ Finset.range N, ((((k + 2 : ℕ) : ℝ))⁻¹))
      atTop atTop := by
    apply tendsto_sum_inv_atTop_of_le_linear
        (γ := fun k => ((k + 2 : ℕ) : ℝ)) (c := 2)
    · norm_num
    · intro k
      positivity
    · filter_upwards [] with k
      push_cast
      have hk : (0 : ℝ) ≤ k := by positivity
      linarith
  have hshift := tendsto_atTop_add_const_right atTop
    (-(∑ k ∈ Finset.range K, ((((k + 2 : ℕ) : ℝ))⁻¹))) hfull
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop K] with N hKN
  rw [← Finset.sum_range_add_sum_Ico (fun k => ((((k + 2 : ℕ) : ℝ))⁻¹)) hKN]
  simp only [one_div]
  ring

/-- A bounded formation potential cannot support an eventual positive current separated from
zero. -/
theorem not_eventually_anchoredCesaroHighPass_ge_of_potential_bounded
    (a : ℕ → ℝ) {B c : ℝ} (hc : 0 < c)
    (hpot : ∀ N, |anchoredCesaroPotential a N| ≤ B) :
    ¬ ∀ᶠ N in atTop, c ≤ anchoredCesaroHighPass a N := by
  intro hevent
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hevent
  let K := max 2 K₀
  have hKtwo : 2 ≤ K := le_max_left _ _
  have hKK₀ : K₀ ≤ K := le_max_right _ _
  have hlarge : ∀ᶠ N in atTop,
      2 * B / c < ∑ k ∈ Finset.Ico K N, (1 / ((k + 2 : ℕ) : ℝ)) :=
    (tendsto_anchoredCesaroHarmonicWindow_atTop K).eventually
      (eventually_gt_atTop (2 * B / c))
  obtain ⟨N, hlargeN, hKN⟩ :=
    (hlarge.and (eventually_ge_atTop K)).exists
  have hhigh : ∀ k ∈ Finset.Ico K N, c ≤ anchoredCesaroHighPass a k := by
    intro k hk
    exact hK₀ k (hKK₀.trans (Finset.mem_Ico.mp hk).1)
  have hbudget := anchoredCesaroHarmonicBudget a hKtwo hKN hhigh
    (abs_le.mp (hpot K)).1 (abs_le.mp (hpot N)).2
  have hstrict : 2 * B <
      c * ∑ k ∈ Finset.Ico K N, (1 / ((k + 2 : ℕ) : ℝ)) := by
    have := (div_lt_iff₀ hc).mp hlargeN
    nlinarith
  linarith

/-- Negation commutes with formation potential. -/
theorem anchoredCesaroPotential_neg (a : ℕ → ℝ) (N : ℕ) :
    anchoredCesaroPotential (fun k => -a k) N = -anchoredCesaroPotential a N := by
  unfold anchoredCesaroPotential
  rw [Finset.sum_neg_distrib]
  ring

/-- Negation commutes with connection current. -/
theorem anchoredCesaroHighPass_neg (a : ℕ → ℝ) (N : ℕ) :
    anchoredCesaroHighPass (fun k => -a k) N = -anchoredCesaroHighPass a N := by
  rw [anchoredCesaroHighPass, anchoredCesaroHighPass,
    anchoredCesaroPotential_neg]
  ring

/-- A bounded formation potential cannot support an eventual negative current separated from
zero. -/
theorem not_eventually_anchoredCesaroHighPass_le_neg_of_potential_bounded
    (a : ℕ → ℝ) {B c : ℝ} (hc : 0 < c)
    (hpot : ∀ N, |anchoredCesaroPotential a N| ≤ B) :
    ¬ ∀ᶠ N in atTop, anchoredCesaroHighPass a N ≤ -c := by
  intro hevent
  apply not_eventually_anchoredCesaroHighPass_ge_of_potential_bounded
      (fun k => -a k) hc
  · intro N
    rw [anchoredCesaroPotential_neg, abs_neg]
    exact hpot N
  · filter_upwards [hevent] with N hN
    rw [anchoredCesaroHighPass_neg]
    linarith

/-- Complete gauge-kernel classification: connection currents agree exactly when the two tails
differ by one constant. -/
theorem anchoredCesaroHighPass_eq_iff_tail_constantGauge
    (a b : ℕ → ℝ) :
    (∀ N, 2 ≤ N → anchoredCesaroHighPass a N = anchoredCesaroHighPass b N) ↔
      ∀ n, 2 ≤ n → a n - b n = a 2 - b 2 := by
  constructor
  · intro h n hn
    by_cases hn2 : n = 2
    · simp [hn2]
    have hn3 : 3 ≤ n := by omega
    let N := n - 1
    have hN : 2 ≤ N := by omega
    have hsum :
        (∑ k ∈ Finset.Ico 2 N,
          anchoredCesaroHighPass a k / (k + 2 : ℕ)) =
        ∑ k ∈ Finset.Ico 2 N,
          anchoredCesaroHighPass b k / (k + 2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [h k (Finset.mem_Ico.mp hk).1]
    have hpa := anchoredCesaroPotential_reconstruction a hN
    have hpb := anchoredCesaroPotential_reconstruction b hN
    have hha := anchoredCesaro_terminal_reconstruction a N
    have hhb := anchoredCesaro_terminal_reconstruction b N
    have hhab := h N hN
    dsimp only [N] at hpa hpb hha hhb hhab
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hha hhb
    linarith
  · intro h N hN
    let c := a 2 - b 2
    have htail (n : ℕ) (hn : 2 ≤ n) : a n = b n + c := by
      dsimp only [c]
      linarith [h n hn]
    have hpotential :
        anchoredCesaroPotential a N =
          anchoredCesaroPotential (fun k => b k + c) N := by
      unfold anchoredCesaroPotential
      congr 2
      · rw [htail 2 (by omega)]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk3 := (Finset.mem_Ico.mp hk).1
        rw [htail k (by omega)]
    rw [anchoredCesaroHighPass, htail (N + 1) (by omega), hpotential,
      anchoredCesaroPotential_add_const b c hN]
    unfold anchoredCesaroHighPass
    ring

end

end GaloisForLFunctions.HTGeometry
