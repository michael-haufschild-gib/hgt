import GaloisForLFunctions.RHTower.WeilTailPanelSharpPrefix
import GaloisForLFunctions.RHTower.WeilFullConeSummableDeficitRigidity

/-!
# Exact finite deficits separate log-shift positivity from full Weil positivity

Sharp tail-panel completion can preserve an arbitrary initial deficit profile
while removing every later deficit. Thus summable deficit does not upgrade the
countable log-shift predicate to full positivity. An explicit existential family
has one prescribed positive normalized deficit at 2 and no deficit elsewhere.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Exact deficit truncation at the sharp prefix boundary, while meeting all later
panel-height targets and only increasing the starting coefficients. -/
theorem exists_weilLogShift_exact_deficit_prefix (base : ℕ) (lam height : ℕ → ℝ) :
    ∃ mu : ℕ → ℝ,
      (∀ n, lam n ≤ mu n) ∧
      (∀ n : ℕ, n < weilLogShiftSharpLiftIndex base → mu n = lam n) ∧
      (∀ n : ℕ, weilLogShiftSharpLiftIndex base ≤ n →
        (ArithmeticFunction.vonMangoldt n : ℝ) ≤ mu n) ∧
      (∀ n : ℕ, max ((ArithmeticFunction.vonMangoldt n : ℝ) - mu n) 0 / Real.sqrt n =
        if n < weilLogShiftSharpLiftIndex base then
          max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n else 0) ∧
      (Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - mu n) 0 / Real.sqrt n) ∧
      ∀ k : ℕ, base + 1 ≤ k → ∀ m, height k < (weilLogShiftWindowPanel k mu m).re := by
  let N := weilLogShiftSharpLiftIndex base
  let v : ℕ → ℝ := fun n =>
    if n < N then lam n else max (lam n) (ArithmeticFunction.vonMangoldt n : ℝ)
  have hNr : (0 : ℝ) < N :=
    (Real.exp_pos _).trans (weilLogShiftSharpLiftIndex_bounds base).1
  have hN : 0 < N := by exact_mod_cast hNr
  have hB : N - 1 < weilLogShiftSharpLiftIndex base := by change N - 1 < N; omega
  obtain ⟨mu, hvmu, hhead, hpanel⟩ :=
    (weilTailPanelHeadCompletable_iff base (N - 1)).mpr hB v height
  have hlv (n : ℕ) : lam n ≤ v n := by
    dsimp only [v]
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  have heq (n : ℕ) (hn : n < N) : mu n = lam n := by
    have h := hhead n (by omega)
    simpa only [v, if_pos hn] using h
  have hge (n : ℕ) (hn : N ≤ n) : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ mu n := by
    have hv : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ v n := by
      dsimp only [v]
      rw [if_neg (by omega : ¬n < N)]
      exact le_max_right _ _
    exact hv.trans (hvmu n)
  have hdef (n : ℕ) : max ((ArithmeticFunction.vonMangoldt n : ℝ) - mu n) 0 / Real.sqrt n =
      if n < N then max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n else 0 := by
    by_cases hn : n < N
    · rw [if_pos hn, heq n hn]
    · rw [if_neg hn, max_eq_right (sub_nonpos.mpr (hge n (by omega))), zero_div]
  have hsum : Summable fun n =>
      max ((ArithmeticFunction.vonMangoldt n : ℝ) - mu n) 0 / Real.sqrt n := by
    refine summable_of_ne_finset_zero (s := Finset.range N) ?_
    intro n hn
    have hn' : ¬n < N := by simpa only [Finset.mem_range] using hn
    rw [hdef n, if_neg hn']
  exact ⟨mu, fun n => (hlv n).trans (hvmu n), heq, hge, hdef, hsum, hpanel⟩

/-- A single normalized deficit of any prescribed positive size is compatible with every
countable log-shift test, but incompatible with full Weil positivity. -/
theorem exists_weilLogShift_single_deficit_separation (t : ℝ) :
    ∃ lam : ℕ → ℝ,
      WeilLogShiftTestsPositive lam ∧
      (∀ n : ℕ, n ≠ 2 → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      lam 2 = (ArithmeticFunction.vonMangoldt 2 : ℝ) - Real.exp t * Real.sqrt 2 ∧
      (∀ n : ℕ, max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n =
        if n = 2 then Real.exp t else 0) ∧
      (Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n) ∧
      ¬ WeilPositiveFull lam := by
  let seed : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) -
    if n = 2 then Real.exp t * Real.sqrt 2 else 0
  obtain ⟨lam, hseed, hhead, _, _, hsum, hpanel⟩ :=
    exists_weilLogShift_exact_deficit_prefix 0 seed (fun _ => 0)
  have hE : (2 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith only [h]
  have hNlo : Real.exp 2 < (weilLogShiftSharpLiftIndex 0 : ℝ) := by
    simpa using (weilLogShiftSharpLiftIndex_bounds 0).1
  have hN2 : 2 < weilLogShiftSharpLiftIndex 0 := by exact_mod_cast hE.trans hNlo
  have hv : lam 2 = (ArithmeticFunction.vonMangoldt 2 : ℝ) - Real.exp t * Real.sqrt 2 :=
    hhead 2 hN2
  have hge (n : ℕ) (hn : n ≠ 2) : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := by
    simpa only [seed, if_neg hn, sub_zero] using hseed n
  have hs2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hdelta : 0 < Real.exp t * Real.sqrt 2 := mul_pos (Real.exp_pos _) hs2
  have hpoint (n : ℕ) : max ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) 0 / Real.sqrt n =
      if n = 2 then Real.exp t else 0 := by
    by_cases hn : n = 2
    · subst n
      have hd : (ArithmeticFunction.vonMangoldt 2 : ℝ) - lam 2 = Real.exp t * Real.sqrt 2 := by
        rw [hv]
        ring
      rw [hd, if_pos rfl, max_eq_left hdelta.le]
      exact mul_div_cancel_right₀ _ hs2.ne'
    · rw [if_neg hn, max_eq_right (sub_nonpos.mpr (hge n hn)), zero_div]
  refine ⟨lam, ?_, hge, hv, hpoint, hsum, ?_⟩
  · intro k m hm2 hmE
    by_cases hk : k = 0
    · subst k
      norm_num at hmE
      omega
    · have hm : m ∈ Finset.Icc 2 ⌊Real.exp (2 * (k : ℝ))⌋₊ :=
        Finset.mem_Icc.mpr ⟨hm2, Nat.le_floor hmE⟩
      exact (hpanel k (by omega) ⟨m, hm⟩).le
  · intro hW
    have heq := eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW hsum 2 (by norm_num)
    linarith only [heq, hv, hdelta]

end RHTower

end
