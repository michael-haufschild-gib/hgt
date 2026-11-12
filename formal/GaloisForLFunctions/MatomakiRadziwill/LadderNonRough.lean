import GaloisForLFunctions.MatomakiRadziwill.LadderNumericsExceptional
import GaloisForLFunctions.RHTower.Sieve.RoughCountTuran

/-!
# The integers outside the rough set

`F(w) = Σ_{X < n ≤ 4X} f(n)/n · n^{2πiw}` differs from the rough polynomial `F_S` by the integers
with no prime factor in some scale.  By Turán's second moment (`Sieve.card_roughSet_le`) at most
`M/A + 2#Pr/A` integers `n ≤ M` avoid a prime set `Pr`, `A = Σ_{p ∈ Pr} 1/p`, so with the mean value
theorem (`integral_normSq_sum_unitLogPhase_le`) (`integral_normSq_full_sub_rough_le`):

`∫_{|w|≤W} |F − F_S|² ≤ (5πW/2 + 10eX) X^{-2} Σ_{scales} (4X + 2#Pr)/A_Pr`.
-/

open Finset MeasureTheory RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The polynomial over all of `(X, 4X]`. -/
def fullPoly (f : ℕ → ℂ) (X : ℕ) (w : ℝ) : ℂ := logPoly (coefA f) (Ioc X (4 * X)) w

theorem not_hits_iff_mem_rough {Pr : Finset ℕ} {n M : ℕ} (hn : n ∈ Icc 1 M) :
    ¬ LadderScales.hits Pr n ↔ n ∈ supportMeanSquareRoughSet Pr M := by
  rw [supportMeanSquareRoughSet, mem_filter, primeFactorsIn, filter_eq_empty_iff]
  unfold LadderScales.hits
  constructor
  · intro h; exact ⟨hn, fun p hp hpn => h ⟨p, hp, hpn⟩⟩
  · rintro ⟨-, h⟩ ⟨p, hp, hpn⟩; exact h hp hpn

namespace LadderScales

variable (L : LadderScales)

/-- The integers of `(X, 4X]` outside the rough set avoid some scale. -/
theorem sdiff_ladderS_subset (X : ℕ) :
    Ioc X (4 * X) \ L.ladderS X
      ⊆ (range L.J).biUnion (fun j => supportMeanSquareRoughSet (L.scale j) (4 * X))
        ∪ supportMeanSquareRoughSet L.top (4 * X) := by
  classical
  intro n hn
  rw [mem_sdiff] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hIcc : n ∈ Icc 1 (4 * X) := by rw [mem_Ioc] at hn1; rw [mem_Icc]; omega
  rw [ladderS, mem_filter] at hn2
  have hn2' : ¬ ((∀ i ∈ range L.J, hits (L.scale i) n) ∧ hits L.top n) := fun h => hn2 ⟨hn1, h⟩
  rw [not_and_or] at hn2'
  rw [mem_union]
  rcases hn2' with h | h
  · left
    push Not at h
    obtain ⟨i, hi, hni⟩ := h
    exact mem_biUnion.mpr ⟨i, hi, (not_hits_iff_mem_rough hIcc).mp hni⟩
  · right
    exact (not_hits_iff_mem_rough hIcc).mp h

/-- **The full polynomial minus the rough one.** -/
theorem integral_normSq_full_sub_rough_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X : ℕ} (hX : 1 ≤ X)
    {W : ℝ} (hW : 1 ≤ W)
    (hA : ∀ j ∈ range L.J, 0 < ∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
    (hAtop : 0 < ∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖fullPoly f X w - logPoly (coefA f) (L.ladderS X) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ)) / (X : ℝ) ^ 2
        * (∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
            / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
          + (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ))) := by
  classical
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set N := Ioc X (4 * X) \ L.ladderS X with hNdef
  have hSsub : L.ladderS X ⊆ Ioc X (4 * X) := filter_subset _ _
  have hdiff : ∀ w, fullPoly f X w - logPoly (coefA f) (L.ladderS X) w
      = ∑ n ∈ N, coefA f n * unitLogPhase w n := by
    intro w
    rw [fullPoly, logPoly_eq_sum_mul_unitLogPhase, logPoly_eq_sum_mul_unitLogPhase,
      ← sum_sdiff hSsub, add_sub_cancel_right]
  simp_rw [hdiff]
  have hNpos : ∀ n ∈ N, 0 < n := fun n hn => by
    rw [hNdef, mem_sdiff, mem_Ioc] at hn; omega
  have hNle : ∀ n ∈ N, n ≤ 4 * X := fun n hn => by
    rw [hNdef, mem_sdiff, mem_Ioc] at hn; exact hn.1.2
  have hbase := integral_normSq_sum_unitLogPhase_le N id (coefA f) hNpos hNle hW
  have hfib : ∑ n ∈ N.image id, ‖∑ i ∈ N with id i = n, coefA f i‖ ^ (2 : ℕ)
      = ∑ n ∈ N, ‖coefA f n‖ ^ 2 := by
    rw [image_id]
    refine sum_congr rfl fun n hn => ?_
    have : N.filter (fun i => id i = n) = {n} := by
      ext i; simp only [mem_filter, Finset.mem_singleton, id]
      exact ⟨fun h => h.2, by rintro rfl; exact ⟨hn, rfl⟩⟩
    rw [this, sum_singleton]
  rw [hfib] at hbase
  -- each coefficient is at most `1/X`
  have hterm : ∀ n ∈ N, ‖coefA f n‖ ^ 2 ≤ 1 / (X : ℝ) ^ 2 := by
    intro n hn
    have hXn : (X : ℝ) < n := by
      rw [hNdef, mem_sdiff, mem_Ioc] at hn; exact_mod_cast hn.1.1
    have h1 : ‖coefA f n‖ ≤ 1 / X :=
      (norm_coefA_le hf n).trans (one_div_le_one_div_of_le hX0 hXn.le)
    calc ‖coefA f n‖ ^ 2 ≤ (1 / (X : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 1 / (X : ℝ) ^ 2 := by ring
  have hsum : ∑ n ∈ N, ‖coefA f n‖ ^ 2 ≤ (N.card : ℝ) / (X : ℝ) ^ 2 := by
    calc ∑ n ∈ N, ‖coefA f n‖ ^ 2 ≤ ∑ _n ∈ N, 1 / (X : ℝ) ^ 2 := sum_le_sum hterm
      _ = (N.card : ℝ) / (X : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul]; ring
  -- the count of `N`
  have hcard : (N.card : ℝ) ≤ ∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
        / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
      + (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)) := by
    have h1 := card_le_card (L.sdiff_ladderS_subset X)
    have h2 := card_union_le ((range L.J).biUnion
      (fun j => supportMeanSquareRoughSet (L.scale j) (4 * X)))
      (supportMeanSquareRoughSet L.top (4 * X))
    have h3 := card_biUnion_le (s := range L.J)
      (t := fun j => supportMeanSquareRoughSet (L.scale j) (4 * X))
    have h4 : (N.card : ℝ) ≤ ∑ j ∈ range L.J,
        ((supportMeanSquareRoughSet (L.scale j) (4 * X)).card : ℝ)
        + ((supportMeanSquareRoughSet L.top (4 * X)).card : ℝ) := by
      have : N.card ≤ ∑ j ∈ range L.J, (supportMeanSquareRoughSet (L.scale j) (4 * X)).card
          + (supportMeanSquareRoughSet L.top (4 * X)).card :=
        h1.trans (h2.trans (Nat.add_le_add_right h3 _))
      exact_mod_cast this
    have h5 : ∀ j ∈ range L.J, ((supportMeanSquareRoughSet (L.scale j) (4 * X)).card : ℝ)
        ≤ (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card) / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ)) := by
      intro j hj
      have h := card_roughSet_le (L.prime_scale j) (4 * X) (hA j hj)
      rw [add_div]
      linarith
    have h6 : ((supportMeanSquareRoughSet L.top (4 * X)).card : ℝ)
        ≤ (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)) := by
      have h := card_roughSet_le L.prime_top (4 * X) hAtop
      rw [add_div]
      linarith
    linarith [sum_le_sum h5]
  have hcoef0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le; have : (0 : ℝ) ≤ W := by linarith
    positivity
  calc (∫ w in Set.Icc (-W) W, ‖∑ n ∈ N, coefA f n * unitLogPhase w n‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ))
          * ∑ n ∈ N, ‖coefA f n‖ ^ 2 := hbase
    _ ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ))
          * ((N.card : ℝ) / (X : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsum hcoef0
    _ ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ))
          * ((∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
              / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
            + (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)))
            / (X : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef0
        exact div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end LadderScales

end

end GaloisForLFunctions.MatomakiRadziwill
