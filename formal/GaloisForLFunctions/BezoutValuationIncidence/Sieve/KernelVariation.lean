import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Discrete variation of reciprocal kernel products

Monotone sampling and clamping at the support endpoint give variation
independent of the kernel scale. Two such kernels multiplied by `1/n`
have endpoint-plus-variation cost proportional to the inverse lower endpoint.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Total discrete variation on an integer interval. -/
def discreteVariation (f : ℕ → ℝ) (A B : ℕ) : ℝ :=
  ∑ n ∈ Ico A B, |f (n + 1) - f n|

theorem sum_Ico_difference (f : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ n ∈ Ico A B, (f n - f (n + 1))) = f A - f B := by
  induction B, hAB using Nat.le_induction with
  | base => simp only [Ico_self, sum_empty, sub_self]
  | succ B hAB ih =>
    rw [sum_Ico_succ_top hAB, ih]
    ring

/-- A Lipschitz function on a monotone unit-range path has bounded variation. -/
theorem antitone_composition_variation {f : ℝ → ℝ} {u : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    {A B : ℕ} (hAB : A ≤ B)
    (hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n)
    (hlo : 0 ≤ u B) (hhi : u A ≤ 1) :
    discreteVariation (fun n => f (u n)) A B ≤ K := by
  have hstep (n : ℕ) (hn : n ∈ Ico A B) :
      |f (u (n + 1)) - f (u n)| ≤ K * (u n - u (n + 1)) := by
    have hm := hu n (n + 1) (mem_Ico.mp hn).1 (by omega) (by have := (mem_Ico.mp hn).2; omega)
    simpa only [abs_sub_comm (u (n + 1)), abs_of_nonneg (sub_nonneg.mpr hm)] using
      hf (u (n + 1)) (u n)
  calc
    _ ≤ ∑ n ∈ Ico A B, K * (u n - u (n + 1)) := sum_le_sum hstep
    _ = K * (u A - u B) := by rw [← mul_sum, sum_Ico_difference _ hAB]
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left (by linarith only [hlo, hhi]) hK
    _ = _ := mul_one _

/-- Product variation is bounded by the two supremum-weighted variations. -/
theorem product_variation {f g : ℕ → ℝ} {F G : ℝ} {A B : ℕ}
    (hf : ∀ n ∈ Icc A B, |f n| ≤ F) (hg : ∀ n ∈ Icc A B, |g n| ≤ G) :
    discreteVariation (fun n => f n * g n) A B ≤
      F * discreteVariation g A B + G * discreteVariation f A B := by
  have hstep (n : ℕ) (hn : n ∈ Ico A B) :
      |f (n + 1) * g (n + 1) - f n * g n| ≤
        F * |g (n + 1) - g n| + G * |f (n + 1) - f n| := by
    have hn0 : n ∈ Icc A B := mem_Icc.mpr ⟨(mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩
    have hn1 : n + 1 ∈ Icc A B := mem_Icc.mpr ⟨by have := (mem_Ico.mp hn).1; omega,
      by have := (mem_Ico.mp hn).2; omega⟩
    rw [show f (n + 1) * g (n + 1) - f n * g n =
      f (n + 1) * (g (n + 1) - g n) + g n * (f (n + 1) - f n) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (hf _ hn1) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (hg _ hn0) (abs_nonneg _))
  refine (sum_le_sum hstep).trans_eq ?_
  simp only [discreteVariation, sum_add_distrib, mul_sum]

theorem inverse_variation {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    discreteVariation (fun n => 1 / (n : ℝ)) A B ≤ 1 / (A : ℝ) := by
  have hstep (n : ℕ) (hn : n ∈ Ico A B) :
      |1 / ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ)| =
        1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hA.trans (mem_Ico.mp hn).1
    have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le hn0 hnn))]
  rw [discreteVariation, sum_congr rfl hstep, sum_Ico_difference _ hAB]
  have hB : 0 ≤ 1 / (B : ℝ) := by positivity
  linarith only [hB]

/-- Two bounded kernels with bounded variation retain one inverse endpoint. -/
theorem pair_kernel_variation {f g : ℕ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hf : ∀ n ∈ Icc A B, |f n| ≤ M) (hg : ∀ n ∈ Icc A B, |g n| ≤ M)
    (hfv : discreteVariation f A B ≤ K) (hgv : discreteVariation g A B ≤ K) :
    |f B * g B / (B : ℝ)| +
      discreteVariation (fun n => f n * g n / (n : ℝ)) A B ≤
        (2 * M ^ 2 + 2 * M * K) / (A : ℝ) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hfg : ∀ n ∈ Icc A B, |f n * g n| ≤ M ^ 2 := by
    intro n hn
    rw [abs_mul, pow_two]
    exact mul_le_mul (hf n hn) (hg n hn) (abs_nonneg _) hM
  have hinv : ∀ n ∈ Icc A B, |1 / (n : ℝ)| ≤ 1 / (A : ℝ) := by
    intro n hn
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))]
    exact one_div_le_one_div_of_le hA0 (by exact_mod_cast (mem_Icc.mp hn).1)
  have hfgv : discreteVariation (fun n => f n * g n) A B ≤ 2 * M * K := by
    refine (product_variation hf hg).trans ?_
    nlinarith only [mul_le_mul_of_nonneg_left hfv hM, mul_le_mul_of_nonneg_left hgv hM]
  have hvar := product_variation hfg hinv
  have hvar' : discreteVariation (fun n => f n * g n / (n : ℝ)) A B ≤
      M ^ 2 / (A : ℝ) + 2 * M * K / (A : ℝ) := by
    simpa only [mul_one_div, div_eq_mul_inv, mul_comm (A : ℝ)⁻¹,
      mul_assoc, one_mul] using hvar.trans (add_le_add
        (mul_le_mul_of_nonneg_left (inverse_variation hA hAB) (sq_nonneg M))
        (mul_le_mul_of_nonneg_left hfgv (by positivity : 0 ≤ 1 / (A : ℝ))))
  have hend : |f B * g B / (B : ℝ)| ≤ M ^ 2 / (A : ℝ) := by
    rw [abs_div, show |(B : ℝ)| = (B : ℝ) from abs_of_nonneg (Nat.cast_nonneg B)]
    exact (div_le_div_of_nonneg_right (hfg B (mem_Icc.mpr ⟨hAB, le_rfl⟩))
      (Nat.cast_nonneg B)).trans (div_le_div_of_nonneg_left (sq_nonneg M)
      hA0 (by exact_mod_cast hAB))
  calc
    _ ≤ M ^ 2 / (A : ℝ) + (M ^ 2 / (A : ℝ) + 2 * M * K / (A : ℝ)) :=
      add_le_add hend hvar'
    _ = _ := by ring

#print axioms pair_kernel_variation

/-- Reciprocal sampling of a compact kernel has variation independent of its scale. -/
theorem clamped_reciprocal_variation {f : ℝ → ℝ} {K a : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → f x = 0) (ha : 0 ≤ a)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    discreteVariation (fun n => f (a / (n : ℝ))) A B ≤ K := by
  let u : ℕ → ℝ := fun n => min (a / (n : ℝ)) 1
  have he (n : ℕ) : f (a / (n : ℝ)) = f (u n) := by
    dsimp only [u]
    by_cases hn : a / (n : ℝ) ≤ 1
    · rw [min_eq_left hn]
    · rw [min_eq_right (le_of_not_ge hn), hf1 _ (le_of_not_ge hn), hf1 1 le_rfl]
  have hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n := by
    intro n m hAn hnm _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hA.trans hAn
    exact min_le_min_right 1 (div_le_div_of_nonneg_left ha hn0 (by exact_mod_cast hnm))
  have h := antitone_composition_variation hK hf hAB hu
    (le_min (div_nonneg ha (Nat.cast_nonneg B)) zero_le_one) (min_le_right _ _)
  simpa only [discreteVariation, ← he] using h

/-- Reciprocal kernel products have endpoint-plus-variation cost of order one over the lower endpoint. -/
theorem reciprocal_kernel_pair_variation {f : ℝ → ℝ} {M K a b : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → f x = 0) (hfM : ∀ x, |f x| ≤ M)
    (ha : 0 ≤ a) (hb : 0 ≤ b) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |f (a / (B : ℝ)) * f (b / (B : ℝ)) / (B : ℝ)| +
      discreteVariation (fun n => f (a / (n : ℝ)) * f (b / (n : ℝ)) / (n : ℝ)) A B ≤
        (2 * M ^ 2 + 2 * M * K) / (A : ℝ) :=
  pair_kernel_variation hM hA hAB (fun _ _ => hfM _) (fun _ _ => hfM _)
    (clamped_reciprocal_variation hK hf hf1 ha hA hAB)
    (clamped_reciprocal_variation hK hf hf1 hb hA hAB)

#print axioms reciprocal_kernel_pair_variation

/-- An antitone sequence has variation equal to its endpoint decrease. -/
theorem antitone_variation {u : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B)
    (hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n) :
    discreteVariation u A B = u A - u B := by
  rw [discreteVariation]
  have he (n : ℕ) (hn : n ∈ Ico A B) : |u (n + 1) - u n| = u n - u (n + 1) := by
    rw [abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr (hu n (n + 1) (mem_Ico.mp hn).1 (by omega)
      (by have := (mem_Ico.mp hn).2; omega))
  rw [sum_congr rfl he, sum_Ico_difference _ hAB]

/-- A monotone sequence has variation equal to its endpoint increase. -/
theorem monotone_variation {u : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B)
    (hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u n ≤ u m) :
    discreteVariation u A B = u B - u A := by
  have h := antitone_variation (u := fun n => -u n) hAB
    (fun n m hn hnm hm => neg_le_neg (hu n m hn hnm hm))
  simpa only [discreteVariation, neg_sub_neg, abs_sub_comm] using h

/-- Clamping a nonnegative antitone argument at the support endpoint bounds variation. -/
theorem clamped_antitone_variation {f : ℝ → ℝ} {u : ℕ → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hf1 : ∀ x, 1 ≤ x → f x = 0) {A B : ℕ} (hAB : A ≤ B)
    (hu : ∀ n m, A ≤ n → n ≤ m → m ≤ B → u m ≤ u n) (huB : 0 ≤ u B) :
    discreteVariation (fun n => f (u n)) A B ≤ K := by
  let v : ℕ → ℝ := fun n => min (u n) 1
  have he (n : ℕ) : f (u n) = f (v n) := by
    dsimp only [v]
    by_cases hn : u n ≤ 1
    · rw [min_eq_left hn]
    · rw [min_eq_right (le_of_not_ge hn), hf1 _ (le_of_not_ge hn), hf1 1 le_rfl]
  have hv : ∀ n m, A ≤ n → n ≤ m → m ≤ B → v m ≤ v n :=
    fun n m hn hnm hm => min_le_min_right 1 (hu n m hn hnm hm)
  have h := antitone_composition_variation hK hf hAB hv
    (le_min huB zero_le_one) (min_le_right _ _)
  simpa only [discreteVariation, ← he] using h

#print axioms clamped_antitone_variation

end GaloisForLFunctions.BezoutValuationIncidence
