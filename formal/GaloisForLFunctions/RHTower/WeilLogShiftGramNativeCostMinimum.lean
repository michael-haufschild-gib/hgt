import GaloisForLFunctions.RHTower.WeilLogShiftGramUniversalCostMinimum

/-!
# Canonical weights uniquely minimize the actual Gram tail cost

Every test in a nontrivial minimal certificate has strictly positive native
tail cost. Thus the canonical positive representation is the unique minimizer
for every positive cost normalization, within that fixed dictionary.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

private theorem gram_native_cost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

theorem finiteWeilGram_form_eq_zero_of_tailCost_eq_zero {B : ℝ} (hB : 0 < B)
    (w : FiniteWeilGramTest) (hw : finiteWeilGramTailCost B w = 0)
    (s : Finset ℕ) (c : s → ℝ) : finiteWeilGramForm s w c = 0 := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost] at hw
  rcases mul_eq_zero.mp hw with ha | hsum
  · rw [finiteWeilGramForm_apply, ha, neg_zero, zero_mul]
  · have hn (i j : Fin N) :
        0 ≤ |u i * u j| * (B * Real.exp (2 * |x j - x i|)) := by positivity
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))).mp hsum
    have hu (i : Fin N) : u i = 0 := by
      have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp
        (hrows i (Finset.mem_univ i)) i (Finset.mem_univ i)
      have hp : 0 < B * Real.exp (2 * |x i - x i|) := mul_pos hB (Real.exp_pos _)
      have habs := (mul_eq_zero.mp ht).resolve_right (ne_of_gt hp)
      have hmul := abs_eq_zero.mp habs
      rcases mul_eq_zero.mp hmul with h | h <;> exact h
    rw [finiteWeilGramForm_apply]
    simp only [hu, zero_mul, mul_zero, Finset.sum_const_zero]

theorem finiteWeilGram_minimal_tailCost_pos {s : Finset ℕ} (hs : s.Nonempty)
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) {B : ℝ} (hB : 0 < B)
    (w : FiniteWeilGramTest) (hw : w ∈ tests) : 0 < finiteWeilGramTailCost B w := by
  by_contra hn
  have hz : finiteWeilGramTailCost B w = 0 :=
    le_antisymm (le_of_not_gt hn) (gram_native_cost_nonneg hB.le w)
  have hzero := finiteWeilGram_form_eq_zero_of_tailCost_eq_zero hB w hz s
  have hdrop : FiniteWeilGramNormCertificate s (tests.erase w) := by
    intro c hc
    obtain ⟨z, hzt, hneg⟩ := hcert c hc
    refine ⟨z, Finset.mem_erase.mpr ⟨?_, hzt⟩, hneg⟩
    intro heq
    subst z
    rw [hzero c] at hneg
    linarith [norm_nonneg c]
  have hbound := finiteWeilGram_certificate_card_lower hs hdrop
  have herase := Finset.card_erase_add_one hw
  omega

/-- Canonical weights are chosen before the positive normalization `B` and
uniquely minimize the actual weighted tail cost within the fixed dictionary. -/
theorem exists_finiteWeilGram_native_cost_minimizer (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ q : tests → ℝ, (∀ w, 0 ≤ q w) ∧
        (Finset.univ.filter fun w => q w ≠ 0).card ≤ s.card ∧
        (∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c) ∧
        ∀ B : ℝ, 0 < B → ∀ b : tests → ℝ, (∀ w, 0 ≤ b w) →
          (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) →
          (∑ w, q w * finiteWeilGramTailCost B w.1) ≤
            (∑ w, b w * finiteWeilGramTailCost B w.1) ∧
          ((∑ w, b w * finiteWeilGramTailCost B w.1) =
            (∑ w, q w * finiteWeilGramTailCost B w.1) ↔ b = q) := by
  obtain ⟨tests, hcert, hcard, hdata⟩ := exists_finiteWeilGram_universal_cost_minimizer s
  refine ⟨tests, hcert, hcard, ?_⟩
  intro L
  obtain ⟨q, hq, hsparse, hrep, hmin, huniq⟩ := hdata L
  refine ⟨q, hq, hsparse, hrep, ?_⟩
  intro B hB b hb hbrep
  have hpos (w : tests) : 0 < finiteWeilGramTailCost B w.1 := by
    have hs : s ≠ ∅ := by
      intro he
      have ht : tests = ∅ := Finset.card_eq_zero.mp (by simpa only [he, if_true] using hcard)
      exact Finset.notMem_empty w.1 (ht ▸ w.2)
    have hc : tests.card = s.card + 1 := by simpa only [hs, if_false] using hcard
    exact finiteWeilGram_minimal_tailCost_pos (Finset.nonempty_iff_ne_empty.mpr hs)
      hcert hc hB w.1 w.2
  exact ⟨hmin _ (fun w => (hpos w).le) b hb hbrep, huniq _ hpos b hb hbrep⟩

end RHTower
