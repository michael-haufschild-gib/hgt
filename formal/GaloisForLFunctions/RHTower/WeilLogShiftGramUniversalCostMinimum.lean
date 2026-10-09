import GaloisForLFunctions.RHTower.WeilLogShiftGramCanonicalDictionary

/-!
# One Gram weight vector minimizes every nonnegative dictionary cost

The dictionary is fixed before the target functional and cost. Its canonical
nonnegative representation minimizes all nonnegative linear costs at once.
For every strictly positive cost, that minimizer is unique. This does not
optimize over different choices of Gram tests.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

theorem finiteWeilGram_weighted_cost_eq_iff {ι : Type} [Fintype ι]
    (q b κ : ι → ℝ) (hqb : q ≤ b) (hκ : ∀ w, 0 < κ w) :
    (∑ w, b w * κ w) = (∑ w, q w * κ w) ↔ b = q := by
  constructor
  · intro he
    have hz : (∑ w, (b w - q w) * κ w) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, he, sub_self]
    have hn (w : ι) (_ : w ∈ (Finset.univ : Finset ι)) :
        0 ≤ (b w - q w) * κ w :=
      mul_nonneg (sub_nonneg.mpr (hqb w)) (hκ w).le
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz
    funext w
    have hw := (mul_eq_zero.mp (hterms w (Finset.mem_univ w))).resolve_right
      (ne_of_gt (hκ w))
    linarith
  · rintro rfl
    rfl

/-- A single canonical weight vector simultaneously solves every nonnegative
linear cost problem on its fixed minimal dictionary. Strictly positive costs
have that vector as their unique minimizer. -/
theorem exists_finiteWeilGram_universal_cost_minimizer (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ q : tests → ℝ, (∀ w, 0 ≤ q w) ∧
        (Finset.univ.filter fun w => q w ≠ 0).card ≤ s.card ∧
        (∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c) ∧
        (∀ κ : tests → ℝ, (∀ w, 0 ≤ κ w) → ∀ b : tests → ℝ,
          (∀ w, 0 ≤ b w) →
          (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) →
          (∑ w, q w * κ w) ≤ ∑ w, b w * κ w) ∧
        ∀ κ : tests → ℝ, (∀ w, 0 < κ w) → ∀ b : tests → ℝ,
          (∀ w, 0 ≤ b w) →
          (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) →
          ((∑ w, b w * κ w) = (∑ w, q w * κ w) ↔ b = q) := by
  obtain ⟨tests, hcert, hcard, hdata⟩ := exists_finiteWeilGram_canonical_dictionary s
  refine ⟨tests, hcert, hcard, ?_⟩
  intro L
  obtain ⟨q, ⟨hq, hsparse, hrep, hleast⟩, _⟩ := hdata L
  refine ⟨q, hq, hsparse, hrep, ?_, ?_⟩
  · intro κ hκ b hb hbrep
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul_of_nonneg_right (hleast b hb hbrep w) (hκ w)
  · intro κ hκ b hb hbrep
    exact finiteWeilGram_weighted_cost_eq_iff q b κ (hleast b hb hbrep) hκ

end RHTower
