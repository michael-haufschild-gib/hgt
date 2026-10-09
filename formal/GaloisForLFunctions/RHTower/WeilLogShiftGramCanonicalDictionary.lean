import GaloisForLFunctions.RHTower.WeilLogShiftGramRelations

/-!
# Canonical nonnegative Gram representations

For a fixed minimal dictionary the feasible weights of each functional form
one ray. Its endpoint is the unique componentwise least representation.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

/-- A fixed minimal dictionary has one positive balance direction, and every
nonnegative representation fiber is a ray from a sparse endpoint. -/
theorem exists_finiteWeilGram_ray_dictionary (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∃ a : tests → ℝ, (∀ w, 0 < a w) ∧
        (∀ c : s → ℝ, ∑ w, a w * finiteWeilGramForm s w.1 c = 0) ∧
        ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ q : tests → ℝ, (∀ w, 0 ≤ q w) ∧
          (Finset.univ.filter fun w => q w ≠ 0).card ≤ s.card ∧
          (∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c) ∧
          ∀ b : tests → ℝ,
            ((∀ w, 0 ≤ b w) ∧
              ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ↔
            ∃ t : ℝ, 0 ≤ t ∧ ∀ w, b w = q w + t * a w := by
  obtain ⟨tests, hcert, hcard, _⟩ := exists_finiteWeilGram_minimal_card_certificate s
  refine ⟨tests, hcert, hcard, ?_⟩
  by_cases hs : s = ∅
  · subst s
    have ht : tests = ∅ := Finset.card_eq_zero.mp (by simpa only [if_true] using hcard)
    subst tests
    have hc (c : (∅ : Finset ℕ) → ℝ) : c = 0 := by
      funext i
      exact False.elim (Finset.notMem_empty i.1 i.2)
    refine ⟨0, ?_, ?_, ?_⟩
    · intro w
      exact False.elim (Finset.notMem_empty w.1 w.2)
    · intro c
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · intro L
      refine ⟨0, fun _ => le_rfl, by simp, ?_, ?_⟩
      · intro c
        simp only [hc c, map_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
      · intro b
        constructor
        · intro _
          exact ⟨0, le_rfl, fun w => False.elim (Finset.notMem_empty w.1 w.2)⟩
        · intro _
          refine ⟨fun w => False.elim (Finset.notMem_empty w.1 w.2), ?_⟩
          intro c
          simp only [hc c, map_zero, mul_zero, Finset.sum_const_zero]
  · have hsize : tests.card = s.card + 1 := by simpa only [hs, if_false] using hcard
    obtain ⟨w₀, hw₀⟩ := (show tests.Nonempty from Finset.card_pos.mp (by omega))
    obtain ⟨a, ha, hbal, _⟩ :=
      exists_finiteWeilGram_positive_balance_and_span hcert hsize w₀ hw₀
    refine ⟨a, ha, hbal, ?_⟩
    intro L
    obtain ⟨q, hq, hsparse, hrep⟩ :=
      finiteWeilGram_minimal_positive_representation hcert hsize L
    have hzero : ∃ w, q w = 0 := by
      by_contra hn
      push Not at hn
      have hf : (Finset.univ.filter fun w => q w ≠ 0) = Finset.univ :=
        Finset.filter_eq_self.mpr (fun w _ => hn w)
      rw [hf, Finset.card_univ, Fintype.card_coe] at hsparse
      omega
    exact ⟨q, hq, hsparse, hrep,
      finiteWeilGram_positive_representation_ray hcert hsize a ha hbal L q hq hrep hzero⟩

/-- The endpoint of each positive representation ray is the unique
componentwise least feasible weight vector. -/
theorem exists_finiteWeilGram_canonical_dictionary (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃! q : tests → ℝ,
        (∀ w, 0 ≤ q w) ∧
        (Finset.univ.filter fun w => q w ≠ 0).card ≤ s.card ∧
        (∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c) ∧
        ∀ b : tests → ℝ, (∀ w, 0 ≤ b w) →
          (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) → q ≤ b := by
  obtain ⟨tests, hcert, hcard, a, ha, _, hdata⟩ := exists_finiteWeilGram_ray_dictionary s
  refine ⟨tests, hcert, hcard, ?_⟩
  intro L
  obtain ⟨q, hq, hsparse, hrep, hray⟩ := hdata L
  have hleast (b : tests → ℝ) (hb : ∀ w, 0 ≤ b w)
      (hbrep : ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) : q ≤ b := by
    obtain ⟨t, ht, he⟩ := (hray b).mp ⟨hb, hbrep⟩
    intro w
    rw [he w]
    exact le_add_of_nonneg_right (mul_nonneg ht (ha w).le)
  refine ⟨q, ⟨hq, hsparse, hrep, hleast⟩, ?_⟩
  rintro b ⟨hb, _, hbrep, hbleast⟩
  exact le_antisymm (hbleast q hq hrep) (hleast b hb hbrep)

end RHTower
