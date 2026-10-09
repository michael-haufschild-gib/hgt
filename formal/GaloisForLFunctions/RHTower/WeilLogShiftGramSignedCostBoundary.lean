import GaloisForLFunctions.RHTower.WeilLogShiftGramCanonicalDictionary

/-!
# The exact scalar boundary for arbitrary signed Gram costs

All feasible weights in a minimal dictionary form a positive ray. A signed
cost is bounded below exactly when its slope on that ray is nonnegative.
The theorem records every attainable cost, upper-budget feasibility, and
uniqueness of the endpoint at every nonzero slope.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

private theorem gram_nonnegative_affine_range (C S R : ℝ) :
    (∃ t : ℝ, 0 ≤ t ∧ R = C + t * S) ↔
      (0 < S ∧ C ≤ R) ∨ (S = 0 ∧ R = C) ∨ (S < 0 ∧ R ≤ C) := by
  constructor
  · rintro ⟨t, ht, he⟩
    rcases lt_trichotomy 0 S with hp | hz | hn
    · exact Or.inl ⟨hp, by have h := mul_nonneg ht hp.le; linarith⟩
    · exact Or.inr (Or.inl ⟨hz.symm,
        by simpa only [← hz, mul_zero, add_zero] using he⟩)
    · exact Or.inr (Or.inr ⟨hn, by
        have h := mul_nonpos_of_nonneg_of_nonpos ht hn.le
        linarith⟩)
  · rintro (⟨hp, hCR⟩ | ⟨_, hRC⟩ | ⟨hn, hRC⟩)
    · refine ⟨(R - C) / S, div_nonneg (sub_nonneg.mpr hCR) hp.le, ?_⟩
      rw [div_mul_cancel₀ _ (ne_of_gt hp)]
      ring
    · exact ⟨0, le_rfl, by simpa only [zero_mul, add_zero] using hRC⟩
    · refine ⟨(R - C) / S, div_nonneg_of_nonpos (sub_nonpos.mpr hRC) hn.le, ?_⟩
      rw [div_mul_cancel₀ _ (ne_of_lt hn)]
      ring

/-- Costs may have arbitrary signs. Their aggregate slope on the positive
relation, rather than coordinatewise nonnegativity, is the exact invariant
for boundedness. The dictionary and its direction precede all targets/costs. -/
theorem exists_finiteWeilGram_signed_cost_dictionary (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∃ a : tests → ℝ, (∀ w, 0 < a w) ∧
        (∀ c : s → ℝ, ∑ w, a w * finiteWeilGramForm s w.1 c = 0) ∧
        ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ q : tests → ℝ, (∀ w, 0 ≤ q w) ∧
          (Finset.univ.filter fun w => q w ≠ 0).card ≤ s.card ∧
          (∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c) ∧
          ∀ κ : tests → ℝ,
            let S := ∑ w, a w * κ w
            let C := ∑ w, q w * κ w
            (∀ R : ℝ,
              (∃ b : tests → ℝ, (∀ w, 0 ≤ b w) ∧
                (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ∧
                (∑ w, b w * κ w) = R) ↔
              (0 < S ∧ C ≤ R) ∨ (S = 0 ∧ R = C) ∨ (S < 0 ∧ R ≤ C)) ∧
            (∀ R : ℝ,
              (∃ b : tests → ℝ, (∀ w, 0 ≤ b w) ∧
                (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ∧
                (∑ w, b w * κ w) ≤ R) ↔ S < 0 ∨ C ≤ R) ∧
            ((∃ M : ℝ, ∀ b : tests → ℝ, (∀ w, 0 ≤ b w) →
              (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) →
              M ≤ ∑ w, b w * κ w) ↔ 0 ≤ S) ∧
            (S ≠ 0 → ∀ b : tests → ℝ, (∀ w, 0 ≤ b w) →
              (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) →
              ((∑ w, b w * κ w) = C ↔ b = q)) := by
  obtain ⟨tests, hcert, hcard, a, ha, hbal, hdata⟩ := exists_finiteWeilGram_ray_dictionary s
  refine ⟨tests, hcert, hcard, a, ha, hbal, ?_⟩
  intro L
  obtain ⟨q, hq, hsparse, hrep, hray⟩ := hdata L
  refine ⟨q, hq, hsparse, hrep, ?_⟩
  intro κ
  let S : ℝ := ∑ w, a w * κ w
  let C : ℝ := ∑ w, q w * κ w
  have hcost (t : ℝ) : (∑ w, (q w + t * a w) * κ w) = C + t * S := by
    simp only [C, S, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcostb (b : tests → ℝ) (t : ℝ) (he : ∀ w, b w = q w + t * a w) :
      (∑ w, b w * κ w) = C + t * S := by
    simpa only [he] using hcost t
  have hrange (R : ℝ) :
      (∃ b : tests → ℝ, (∀ w, 0 ≤ b w) ∧
        (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ∧
        (∑ w, b w * κ w) = R) ↔
      (0 < S ∧ C ≤ R) ∨ (S = 0 ∧ R = C) ∨ (S < 0 ∧ R ≤ C) := by
    constructor
    · rintro ⟨b, hb, hbrep, he⟩
      obtain ⟨t, ht, hw⟩ := (hray b).mp ⟨hb, hbrep⟩
      exact (gram_nonnegative_affine_range C S R).mp
        ⟨t, ht, he.symm.trans (hcostb b t hw)⟩
    · intro h
      obtain ⟨t, ht, he⟩ := (gram_nonnegative_affine_range C S R).mpr h
      let b : tests → ℝ := fun w => q w + t * a w
      have hb := (hray b).mpr ⟨t, ht, fun _ => rfl⟩
      exact ⟨b, hb.1, hb.2, (hcost t).trans he.symm⟩
  have hbudget (R : ℝ) :
      (∃ b : tests → ℝ, (∀ w, 0 ≤ b w) ∧
        (∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ∧
        (∑ w, b w * κ w) ≤ R) ↔ S < 0 ∨ C ≤ R := by
    constructor
    · rintro ⟨b, hb, hbrep, hle⟩
      rcases (hrange (∑ w, b w * κ w)).mp ⟨b, hb, hbrep, rfl⟩ with
        ⟨_, hC⟩ | ⟨_, he⟩ | ⟨hn, _⟩
      · exact Or.inr (hC.trans hle)
      · exact Or.inr (by rwa [he] at hle)
      · exact Or.inl hn
    · rintro (hn | hC)
      · obtain ⟨b, hb, hbrep, he⟩ := (hrange (min C R)).mpr
          (Or.inr (Or.inr ⟨hn, min_le_left C R⟩))
        exact ⟨b, hb, hbrep, he.le.trans (min_le_right C R)⟩
      · exact ⟨q, hq, hrep, hC⟩
  refine ⟨hrange, hbudget, ?_, ?_⟩
  · constructor
    · rintro ⟨M, hM⟩
      by_contra hn
      have hn' : S < 0 := lt_of_not_ge hn
      obtain ⟨b, hb, hbrep, hle⟩ := (hbudget (M - 1)).mpr (Or.inl hn')
      have h := hM b hb hbrep
      linarith
    · intro hS
      refine ⟨C, ?_⟩
      intro b hb hbrep
      rcases (hrange (∑ w, b w * κ w)).mp ⟨b, hb, hbrep, rfl⟩ with
        ⟨_, hC⟩ | ⟨_, he⟩ | ⟨hn, _⟩
      · exact hC
      · exact he.symm.le
      · linarith
  · intro hS b hb hbrep
    constructor
    · intro he
      obtain ⟨t, _, hw⟩ := (hray b).mp ⟨hb, hbrep⟩
      have hv := hcostb b t hw
      have ht : t = 0 :=
        (mul_eq_zero.mp (show t * S = 0 by linarith)).resolve_right hS
      funext w
      simpa only [ht, zero_mul, add_zero] using hw w
    · rintro rfl
      rfl

end RHTower
