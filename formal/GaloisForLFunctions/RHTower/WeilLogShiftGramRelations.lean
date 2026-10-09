import GaloisForLFunctions.RHTower.WeilLogShiftGramPositiveDictionary

/-! # The one-dimensional relation space of a minimal Gram dictionary -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

theorem finiteWeilGram_relation_zero_of_zero_coordinate {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (r : tests → ℝ)
    (hr : ∀ c : s → ℝ, ∑ w, r w * finiteWeilGramForm s w.1 c = 0)
    (j : tests) (hj : r j = 0) : r = 0 := by
  funext w
  change r w = 0
  by_cases hw : w = j
  · simpa only [hw] using hj
  have hw' : w.1 ≠ j.1 := fun h => hw (Subtype.ext h)
  let k : tests.erase j.1 := ⟨w.1, Finset.mem_erase.mpr ⟨hw', w.2⟩⟩
  obtain ⟨c, hc⟩ :=
    (finiteWeilGram_erase_evaluation_bijective hcert hcard j.1 j.2).surjective
      (Pi.single k 1)
  have heval (z : tests.erase j.1) : finiteWeilGramForm s z.1 c =
      (Pi.single k (1 : ℝ) : tests.erase j.1 → ℝ) z := congrFun hc z
  have hsum (f : (tests.erase j.1) → ℝ) :
      ∑ z, f z * finiteWeilGramForm s z.1 c = f k := by
    simp_rw [heval]
    simp [Pi.single_apply]
  have h := finiteWeilGram_sum_erase tests j.1 j.2
    (fun z => r z * finiteWeilGramForm s z.1 c)
  rw [hsum, hr c] at h
  simpa only [hj, zero_mul, add_zero] using h

/-- Every relation is a scalar multiple of any strictly positive relation. -/
theorem finiteWeilGram_relation_eq_positive_direction {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (a : tests → ℝ) (ha : ∀ w, 0 < a w)
    (hbal : ∀ c : s → ℝ, ∑ w, a w * finiteWeilGramForm s w.1 c = 0)
    (r : tests → ℝ)
    (hr : ∀ c : s → ℝ, ∑ w, r w * finiteWeilGramForm s w.1 c = 0) :
    ∃ t : ℝ, ∀ w, r w = t * a w := by
  obtain ⟨w₀, hw₀⟩ := (show tests.Nonempty from Finset.card_pos.mp (by omega))
  let j : tests := ⟨w₀, hw₀⟩
  let t : ℝ := r j / a j
  let v : tests → ℝ := fun w => r w - t * a w
  have hv : ∀ c : s → ℝ, ∑ w, v w * finiteWeilGramForm s w.1 c = 0 := by
    intro c
    simp only [v, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hr c, hbal c, mul_zero, sub_self]
  have hvj : v j = 0 := by
    dsimp [v, t]
    rw [div_mul_cancel₀ _ (ne_of_gt (ha j)), sub_self]
  have hz := finiteWeilGram_relation_zero_of_zero_coordinate hcert hcard v hv j hvj
  refine ⟨t, ?_⟩
  intro w
  have hw := congrFun hz w
  change r w - t * a w = 0 at hw
  linarith

/-- A positive relation together with one boundary representation determines
all nonnegative representations as a ray. -/
theorem finiteWeilGram_positive_representation_ray {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (a : tests → ℝ) (ha : ∀ w, 0 < a w)
    (hbal : ∀ c : s → ℝ, ∑ w, a w * finiteWeilGramForm s w.1 c = 0)
    (L : (s → ℝ) →ₗ[ℝ] ℝ) (q : tests → ℝ) (hq : ∀ w, 0 ≤ q w)
    (hqrep : ∀ c : s → ℝ, L c = ∑ w, q w * finiteWeilGramForm s w.1 c)
    (hqzero : ∃ w, q w = 0) (b : tests → ℝ) :
    ((∀ w, 0 ≤ b w) ∧ ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c) ↔
      ∃ t : ℝ, 0 ≤ t ∧ ∀ w, b w = q w + t * a w := by
  constructor
  · rintro ⟨hb, hbrep⟩
    have hr : ∀ c : s → ℝ,
        ∑ w, (b w - q w) * finiteWeilGramForm s w.1 c = 0 := by
      intro c
      simp only [sub_mul, Finset.sum_sub_distrib, ← hbrep c, ← hqrep c, sub_self]
    obtain ⟨t, ht⟩ := finiteWeilGram_relation_eq_positive_direction
      hcert hcard a ha hbal (fun w => b w - q w) hr
    have ht0 : 0 ≤ t := by
      obtain ⟨w, hw⟩ := hqzero
      have he := ht w
      rw [hw, sub_zero] at he
      by_contra hn
      have hn' : t < 0 := lt_of_not_ge hn
      have hm := mul_neg_of_neg_of_pos hn' (ha w)
      linarith [hb w]
    refine ⟨t, ht0, ?_⟩
    intro w
    linarith [ht w]
  · rintro ⟨t, ht, he⟩
    refine ⟨fun w => ?_, ?_⟩
    · rw [he w]
      exact add_nonneg (hq w) (mul_nonneg ht (ha w).le)
    · intro c
      simp only [he, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
        hbal c, mul_zero, add_zero, ← hqrep c]

end RHTower
