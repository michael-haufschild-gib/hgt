import GaloisForLFunctions.RHTower.WeilLogShiftGramSimplexBasis

/-!
# Exact positive representations by a fixed finite Gram dictionary

Every functional on a finite coefficient support is a nonnegative combination
of at most `d` tests from one fixed minimal `d+1`-test certificate. This is an
exact identity of linear functionals, with no closure or approximation.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

theorem finiteWeilGram_sum_erase [DecidableEq FiniteWeilGramTest]
    (tests : Finset FiniteWeilGramTest)
    (w₀ : FiniteWeilGramTest) (hw₀ : w₀ ∈ tests) (f : tests → ℝ) :
    (∑ j : tests.erase w₀, f ⟨j.1, (Finset.mem_erase.mp j.2).2⟩) +
      f ⟨w₀, hw₀⟩ = ∑ w : tests, f w := by
  let g : FiniteWeilGramTest → ℝ := fun w => if hw : w ∈ tests then f ⟨w, hw⟩ else 0
  have hfull : ∑ w ∈ tests, g w = ∑ w : tests, f w := by
    rw [Finset.sum_subtype tests (fun _ => Iff.rfl) g]
    apply Finset.sum_congr rfl
    intro w _
    simp only [g, dif_pos w.2]
  have htail : ∑ w ∈ tests.erase w₀, g w =
      ∑ j : tests.erase w₀, f ⟨j.1, (Finset.mem_erase.mp j.2).2⟩ := by
    rw [Finset.sum_subtype (tests.erase w₀) (fun _ => Iff.rfl) g]
    apply Finset.sum_congr rfl
    intro w _
    simp only [g, dif_pos (Finset.mem_erase.mp w.2).2]
  have h := Finset.sum_erase_add tests g hw₀
  rw [hfull, htail] at h
  simpa only [g, dif_pos hw₀] using h

theorem exists_finiteWeilGram_positive_balance_and_span {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (w₀ : FiniteWeilGramTest) (hw₀ : w₀ ∈ tests) :
    ∃ a : tests → ℝ, (∀ w, 0 < a w) ∧
      (∀ c : s → ℝ, ∑ w, a w * finiteWeilGramForm s w.1 c = 0) ∧
      ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ b : tests → ℝ,
        ∀ c : s → ℝ, L c = ∑ w, b w * finiteWeilGramForm s w.1 c := by
  obtain ⟨a₀, ha₀, hbal⟩ := exists_finiteWeilGram_positive_balance hcert hcard w₀ hw₀
  let a : tests → ℝ := fun w =>
    if h : w.1 = w₀ then 1 else a₀ ⟨w.1, Finset.mem_erase.mpr ⟨h, w.2⟩⟩
  have hahead : a ⟨w₀, hw₀⟩ = 1 := by simp only [a, dif_pos rfl]
  have hatail (j : tests.erase w₀) :
      a ⟨j.1, (Finset.mem_erase.mp j.2).2⟩ = a₀ j := by
    simp only [a, dif_neg (Finset.mem_erase.mp j.2).1]
  refine ⟨a, ?_, ?_, ?_⟩
  · intro w
    dsimp [a]
    split_ifs
    · norm_num
    · exact ha₀ _
  · intro c
    have h := finiteWeilGram_sum_erase tests w₀ hw₀ (fun w => a w * finiteWeilGramForm s w.1 c)
    simp only [hatail, hahead, one_mul] at h
    linarith [hbal c]
  · intro L
    obtain ⟨u, hu, _⟩ := exists_finiteWeilGram_erase_coordinates hcert hcard w₀ hw₀
    let b : tests → ℝ := fun w =>
      if h : w.1 = w₀ then 0 else L (u ⟨w.1, Finset.mem_erase.mpr ⟨h, w.2⟩⟩)
    have hbhead : b ⟨w₀, hw₀⟩ = 0 := by simp only [b, dif_pos rfl]
    have hbtail (j : tests.erase w₀) :
        b ⟨j.1, (Finset.mem_erase.mp j.2).2⟩ = L (u j) := by
      simp only [b, dif_neg (Finset.mem_erase.mp j.2).1]
    refine ⟨b, ?_⟩
    intro c
    have h := finiteWeilGram_sum_erase tests w₀ hw₀ (fun w => b w * finiteWeilGramForm s w.1 c)
    simp only [hbtail, hbhead, zero_mul, add_zero] at h
    have he := congrArg L (hu c)
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm] at he
    exact he.trans h

theorem finiteWeilGram_minimal_positive_representation {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (L : (s → ℝ) →ₗ[ℝ] ℝ) :
    ∃ a : tests → ℝ, (∀ w, 0 ≤ a w) ∧
      (Finset.univ.filter fun w => a w ≠ 0).card ≤ s.card ∧
      ∀ c : s → ℝ, L c = ∑ w, a w * finiteWeilGramForm s w.1 c := by
  have hne : tests.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨a, ha, hbal, hspan⟩ := exists_finiteWeilGram_positive_balance_and_span hcert hcard w₀ hw₀
  obtain ⟨b, hb⟩ := hspan L
  obtain ⟨j, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset tests)
    (fun w => b w / a w) ⟨⟨w₀, hw₀⟩, Finset.mem_univ _⟩
  let q : tests → ℝ := fun w => b w - (b j / a j) * a w
  have hq (w : tests) : 0 ≤ q w :=
    sub_nonneg.mpr ((le_div_iff₀ (ha w)).mp (hmin w (Finset.mem_univ w)))
  have hqj : q j = 0 := by
    dsimp [q]
    rw [div_mul_cancel₀ _ (ne_of_gt (ha j)), sub_self]
  refine ⟨q, hq, ?_, ?_⟩
  · have hsub : (Finset.univ.filter fun w => q w ≠ 0) ⊆ Finset.univ.erase j := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ w⟩
      intro heq
      subst w
      exact (Finset.mem_filter.mp hw).2 hqj
    have hle := Finset.card_le_card hsub
    have heq := Finset.card_erase_add_one (Finset.mem_univ j)
    simp only [Finset.card_univ, Fintype.card_coe] at heq
    omega
  · intro c
    rw [hb c]
    simp only [q, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hbal c, mul_zero, sub_zero]

/-- One fixed minimal dictionary exactly represents every coefficient functional
with nonnegative weights and at most `s.card` nonzero terms. -/
theorem exists_finiteWeilGram_positive_dictionary (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ L : (s → ℝ) →ₗ[ℝ] ℝ, ∃ a : tests → ℝ, (∀ w, 0 ≤ a w) ∧
        (Finset.univ.filter fun w => a w ≠ 0).card ≤ s.card ∧
        ∀ c : s → ℝ, L c = ∑ w, a w * finiteWeilGramForm s w.1 c := by
  obtain ⟨tests, hcert, hcard, _⟩ := exists_finiteWeilGram_minimal_card_certificate s
  refine ⟨tests, hcert, hcard, ?_⟩
  intro L
  by_cases hs : s = ∅
  · subst s
    refine ⟨0, fun _ => le_rfl, by simp, ?_⟩
    intro c
    have hc : c = 0 := by
      funext i
      exact False.elim (Finset.notMem_empty i.1 i.2)
    simp only [hc, map_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · exact finiteWeilGram_minimal_positive_representation hcert
      (by simpa only [hs, if_false] using hcard) L

/-- Every minimal certificate has the basis and strictly positive balance
properties, including the vacuous empty-support case. -/
theorem exists_finiteWeilGram_simplex_certificate [DecidableEq FiniteWeilGramTest]
    (s : Finset ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, FiniteWeilGramNormCertificate s tests ∧
      tests.card = (if s = ∅ then 0 else s.card + 1) ∧
      ∀ w₀ ∈ tests,
        Function.Bijective (finiteWeilGramEvaluation s (tests.erase w₀)) ∧
        ∃ a : (tests.erase w₀) → ℝ, (∀ j, 0 < a j) ∧
          ∀ c : s → ℝ, finiteWeilGramForm s w₀ c +
            ∑ j, a j * finiteWeilGramForm s j.1 c = 0 := by
  obtain ⟨tests, hcert, hcard, _⟩ := exists_finiteWeilGram_minimal_card_certificate s
  refine ⟨tests, hcert, hcard, ?_⟩
  intro w₀ hw₀
  have hs : s ≠ ∅ := by
    intro heq
    simp only [heq, if_true] at hcard
    have ht := Finset.card_eq_zero.mp hcard
    simp only [ht, Finset.notMem_empty] at hw₀
  have hc : tests.card = s.card + 1 := by simpa only [hs, if_false] using hcard
  exact ⟨finiteWeilGram_erase_evaluation_bijective hcert hc w₀ hw₀,
    exists_finiteWeilGram_positive_balance hcert hc w₀ hw₀⟩

end RHTower
