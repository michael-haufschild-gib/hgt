import GaloisForLFunctions.RHTower.WeilLogShiftGramMinimalCardinality

/-!
# Every facet of a minimal Gram certificate is a basis

Deleting one test from a certificate of cardinality `d+1` gives exact
interpolation on the remaining `d` tests. Its coordinate vectors have
strictly negative evaluation at the omitted test.
-/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RHTower

noncomputable def finiteWeilGramEvaluation (s : Finset ℕ) (tests : Finset FiniteWeilGramTest) :
    (s → ℝ) →ₗ[ℝ] (tests → ℝ) :=
  LinearMap.pi fun w => finiteWeilGramForm s w.1

variable [DecidableEq FiniteWeilGramTest]

theorem finiteWeilGram_erase_evaluation_bijective {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (w₀ : FiniteWeilGramTest) (hw₀ : w₀ ∈ tests) :
    Function.Bijective (finiteWeilGramEvaluation s (tests.erase w₀)) := by
  have hinj : Function.Injective (finiteWeilGramEvaluation s (tests.erase w₀)) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    by_contra hc0
    have hvanish (w : FiniteWeilGramTest) (hw : w ∈ tests) (hne : w ≠ w₀) :
        finiteWeilGramForm s w c = 0 :=
      congrFun hc ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩⟩
    obtain ⟨w, hw, hneg⟩ := hcert c hc0
    have hww₀ : w = w₀ := by
      by_contra hne
      rw [hvanish w hw hne] at hneg
      linarith [norm_nonneg c]
    subst w
    obtain ⟨z, hz, hneg'⟩ := hcert (-c) (neg_ne_zero.mpr hc0)
    have hzw₀ : z = w₀ := by
      by_contra hne
      rw [map_neg, hvanish z hz hne, neg_zero] at hneg'
      linarith [norm_nonneg (-c)]
    subst z
    rw [map_neg, norm_neg] at hneg'
    linarith [norm_nonneg c]
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
  simp only [Module.finrank_pi, Fintype.card_coe]
  have h := Finset.card_erase_add_one hw₀
  omega

theorem exists_finiteWeilGram_erase_coordinates {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (w₀ : FiniteWeilGramTest) (hw₀ : w₀ ∈ tests) :
    ∃ u : (tests.erase w₀) → s → ℝ,
      (∀ c : s → ℝ, c = ∑ j, finiteWeilGramForm s j.1 c • u j) ∧
      ∀ j, finiteWeilGramForm s w₀ (u j) < 0 := by
  let e := LinearEquiv.ofBijective (finiteWeilGramEvaluation s (tests.erase w₀))
    (finiteWeilGram_erase_evaluation_bijective hcert hcard w₀ hw₀)
  let u : (tests.erase w₀) → s → ℝ := fun j => e.symm (Pi.single j 1)
  have heval (c : s → ℝ) (j : tests.erase w₀) :
      e c j = finiteWeilGramForm s j.1 c := rfl
  refine ⟨u, ?_, ?_⟩
  · intro c
    have h := congrArg e.symm ((Pi.basisFun ℝ (tests.erase w₀)).sum_repr (e c))
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
      LinearEquiv.symm_apply_apply, heval, u] using h.symm
  · intro j
    have hu : u j ≠ 0 := by
      intro hz
      have he := e.apply_symm_apply (Pi.single j 1)
      change e (u j) = Pi.single j 1 at he
      rw [hz, map_zero] at he
      have hv := congrFun he j
      simp at hv
    obtain ⟨z, hz, hneg⟩ := hcert (u j) hu
    have hzw₀ : z = w₀ := by
      by_contra hne
      let k : tests.erase w₀ := ⟨z, Finset.mem_erase.mpr ⟨hne, hz⟩⟩
      have hv := congrFun (e.apply_symm_apply (Pi.single j 1)) k
      change finiteWeilGramForm s z (u j) =
        (Pi.single j (1 : ℝ) : tests.erase w₀ → ℝ) k at hv
      have hp : 0 ≤ (Pi.single j (1 : ℝ) : tests.erase w₀ → ℝ) k := by
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      linarith [norm_nonneg (u j)]
    subst z
    linarith [norm_nonneg (u j)]

theorem exists_finiteWeilGram_positive_balance {s : Finset ℕ}
    {tests : Finset FiniteWeilGramTest} (hcert : FiniteWeilGramNormCertificate s tests)
    (hcard : tests.card = s.card + 1) (w₀ : FiniteWeilGramTest) (hw₀ : w₀ ∈ tests) :
    ∃ a : (tests.erase w₀) → ℝ, (∀ j, 0 < a j) ∧
      ∀ c : s → ℝ, finiteWeilGramForm s w₀ c +
        ∑ j, a j * finiteWeilGramForm s j.1 c = 0 := by
  obtain ⟨u, hu, hneg⟩ := exists_finiteWeilGram_erase_coordinates hcert hcard w₀ hw₀
  refine ⟨fun j => -finiteWeilGramForm s w₀ (u j), fun j => neg_pos.mpr (hneg j), ?_⟩
  intro c
  have h := congrArg (finiteWeilGramForm s w₀) (hu c)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [h]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  ring

end RHTower
