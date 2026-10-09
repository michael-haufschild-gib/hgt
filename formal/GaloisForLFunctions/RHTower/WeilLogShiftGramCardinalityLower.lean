import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth

/-! # Every nontrivial finite Gram certificate needs more tests than coefficients -/

namespace RHTower

theorem finiteWeilGram_certificate_card_lower {s : Finset ℕ}
    (hs : s.Nonempty) {tests : Finset FiniteWeilGramTest}
    (hcert : FiniteWeilGramNormCertificate s tests) : s.card + 1 ≤ tests.card := by
  classical
  obtain ⟨i, hi⟩ := hs
  let e : s → ℝ := Pi.single ⟨i, hi⟩ 1
  have he : e ≠ 0 := by
    intro hz
    have hv := congrFun hz ⟨i, hi⟩
    simp [e] at hv
  obtain ⟨w, hw, _⟩ := hcert e he
  let F : (s → ℝ) →ₗ[ℝ] (tests → ℝ) :=
    LinearMap.pi fun w => finiteWeilGramForm s w.1
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    by_contra hc0
    obtain ⟨z, hz, hneg⟩ := hcert c hc0
    have hv := congrFun hc ⟨z, hz⟩
    change finiteWeilGramForm s z c = 0 at hv
    linarith [norm_nonneg c]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_pi, Fintype.card_coe] at hdim
  by_contra hcard
  have hsame : s.card = tests.card := by omega
  have hsurj : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_pi, Fintype.card_coe] using hsame)).mp hinj
  obtain ⟨c, hc⟩ := hsurj (fun _ => 1)
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    have hv := congrFun hc ⟨w, hw⟩
    norm_num at hv
  obtain ⟨z, hz, hneg⟩ := hcert c hc0
  have hv := congrFun hc ⟨z, hz⟩
  change finiteWeilGramForm s z c = 1 at hv
  linarith [norm_nonneg c]

end RHTower
