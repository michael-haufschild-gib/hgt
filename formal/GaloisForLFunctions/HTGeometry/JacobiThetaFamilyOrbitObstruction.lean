import GaloisForLFunctions.HTGeometry.CompactEllipticPoleFiniteness

/-!
# Simultaneous theta-defect orbit obstruction

A finite family of pairwise nonresonant theta defects remains outside the elliptic translation-
coboundary image after arbitrary constant-coefficient differential operators, provided one
operator is nonzero.  The shifted pole belonging to that operator is the unique pole on its
distinguished nontorsion orbit; all other family members are analytic there.  Compact elliptic
pole finiteness then converts this singleton support into the simultaneous noncoboundary theorem.
-/

open Complex Set Filter Function Metric
open scoped Topology BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- A finite constant-coefficient differential combination of translated theta defects. -/
def thetaDifferentialFamilySum {ι : Type*} (s : Finset ι)
    (L : ι → Polynomial ℂ) (h : ι → ℂ) (τ : ℂ) : ℂ → ℂ :=
  ∑ i ∈ s, constantCoeffDifferentialOperator (L i) (thetaLogDerivDefect (h i) · τ)

theorem analyticAt_thetaDifferentialFamilyTerm_on_distinguishedOrbit
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ} {τ q : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ q (h j))
    {i₀ j : ι} (hi₀ : i₀ ∈ s) (hj : j ∈ s)
    (hsep : ∀ k ∈ s, k ≠ i₀ → ThetaTranslationNonresonant τ q (h k - h i₀))
    (n : ℤ) (hnot : j ≠ i₀ ∨ n ≠ 0) :
    AnalyticAt ℂ
      (constantCoeffDifferentialOperator (L j) (thetaLogDerivDefect (h j) · τ))
      (additiveOrbitPoint (thetaHalfPeriod τ - h i₀) q n) := by
  apply analyticAt_constantCoeffDifferentialOperator_thetaLogDerivDefect_of_off_lattices hτ
  · intro a b hab
    apply hnonres i₀ hi₀
    refine ⟨-a, -b, n, ?_⟩
    dsimp [additiveOrbitPoint] at hab
    push_cast
    linear_combination -hab
  · intro a b hab
    by_cases hji : j = i₀
    · subst j
      have hn0 := hq a b n (by
        dsimp [additiveOrbitPoint] at hab
        linear_combination hab)
      exact hnot.resolve_left (by simp) hn0
    · apply hsep j hj hji
      refine ⟨a, b, -n, ?_⟩
      dsimp [additiveOrbitPoint] at hab
      push_cast
      linear_combination hab

/-- A separated finite theta-defect family has exactly one pole on the orbit belonging to any
chosen nonzero differential operator. -/
theorem thetaDifferentialFamilySum_singleton_poleOrbit
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ} {τ q : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ q (h j))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hLi₀ : L i₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ i₀ → ThetaTranslationNonresonant τ q (h j - h i₀)) :
    meromorphicOrderAt (thetaDifferentialFamilySum s L h τ)
        (thetaHalfPeriod τ - h i₀) < 0 ∧
      ∀ n : ℤ, meromorphicOrderAt (thetaDifferentialFamilySum s L h τ)
          (additiveOrbitPoint (thetaHalfPeriod τ - h i₀) q n) < 0 → n = 0 := by
  let p := thetaHalfPeriod τ - h i₀
  let term : ι → ℂ → ℂ := fun j =>
    constantCoeffDifferentialOperator (L j) (thetaLogDerivDefect (h j) · τ)
  have hhi₀ := thetaNonlatticeShift_of_translationNonresonant (hnonres i₀ hi₀)
  have htopOrder : meromorphicOrderAt (term i₀) p =
      ((-((L i₀).natDegree + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    apply meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hLi₀
      (meromorphicAt_thetaLogDerivDefect hτ)
    simpa [p] using meromorphicOrderAt_thetaLogDerivDefect_shifted hτ hhi₀ 0 0
  let R := s.erase i₀
  have hrestAn : AnalyticAt ℂ (∑ j ∈ R, term j) p := by
    apply Finset.analyticAt_sum
    intro j hj
    have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
    have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    simpa [p, additiveOrbitPoint] using
      analyticAt_thetaDifferentialFamilyTerm_on_distinguishedOrbit
        hτ hq hnonres hi₀ hjs hsep 0 (Or.inl hji)
  have hsplit : thetaDifferentialFamilySum s L h τ = term i₀ + ∑ j ∈ R, term j := by
    funext z
    rw [thetaDifferentialFamilySum]
    simp only [Finset.sum_apply, Pi.add_apply]
    rw [← Finset.sum_erase_add _ _ hi₀, add_comm]
  constructor
  · rw [hsplit]
    have hlt : meromorphicOrderAt (term i₀) p <
        meromorphicOrderAt (∑ j ∈ R, term j) p := by
      rw [htopOrder]
      exact lt_of_lt_of_le (by
        exact_mod_cast (show -((L i₀).natDegree + 1 : ℕ) < (0 : ℤ) by omega))
        hrestAn.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_add_eq_left_of_lt hrestAn.meromorphicAt hlt, htopOrder]
    exact_mod_cast (show -((L i₀).natDegree + 1 : ℕ) < (0 : ℤ) by omega)
  · intro n hn
    by_contra hn0
    have hallAn : AnalyticAt ℂ (thetaDifferentialFamilySum s L h τ)
        (additiveOrbitPoint p q n) := by
      rw [thetaDifferentialFamilySum]
      apply Finset.analyticAt_sum
      intro j hj
      exact analyticAt_thetaDifferentialFamilyTerm_on_distinguishedOrbit
        hτ hq hnonres hi₀ hj hsep n (Or.inr hn0)
    exact (not_lt_of_ge hallAn.meromorphicOrderAt_nonneg) hn

/-- **Simultaneous unconditional local elliptic obstruction.** A separated finite family of theta
defects with at least one nonzero differential operator is not a translation coboundary of any
globally meromorphic elliptic primitive. -/
theorem thetaDifferentialFamily_ne_ellipticShiftCoboundary
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {L : ι → Polynomial ℂ} {h : ι → ℂ} {τ q : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ∀ j ∈ s, ThetaTranslationNonresonant τ q (h j))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hLi₀ : L i₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ i₀ → ThetaTranslationNonresonant τ q (h j - h i₀))
    (g : ℂ → ℂ) (hg : MeromorphicOn g Set.univ)
    (hperiodOne : Function.Periodic g 1)
    (hperiodTau : Function.Periodic g τ) :
    ¬ ∀ z : ℂ, thetaDifferentialFamilySum s L h τ z = g (z + q) - g z := by
  intro heq
  obtain ⟨hpole, hunique⟩ := thetaDifferentialFamilySum_singleton_poleOrbit
    hτ hq hnonres hi₀ hLi₀ hsep
  apply shiftCoboundary_not_singleton_poleOrbit g (thetaDifferentialFamilySum s L h τ)
    (thetaHalfPeriod τ - h i₀) q
  · intro n
    exact hg _ (Set.mem_univ _)
  · exact heq
  · exact poleIndexSet_finite_of_elliptic hτ hg hperiodOne hperiodTau hq
  · simpa [additiveOrbitPoint] using hpole
  · exact hunique

end

end GaloisForLFunctions
