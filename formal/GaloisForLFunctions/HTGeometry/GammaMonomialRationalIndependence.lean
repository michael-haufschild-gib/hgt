import GaloisForLFunctions.HTGeometry.GammaMonomialLinearIndependence

/-!
# Linear independence with rational coefficients

The coefficients of a normal-form element of a shifted Gamma field are rational, not polynomial.
Clearing denominators reduces to the polynomial case, at the cost of moving the half plane far
enough to the right that no denominator vanishes on it — which is possible because a nonzero
polynomial has finitely many roots.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- A nonzero polynomial is nonvanishing on a sufficiently far right half plane. -/
theorem exists_threshold_above_roots (p : Polynomial ℂ) (hp : p ≠ 0) (R : ℝ) :
    ∃ Rb : ℝ, R ≤ Rb ∧ ∀ s : ℂ, Rb < s.re → Polynomial.eval s p ≠ 0 := by
  classical
  have hfin : {x : ℂ | p.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hp
  have himg : (Complex.re '' {x : ℂ | p.IsRoot x}).Finite := hfin.image _
  obtain ⟨M, hM⟩ := himg.bddAbove
  refine ⟨max R M, le_max_left _ _, fun s hs hcon => ?_⟩
  have hmem : s.re ∈ Complex.re '' {x : ℂ | p.IsRoot x} := ⟨s, hcon, rfl⟩
  have hle : s.re ≤ M := hM hmem
  have : M < s.re := lt_of_le_of_lt (le_max_right R M) hs
  linarith

/-- **Linear independence of Gamma monomials over the rational functions.** -/
theorem gammaMonomial_linearIndependent_rat {r : ℕ} {ι : Type*} [DecidableEq ι] (lam : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (T : Finset ι) (e : ι → Fin r → ℤ)
    (hdist : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → e α ≠ e β)
    (Pn Qn : ι → Polynomial ℂ) (hQ : ∀ α ∈ T, Qn α ≠ 0)
    (hid : ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re →
      ∑ α ∈ T, (Polynomial.eval s (Pn α) / Polynomial.eval s (Qn α))
        * gammaMonomial lam (e α) s = 0) :
    ∀ α ∈ T, Pn α = 0 := by
  classical
  set QQ : Polynomial ℂ := ∏ β ∈ T, Qn β with hQQ
  have hQQne : QQ ≠ 0 := Finset.prod_ne_zero_iff.mpr hQ
  obtain ⟨Rb, hRbge, hRb⟩ := exists_threshold_above_roots QQ hQQne (∑ j, |(lam j).re|)
  set Rc : ι → Polynomial ℂ := fun α => Pn α * ∏ β ∈ T.erase α, Qn β with hRc
  have hkey : ∀ α ∈ T, Rc α = 0 := by
    refine gammaMonomial_linearIndependent_of_threshold lam hincong Rb hRbge T.card T le_rfl e
      hdist Rc ?_
    intro s hs
    have hQQs : Polynomial.eval s QQ ≠ 0 := hRb s hs
    have hQs : ∀ β ∈ T, Polynomial.eval s (Qn β) ≠ 0 := by
      intro β hβ
      intro hcon
      refine hQQs ?_
      rw [hQQ, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hβ hcon
    have hterm : ∀ α ∈ T, Polynomial.eval s (Rc α) * gammaMonomial lam (e α) s
        = Polynomial.eval s QQ *
          ((Polynomial.eval s (Pn α) / Polynomial.eval s (Qn α)) * gammaMonomial lam (e α) s) := by
      intro α hα
      have hQα : Polynomial.eval s (Qn α) ≠ 0 := hQs α hα
      have hsplit : Polynomial.eval s QQ
          = Polynomial.eval s (Qn α) * ∏ β ∈ T.erase α, Polynomial.eval s (Qn β) := by
        rw [hQQ, Polynomial.eval_prod]
        exact (Finset.mul_prod_erase T (fun β => Polynomial.eval s (Qn β)) hα).symm
      rw [hRc]
      simp only [Polynomial.eval_mul, Polynomial.eval_prod, hsplit]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      hid s (lt_of_le_of_lt hRbge hs), mul_zero]
  intro α hα
  have h := hkey α hα
  rw [hRc] at h
  simp only [] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · exact absurd h1 (Finset.prod_ne_zero_iff.mpr fun β hβ => hQ β (Finset.mem_of_mem_erase hβ))

end

end GaloisForLFunctions.HTGeometry
