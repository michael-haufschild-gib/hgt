import GaloisForLFunctions.HTGeometry.GammaMonomialNotRational

/-!
# Two distinct Gamma monomials are not proportional over the rational functions

This is the statement `archimedean-relative-prime-cocycle-curvature` names as the one the leading
shape cannot supply: `Γ(s+α)Γ(s+β)` and `Γ(s+α+β)Γ(s)` share their degree, their weighted shift and
their leading constant, so nothing about the leading datum separates them.  Their *ratio* is a
nontrivial Gamma monomial, and a nontrivial Gamma monomial is not rational.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The Gamma monomial of a difference of exponent vectors is the ratio of the monomials. -/
theorem gammaMonomial_sub {r : ℕ} (lam : Fin r → ℂ) (e f : Fin r → ℤ) {s : ℂ}
    (hne : ∀ k, Complex.Gamma (s + lam k) ≠ 0) :
    gammaMonomial lam (fun k => e k - f k) s
      = gammaMonomial lam e s / gammaMonomial lam f s := by
  rw [gammaMonomial, gammaMonomial, gammaMonomial, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_sub₀ (hne k) _ _

theorem gamma_ne_zero_of_gt_sum_abs {r : ℕ} (lam : Fin r → ℂ) {s : ℂ}
    (hs : (∑ j, |(lam j).re|) < s.re) (k : Fin r) : Complex.Gamma (s + lam k) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have h1 : (s + lam k).re = -(m : ℝ) := by rw [hcon]; simp
  have h2 := re_pos_of_gt_sum_abs lam hs k
  have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [h1] at h2
  linarith

/-- **Two distinct Gamma monomials are not proportional over the rational function field.** -/
theorem not_rational_gammaMonomial_ratio {r : ℕ} (lam : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (e f : Fin r → ℤ) (k₀ : Fin r) (hne : e k₀ ≠ f k₀)
    (P Q : Polynomial ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re →
      gammaMonomial lam e s / gammaMonomial lam f s
        = Polynomial.eval s P / Polynomial.eval s Q) :
    False := by
  refine not_rational_gammaMonomial lam hincong (fun k => e k - f k) k₀ (by omega) P Q hP hQ ?_
  intro s hs
  rw [gammaMonomial_sub lam e f (gamma_ne_zero_of_gt_sum_abs lam hs)]
  exact h s hs

end

end GaloisForLFunctions.HTGeometry
