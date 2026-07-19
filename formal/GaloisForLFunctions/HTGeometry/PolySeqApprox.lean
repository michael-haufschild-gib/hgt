import GaloisForLFunctions.HTGeometry.WeierstrassApprox

/-!
# Weierstrass as a uniformly convergent sequence

Taking `ε = 1/(n+1)` in the pointwise approximation turns it into a sequence of polynomials
converging uniformly on the interval.

The statement is phrased for a function `g : ℝ → ℝ` continuous *on* the interval rather than for a
`ContinuousMap` on the subtype, so that it matches the shape
`tendsto_integral_of_tendstoUniformlyOn` consumes; the subtype appears only inside the proof, where
`ContinuousOn.restrict` produces the bundled map that Weierstrass needs.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

/-- **Weierstrass, as a sequence.** -/
theorem exists_poly_seq_tendstoUniformlyOn {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) :
    ∃ P : ℕ → Polynomial ℝ,
      TendstoUniformlyOn (fun n x => (P n).eval x) g atTop (Set.Icc a b) := by
  classical
  set F : C(Set.Icc a b, ℝ) := ⟨Set.restrict _ g, hg.restrict⟩ with hF
  have hex : ∀ n : ℕ, ∃ p : Polynomial ℝ,
      ∀ x : Set.Icc a b, |F x - p.eval (x : ℝ)| < 1 / (n + 1) := by
    intro n
    exact exists_poly_approx F (by positivity)
  choose P hP using hex
  refine ⟨P, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt heps
  refine eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
  have h1 := hP n ⟨x, hx⟩
  have hmono : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.succ_le_succ hn
  rw [Real.dist_eq]
  have hFx : F ⟨x, hx⟩ = g x := rfl
  rw [hFx] at h1
  calc |g x - (P n).eval x| < 1 / (n + 1) := h1
    _ ≤ 1 / (N + 1) := hmono
    _ < eps := hN

end HTGeometry
