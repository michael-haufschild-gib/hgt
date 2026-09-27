import GaloisForLFunctions.RHTower.CCMPrimeFrustratedTriangle

/-!
# Continuous phase frustration for actual arithmetic sources

The sum of the cosine and sine source energies is an exact three-angle
potential. It is invariant under a common continuous phase translation. The
constructed prime triangles have a strict gap above the sum of independent
edge minima, uniformly over every triple of angles.
-/

noncomputable section

namespace RHTower

def ccmWeilTrianglePhaseEnergy (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a
    ((Real.cos alpha : ℂ) • u + (Real.cos beta : ℂ) • v + (Real.cos gamma : ℂ) • w) +
  ccmRestrictedWeilSourceQuadratic a
    ((Real.sin alpha : ℂ) • u + (Real.sin beta : ℂ) • v + (Real.sin gamma : ℂ) • w)

theorem ccmWeilTrianglePhaseEnergy_eq (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    ccmWeilTrianglePhaseEnergy a u v w alpha beta gamma =
      ccmRestrictedWeilSourceQuadratic a u + ccmRestrictedWeilSourceQuadratic a v +
      ccmRestrictedWeilSourceQuadratic a w +
      2 * ccmWeilRealPolar a u v * Real.cos (alpha - beta) +
      2 * ccmWeilRealPolar a u w * Real.cos (alpha - gamma) +
      2 * ccmWeilRealPolar a v w * Real.cos (beta - gamma) := by
  unfold ccmWeilTrianglePhaseEnergy
  rw [ccmRestrictedWeilSourceQuadratic_real_three, ccmRestrictedWeilSourceQuadratic_real_three]
  simp only [Real.cos_sub]
  linear_combination
    ccmRestrictedWeilSourceQuadratic a u * Real.sin_sq_add_cos_sq alpha +
    ccmRestrictedWeilSourceQuadratic a v * Real.sin_sq_add_cos_sq beta +
    ccmRestrictedWeilSourceQuadratic a w * Real.sin_sq_add_cos_sq gamma

/-- The potential has the diagonal continuous phase symmetry. -/
theorem ccmWeilTrianglePhaseEnergy_common_shift (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma t : ℝ) :
    ccmWeilTrianglePhaseEnergy a u v w (alpha + t) (beta + t) (gamma + t) =
      ccmWeilTrianglePhaseEnergy a u v w alpha beta gamma := by
  simp only [ccmWeilTrianglePhaseEnergy_eq, add_sub_add_right_eq_sub]

def ccmWeilTrianglePhaseFloor (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a u + ccmRestrictedWeilSourceQuadratic a v +
    ccmRestrictedWeilSourceQuadratic a w -
    2 * (|ccmWeilRealPolar a u v| + |ccmWeilRealPolar a u w| + |ccmWeilRealPolar a v w|)

theorem ccmWeilTriangleSeparateLower_cos_sin (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (alpha beta gamma : ℝ) :
    ccmWeilTriangleSeparateLower a u v w (Real.cos alpha) (Real.cos beta) (Real.cos gamma) +
      ccmWeilTriangleSeparateLower a u v w (Real.sin alpha) (Real.sin beta) (Real.sin gamma) =
      ccmWeilTrianglePhaseFloor a u v w := by
  unfold ccmWeilTriangleSeparateLower ccmWeilTrianglePhaseFloor
  linear_combination
    (ccmRestrictedWeilSourceQuadratic a u - |ccmWeilRealPolar a u v| - |ccmWeilRealPolar a u w|) *
      Real.sin_sq_add_cos_sq alpha +
    (ccmRestrictedWeilSourceQuadratic a v - |ccmWeilRealPolar a u v| - |ccmWeilRealPolar a v w|) *
      Real.sin_sq_add_cos_sq beta +
    (ccmRestrictedWeilSourceQuadratic a w - |ccmWeilRealPolar a u w| - |ccmWeilRealPolar a v w|) *
      Real.sin_sq_add_cos_sq gamma

theorem ccmWeilTrianglePhaseEnergy_gap_of_real_lower (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) (m : ℝ)
    (h : ∀ x y z : ℝ, ccmWeilTriangleSeparateLower a u v w x y z +
      m * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      ccmRestrictedWeilSourceQuadratic a ((x : ℂ) • u + (y : ℂ) • v + (z : ℂ) • w))
    (alpha beta gamma : ℝ) :
    ccmWeilTrianglePhaseFloor a u v w + 3 * m ≤
      ccmWeilTrianglePhaseEnergy a u v w alpha beta gamma := by
  have hc := h (Real.cos alpha) (Real.cos beta) (Real.cos gamma)
  have hs := h (Real.sin alpha) (Real.sin beta) (Real.sin gamma)
  have hsum := ccmWeilTriangleSeparateLower_cos_sin a u v w alpha beta gamma
  have hmass : m * (Real.cos alpha ^ 2 + Real.cos beta ^ 2 + Real.cos gamma ^ 2) +
      m * (Real.sin alpha ^ 2 + Real.sin beta ^ 2 + Real.sin gamma ^ 2) = 3 * m := by
    linear_combination m * Real.sin_sq_add_cos_sq alpha + m * Real.sin_sq_add_cos_sq beta +
      m * Real.sin_sq_add_cos_sq gamma
  unfold ccmWeilTrianglePhaseEnergy
  linarith only [hc, hs, hsum, hmass]

/-- A uniform continuous-phase gap, with all source geometry and arithmetic signs constructed. -/
theorem exists_cofinal_ccmPrime_frustrated_phase_gap (N : ℕ) :
    ∃ (p q : ℕ) (r m : ℝ) (a : SuzukiPositiveAperture)
      (u v w : CCMComplexSmoothInteriorSource a),
      N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ 2 * p < q ∧ 0 < r ∧ 0 < m ∧
      Function.support u = Metric.ball 0 r ∧
      Function.support v = Metric.ball (Real.log p) r ∧
      Function.support w = Metric.ball (Real.log q) r ∧
      ∀ alpha beta gamma : ℝ,
        ccmWeilTrianglePhaseFloor a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector + 3 * m ≤
          ccmWeilTrianglePhaseEnergy a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector
            alpha beta gamma := by
  obtain ⟨p, q, r, m, a, u, v, w, hpN, hp, hq, hpq, hr, hm, hus, hvs, hws, _, _, _, h⟩ :=
    exists_cofinal_ccmPrime_frustrated_triangle N
  exact ⟨p, q, r, m, a, u, v, w, hpN, hp, hq, hpq, hr, hm, hus, hvs, hws,
    ccmWeilTrianglePhaseEnergy_gap_of_real_lower a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector m h⟩

end RHTower
