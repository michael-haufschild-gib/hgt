import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import GaloisForLFunctions.HTGeometry.OscillatorSolutionSpaceRank
import GaloisForLFunctions.HTGeometry.OscillatorSpectralRigidity

/-!
# Even square-integrable solutions of the oscillator equation

The rigidity statement the constrained-prolate cards name as their missing classical input:

`if v ∈ L²(ℝ) is even and solves v″ = (ξ²−μ)v on all of ℝ, then μ = 2n+1 with n even, and v is a
multiple of the corresponding Hermite function.`

Rigidity puts `μ` on the ladder; one-dimensionality of the square-integrable solution space makes
`v` proportional to the Hermite function at that rung; and the Hermite function at an odd rung is
odd, so it could not be proportional to an even solution that does not vanish at the origin.
-/

open Set MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

/-- For odd index the Hermite polynomial is an odd function. -/
theorem aeval_hermite_neg_of_odd {n : ℕ} (hn : Odd n) (x : ℝ) :
    Polynomial.aeval (-x) (Polynomial.hermite n) = -Polynomial.aeval x (Polynomial.hermite n) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with hke | hko
  · have hz : (Polynomial.hermite n).coeff k = 0 :=
      Polynomial.coeff_hermite_of_odd_add (hn.add_even hke)
    rw [hz]
    simp
  · rw [hko.neg_pow]
    ring

/-- The Hermite function of odd index is odd. -/
theorem odd_hermiteFun {n : ℕ} (hn : Odd n) (x : ℝ) : hermiteFun n (-x) = -hermiteFun n x := by
  have hp : Polynomial.aeval (Real.sqrt 2 * -x) (Polynomial.hermite n)
      = -Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n) := by
    have hrw : Real.sqrt 2 * -x = -(Real.sqrt 2 * x) := by ring
    rw [hrw]
    exact aeval_hermite_neg_of_odd hn _
  show probHermiteFun n (Real.sqrt 2 * -x) = -probHermiteFun n (Real.sqrt 2 * x)
  rw [probHermiteFun, probHermiteFun, hp]
  have hsq : (Real.sqrt 2 * -x) ^ 2 = (Real.sqrt 2 * x) ^ 2 := by ring
  rw [hsq]
  ring

/-- The Hermite function is square integrable. -/
theorem integrable_hermiteFun_sq (n : ℕ) : Integrable fun x => hermiteFun n x ^ 2 := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  have h := integrable_polyEval_mul_gauss (p * p) (by norm_num : (0 : ℝ) < 1)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show Polynomial.eval x (p * p) * Real.exp (-(1 * x ^ 2)) = hermiteFun n x ^ 2
  rw [hp x, Polynomial.eval_mul,
    show Real.exp (-(1 * x ^ 2))
      = Real.exp (-(1 / 2 * x ^ 2)) * Real.exp (-(1 / 2 * x ^ 2)) by
      rw [← Real.exp_add]; congr 1; ring]
  ring

/-- The Hermite function never degenerates: its value and derivative do not vanish together. -/
theorem hermiteFun_nontrivial (n : ℕ) (y : ℝ) :
    hermiteFun n y ≠ 0 ∨ deriv (hermiteFun n) y ≠ 0 := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hP : Continuous fun x : ℝ => x ^ 2 - (2 * (n : ℝ) + 1) :=
    (continuous_pow 2).sub continuous_const
  have hzero : hermiteFun n = fun _ : ℝ => (0 : ℝ) := by
    refine secondOrder_eq_at hP y (hasDerivAt_hermiteFun n) ?_
      (fun x => hasDerivAt_const x (0 : ℝ))
      (fun x => (hasDerivAt_const x (0 : ℝ)).congr_deriv (by ring)) h1 ?_
    · intro x
      have h := hasDerivAt_deriv_hermiteFun n x
      rw [hermiteRungP] at h
      exact h
    · simpa using h2
  obtain ⟨z, -, hz⟩ := exists_hermiteFun_ne_zero n (by norm_num : (-1 : ℝ) < 1)
  exact hz (congrFun hzero z)

/-- **Even oscillator rigidity.**  An even square-integrable solution sits at an even rung and is a
multiple of the Hermite function there. -/
theorem even_integrable_solution_rung {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hnt : ∀ y, v y ≠ 0 ∨ v' y ≠ 0) (hint : Integrable fun x => v x ^ 2)
    (heven : Function.Even v) (heven' : ∀ x, v' (-x) = -v' x) :
    ∃ n : ℕ, Even n ∧ mu = 2 * (n : ℝ) + 1 ∧
      hermiteFun n = fun x => (hermiteFun n 0 / v 0) * v x := by
  obtain ⟨n, hn⟩ := exists_rung_of_integrable hv hv' hnt hint
  -- the even solution does not vanish at the origin
  have hv0 : v 0 ≠ 0 := by
    intro h0
    have h0' : v' 0 = 0 := by
      have := heven' 0
      simp only [neg_zero] at this
      linarith
    rcases hnt 0 with h | h
    · exact h h0
    · exact h h0'
  -- the Hermite function at the same rung
  have hmu : mu = 2 * (n : ℝ) + 1 := hn
  have hHeq : ∀ x, HasDerivAt (deriv (hermiteFun n)) ((x ^ 2 - mu) * hermiteFun n x) x := by
    intro x
    have h := hasDerivAt_deriv_hermiteFun n x
    rw [hermiteRungP, ← hmu] at h
    exact h
  have hproportional : hermiteFun n = fun x => (hermiteFun n 0 / v 0) * v x := by
    refine eq_smul_of_integrable (a := max 1 (|mu| + 1)) ?_ ?_ hv hv' hnt hint
      (hasDerivAt_hermiteFun n) hHeq (hermiteFun_nontrivial n) (integrable_hermiteFun_sq n) hv0
    · exact lt_of_lt_of_le one_pos (le_max_left _ _)
    · have h1 : |mu| + 1 ≤ max 1 (|mu| + 1) := le_max_right _ _
      have h2 : mu ≤ |mu| := le_abs_self mu
      have h3 : (1 : ℝ) ≤ max 1 (|mu| + 1) := le_max_left _ _
      nlinarith
  refine ⟨n, ?_, hmu, hproportional⟩
  -- the rung is even
  rcases Nat.even_or_odd n with hne | hno
  · exact hne
  · exfalso
    have hzero : hermiteFun n = fun _ : ℝ => (0 : ℝ) := by
      funext x
      have hoddH := odd_hermiteFun hno x
      have hx := congrFun hproportional x
      have hnx := congrFun hproportional (-x)
      rw [heven x] at hnx
      rw [hoddH, hx] at hnx
      linarith
    obtain ⟨z, -, hz⟩ := exists_hermiteFun_ne_zero n (by norm_num : (-1 : ℝ) < 1)
    exact hz (congrFun hzero z)

end RHTower
