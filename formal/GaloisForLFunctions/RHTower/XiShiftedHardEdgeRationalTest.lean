import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift

/-!
# The rational hard-edge test and its Cayley angular coordinate

For a real polynomial `p` and a positive mass `a` the rational hard-edge test is

`g_{a,p}(x) = a·(a² + x²)^{-1/2}·p((a² + x²)^{-1})`.

Its square is a rational function, so it extends to the complex plane without a branch choice, and
evaluating it on the Xi divisor gives exactly the mass-scaled shifted reciprocal Hankel form:

`Σ_q g_{a,p}(α_q)² = a²·Φ_{a²}[p]`.

In the Cayley angular coordinate `x = a·tan(θ/2)` the half-density Jacobian cancels and the test
becomes `cos(θ/2)` times a real trigonometric polynomial of degree at most `deg p` in `θ`.  That is
the coordinate in which degree is an aperture and the completed source becomes a bounded prime-log
cone.
-/

open Polynomial

noncomputable section

namespace RHTower

/-! ## The rational test -/

/-- The literal rational hard-edge test attached to a mass and a real polynomial. -/
def routeUHardEdgeRationalTest (a : ℝ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  a / Real.sqrt (a ^ (2 : ℕ) + x ^ (2 : ℕ)) * p.eval ((a ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹)

/-- The square of the rational test, as a rational function of the spectral variable.  This is the
single-valued extension used on the complex Xi divisor. -/
def routeUHardEdgeRationalTestSq (a : ℝ) (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  ((a ^ (2 : ℕ) : ℝ) : ℂ) * (((a ^ (2 : ℕ) : ℝ) : ℂ) + z ^ (2 : ℕ))⁻¹ *
    evalRealPolynomial p ((((a ^ (2 : ℕ) : ℝ) : ℂ) + z ^ (2 : ℕ))⁻¹) ^ (2 : ℕ)

theorem routeUHardEdgeRationalTest_sq_eq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) (x : ℝ) :
    routeUHardEdgeRationalTest a p x ^ (2 : ℕ)
      = a ^ (2 : ℕ) * (a ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹ * p.eval ((a ^ (2 : ℕ) + x ^ (2 : ℕ))⁻¹) ^ (2 : ℕ) := by
  have hden : (0 : ℝ) < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
  have hsq : Real.sqrt (a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (2 : ℕ) = a ^ (2 : ℕ) + x ^ (2 : ℕ) := Real.sq_sqrt hden.le
  rw [routeUHardEdgeRationalTest, mul_pow, div_pow, hsq]
  field_simp

/-- On the real line the rational extension of the square is the square of the test. -/
theorem routeUHardEdgeRationalTestSq_ofReal {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) (x : ℝ) :
    routeUHardEdgeRationalTestSq a p (x : ℂ)
      = ((routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hden : (0 : ℝ) < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
  have hcast : (((a ^ (2 : ℕ) : ℝ) : ℂ) + (x : ℂ) ^ (2 : ℕ)) = (((a ^ (2 : ℕ) + x ^ (2 : ℕ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [routeUHardEdgeRationalTestSq, hcast, ← Complex.ofReal_inv,
    routeUHardEdgeRationalTest_sq_eq ha p x, evalRealPolynomial_ofReal]
  push_cast
  ring

/-! ## The divisor form -/

/-- **(CSHC.2) pointwise.**  On a Xi divisor point the squared rational test is the mass-scaled
shifted reciprocal Hankel atom. -/
theorem routeUHardEdgeRationalTestSq_xiSpectralPoint (a : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    routeUHardEdgeRationalTestSq a p (xiSpectralPoint q)
      = ((a ^ (2 : ℕ) : ℝ) : ℂ) * xiShiftedReciprocalTraceHankelTerm (a ^ (2 : ℕ)) p q := by
  have hshift := xiShiftedReciprocalSquare_eq_inv (sq_nonneg a) q
  rw [routeUHardEdgeRationalTestSq, xiShiftedReciprocalTraceHankelTerm, hshift, xiSquaredNode]
  ring

/-- **(CSHC.2) The completed divisor form of the rational hard-edge test.** -/
theorem tsum_routeUHardEdgeRationalTestSq_eq (a : ℝ) (p : Polynomial ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q))
      = ((a ^ (2 : ℕ) : ℝ) : ℂ) * xiShiftedReciprocalTraceHankel (a ^ (2 : ℕ)) p := by
  rw [xiShiftedReciprocalTraceHankel, ← tsum_mul_left]
  exact tsum_congr (routeUHardEdgeRationalTestSq_xiSpectralPoint a p)

theorem summable_routeUHardEdgeRationalTestSq_xiSpectralPoint (a : ℝ) (p : Polynomial ℝ) :
    Summable fun q : XiZeroCopy => routeUHardEdgeRationalTestSq a p (xiSpectralPoint q) := by
  refine ((summable_xiShiftedReciprocalTraceHankelTerm (sq_nonneg a) p).mul_left
    (((a ^ (2 : ℕ) : ℝ) : ℂ))).congr ?_
  intro q
  exact (routeUHardEdgeRationalTestSq_xiSpectralPoint a p q).symm

/-! ## The Cayley angular coordinate -/

/-- The angular polynomial of the rational test: a real polynomial in `cos θ`. -/
def routeUHardEdgeAngularPoly (a : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  p.comp (Polynomial.C (1 / (2 * a ^ (2 : ℕ))) * (Polynomial.X + Polynomial.C 1))

/-- The angular polynomial has degree at most that of the source polynomial: scaled degree is the
aperture. -/
theorem natDegree_routeUHardEdgeAngularPoly_le (a : ℝ) (p : Polynomial ℝ) :
    (routeUHardEdgeAngularPoly a p).natDegree ≤ p.natDegree := by
  have hlin : (Polynomial.C (1 / (2 * a ^ (2 : ℕ))) * (Polynomial.X + Polynomial.C 1) :
      Polynomial ℝ).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · simp
    · simp
  calc (routeUHardEdgeAngularPoly a p).natDegree
      ≤ p.natDegree * (Polynomial.C (1 / (2 * a ^ (2 : ℕ))) *
          (Polynomial.X + Polynomial.C 1) : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hlin
    _ = p.natDegree := Nat.mul_one _

/-- The half-angle square in terms of the full angle. -/
theorem cos_half_sq (θ : ℝ) : Real.cos (θ / 2) ^ (2 : ℕ) = (1 + Real.cos θ) / 2 := by
  have h := Real.cos_sq (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  rw [h]
  ring

/-- The angular polynomial evaluates the source polynomial at the reciprocal atom. -/
theorem routeUHardEdgeAngularPoly_eval {a : ℝ} (ha : a ≠ 0) (p : Polynomial ℝ) (θ : ℝ) :
    (routeUHardEdgeAngularPoly a p).eval (Real.cos θ)
      = p.eval (Real.cos (θ / 2) ^ (2 : ℕ) / a ^ (2 : ℕ)) := by
  rw [routeUHardEdgeAngularPoly, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, cos_half_sq]
  congr 1
  field_simp
  ring

/-- Squares of the tangent and the cosine on the principal branch. -/
theorem tan_sq_add_one_of_cos_ne_zero {u : ℝ} (hu : Real.cos u ≠ 0) :
    Real.tan u ^ (2 : ℕ) + 1 = 1 / Real.cos u ^ (2 : ℕ) := by
  rw [Real.tan_eq_sin_div_cos, div_pow]
  field_simp
  have := Real.sin_sq_add_cos_sq u
  linarith

/-- **(CSHC.16) The Cayley angular form of the rational test.**  In the coordinate
`x = a·tan(θ/2)` the test is `cos(θ/2)` times a real trigonometric polynomial. -/
theorem routeUHardEdgeRationalTest_tan {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {θ : ℝ}
    (hθ : Real.cos (θ / 2) > 0) :
    routeUHardEdgeRationalTest a p (a * Real.tan (θ / 2))
      = Real.cos (θ / 2) * (routeUHardEdgeAngularPoly a p).eval (Real.cos θ) := by
  have hcne : Real.cos (θ / 2) ≠ 0 := ne_of_gt hθ
  have hsum : a ^ (2 : ℕ) + (a * Real.tan (θ / 2)) ^ (2 : ℕ) = a ^ (2 : ℕ) / Real.cos (θ / 2) ^ (2 : ℕ) := by
    have h := tan_sq_add_one_of_cos_ne_zero hcne
    calc a ^ (2 : ℕ) + (a * Real.tan (θ / 2)) ^ (2 : ℕ) = a ^ (2 : ℕ) * (Real.tan (θ / 2) ^ (2 : ℕ) + 1) := by ring
      _ = a ^ (2 : ℕ) * (1 / Real.cos (θ / 2) ^ (2 : ℕ)) := by rw [h]
      _ = a ^ (2 : ℕ) / Real.cos (θ / 2) ^ (2 : ℕ) := by ring
  have hsqrt : Real.sqrt (a ^ (2 : ℕ) + (a * Real.tan (θ / 2)) ^ (2 : ℕ)) = a / Real.cos (θ / 2) := by
    rw [hsum]
    rw [show a ^ (2 : ℕ) / Real.cos (θ / 2) ^ (2 : ℕ) = (a / Real.cos (θ / 2)) ^ (2 : ℕ) by
      rw [div_pow]]
    exact Real.sqrt_sq (by positivity)
  rw [routeUHardEdgeRationalTest, hsqrt, hsum, routeUHardEdgeAngularPoly_eval (ne_of_gt ha) p θ]
  have hfactor : a / (a / Real.cos (θ / 2)) = Real.cos (θ / 2) := by
    field_simp
  rw [hfactor]
  congr 2
  field_simp

end RHTower

end
