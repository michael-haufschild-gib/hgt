import GaloisForLFunctions.RHTower.XiResolventSingleMinorCriterion

/-!
# RH as the Cauchy–Schwarz inequality of the resolvent trace functional

Let `L p = sum_q u_q * p (u_q)` be the resolvent trace functional on real polynomials at a
shift `X`.  On the critical line the atoms `u_q` are positive reals, so `L` is integration
against a positive discrete measure and satisfies the Cauchy–Schwarz inequality
`L(f^2) L(g^2) ≥ L(fg)^2` by the Lagrange pair identity.  Conversely the special pairs
`(f, X f)` recover exactly the index-`0` polynomial Turán minors, which alone drive the
spectral descent.

**Theorem**: at any one shift `X ≥ 0`,

`RH  ↔  ∀ f g : Polynomial ℝ, 0 ≤ Re (L (f*f) * L (g*g) - L (f*g)^2)`

— the Riemann hypothesis is the Cauchy–Schwarz inequality of one explicit arithmetic
functional.  The criterion is sign-blind: negating `L` preserves every inequality on the
right, so the mechanism locating the zeros is oscillation along the descent, not the
positivity of a measure.
-/

open Complex

namespace RHTower

noncomputable section

/-- The resolvent trace functional on real polynomials: `L p = sum_q u_q * p (u_q)`. -/
def xiPolyFunctional (p : Polynomial ℝ) (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q)

/-- Norm-summability of the functional atoms. -/
theorem summable_norm_polyFunctionalAtom {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy =>
      ‖xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q)‖) := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((summable_norm_xiResolventPoint hX).mul_right (evalRealPolynomialNormBound p 1))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_evalRealPolynomial_le p (norm_xiResolventPoint_le_one hX q)) (norm_nonneg _)

/-- `L (p * p)` is the zeroth `p`-weighted moment. -/
theorem xiPolyFunctional_mul_self (p : Polynomial ℝ) (X : ℝ) :
    xiPolyFunctional (p * p) X = xiPolyMoment p 0 X := by
  rw [show xiPolyFunctional (p * p) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q * evalRealPolynomial (p * p) (xiResolventPoint X q) from rfl,
    show xiPolyMoment p 0 X = ∑' q : XiZeroCopy, xiResolventPoint X q ^ (0 + 1) *
      evalRealPolynomial p (xiResolventPoint X q) ^ 2 from rfl]
  refine tsum_congr fun q => ?_
  rw [evalRealPolynomial_mul]
  ring

/-- `L ((X p) * (X p))` is the second `p`-weighted moment. -/
theorem xiPolyFunctional_X_mul_self (p : Polynomial ℝ) (X : ℝ) :
    xiPolyFunctional ((Polynomial.X * p) * (Polynomial.X * p)) X = xiPolyMoment p 2 X := by
  rw [show xiPolyFunctional ((Polynomial.X * p) * (Polynomial.X * p)) X =
      ∑' q : XiZeroCopy, xiResolventPoint X q *
        evalRealPolynomial ((Polynomial.X * p) * (Polynomial.X * p))
          (xiResolventPoint X q) from rfl,
    show xiPolyMoment p 2 X = ∑' q : XiZeroCopy, xiResolventPoint X q ^ (2 + 1) *
      evalRealPolynomial p (xiResolventPoint X q) ^ 2 from rfl]
  refine tsum_congr fun q => ?_
  simp only [evalRealPolynomial_mul, evalRealPolynomial_X]
  ring

/-- `L (p * (X p))` is the first `p`-weighted moment. -/
theorem xiPolyFunctional_mul_X_mul (p : Polynomial ℝ) (X : ℝ) :
    xiPolyFunctional (p * (Polynomial.X * p)) X = xiPolyMoment p 1 X := by
  rw [show xiPolyFunctional (p * (Polynomial.X * p)) X =
      ∑' q : XiZeroCopy, xiResolventPoint X q *
        evalRealPolynomial (p * (Polynomial.X * p)) (xiResolventPoint X q) from rfl,
    show xiPolyMoment p 1 X = ∑' q : XiZeroCopy, xiResolventPoint X q ^ (1 + 1) *
      evalRealPolynomial p (xiResolventPoint X q) ^ 2 from rfl]
  refine tsum_congr fun q => ?_
  simp only [evalRealPolynomial_mul, evalRealPolynomial_X]
  ring

/-- **The Lagrange pair identity** for the Cauchy–Schwarz defect of the trace functional. -/
theorem two_mul_polyCauchySchwarz_eq_tsum_pair {X : ℝ} (hX : 0 ≤ X)
    (f g : Polynomial ℝ) :
    2 * (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
      xiPolyFunctional (f * g) X ^ 2) =
    ∑' z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1 * xiResolventPoint X z.2) *
        (evalRealPolynomial f (xiResolventPoint X z.1) *
            evalRealPolynomial g (xiResolventPoint X z.2) -
          evalRealPolynomial f (xiResolventPoint X z.2) *
            evalRealPolynomial g (xiResolventPoint X z.1)) ^ 2 := by
  have hff := summable_norm_polyFunctionalAtom hX (f * f)
  have hgg := summable_norm_polyFunctionalAtom hX (g * g)
  have hfg := summable_norm_polyFunctionalAtom hX (f * g)
  have hA := tsum_mul_tsum_of_summable_norm hff hgg
  have hB := tsum_mul_tsum_of_summable_norm hfg hfg
  have hC := tsum_mul_tsum_of_summable_norm hgg hff
  have hsumA := summable_mul_of_summable_norm hff hgg
  have hsumB := summable_mul_of_summable_norm hfg hfg
  have hsumC := summable_mul_of_summable_norm hgg hff
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy,
      (xiResolventPoint X z.1 * xiResolventPoint X z.2) *
        (evalRealPolynomial f (xiResolventPoint X z.1) *
            evalRealPolynomial g (xiResolventPoint X z.2) -
          evalRealPolynomial f (xiResolventPoint X z.2) *
            evalRealPolynomial g (xiResolventPoint X z.1)) ^ 2 =
      (((xiResolventPoint X z.1 *
          evalRealPolynomial (f * f) (xiResolventPoint X z.1)) *
          (xiResolventPoint X z.2 *
            evalRealPolynomial (g * g) (xiResolventPoint X z.2)) -
        2 * ((xiResolventPoint X z.1 *
            evalRealPolynomial (f * g) (xiResolventPoint X z.1)) *
          (xiResolventPoint X z.2 *
            evalRealPolynomial (f * g) (xiResolventPoint X z.2)))) +
        (xiResolventPoint X z.1 *
          evalRealPolynomial (g * g) (xiResolventPoint X z.1)) *
          (xiResolventPoint X z.2 *
            evalRealPolynomial (f * f) (xiResolventPoint X z.2))) := by
    intro z
    simp only [evalRealPolynomial_mul]
    ring
  rw [show xiPolyFunctional (f * f) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q * evalRealPolynomial (f * f) (xiResolventPoint X q) from rfl,
    show xiPolyFunctional (g * g) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q * evalRealPolynomial (g * g) (xiResolventPoint X q) from rfl,
    show xiPolyFunctional (f * g) X = ∑' q : XiZeroCopy,
      xiResolventPoint X q * evalRealPolynomial (f * g) (xiResolventPoint X q) from rfl,
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

/-- **Under RH the trace functional satisfies Cauchy–Schwarz**: the Lagrange pair expansion
is a sum of nonnegative reals. -/
theorem polyCauchySchwarz_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 ≤ X) (f g : Polynomial ℝ) :
    0 ≤ (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
      xiPolyFunctional (f * g) X ^ 2).re := by
  have hhalf : (0 : ℝ) ≤ (2 * (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
      xiPolyFunctional (f * g) X ^ 2)).re := by
    rw [two_mul_polyCauchySchwarz_eq_tsum_pair hX f g]
    have hterm : ∀ z : XiZeroCopy × XiZeroCopy, ∃ w : ℝ, 0 ≤ w ∧
        (xiResolventPoint X z.1 * xiResolventPoint X z.2) *
          (evalRealPolynomial f (xiResolventPoint X z.1) *
              evalRealPolynomial g (xiResolventPoint X z.2) -
            evalRealPolynomial f (xiResolventPoint X z.2) *
              evalRealPolynomial g (xiResolventPoint X z.1)) ^ 2 = (w : ℂ) := by
      intro z
      obtain ⟨v₁, hv₁, he₁⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.1
      obtain ⟨v₂, hv₂, he₂⟩ := exists_pos_ofReal_xiResolventPoint_of_rh hRH hX z.2
      refine ⟨(v₁ * v₂) * (Polynomial.eval v₁ f * Polynomial.eval v₂ g -
        Polynomial.eval v₂ f * Polynomial.eval v₁ g) ^ 2, by positivity, ?_⟩
      rw [he₁, he₂]
      simp only [evalRealPolynomial_ofReal]
      push_cast
      ring
    choose w hw hweq using hterm
    rw [tsum_congr hweq]
    by_cases hsum : Summable (fun z : XiZeroCopy × XiZeroCopy => ((w z : ℝ) : ℂ))
    · rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun z => by simpa using hw z
    · rw [tsum_eq_zero_of_not_summable hsum]
      simp
  have h2 : (2 * (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
      xiPolyFunctional (f * g) X ^ 2)).re =
      2 * (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
        xiPolyFunctional (f * g) X ^ 2).re := by
    simp [Complex.mul_re]
  rw [h2] at hhalf
  linarith

/-- The Cauchy–Schwarz inequalities of the trace functional prove RH: the pairs `(f, X f)`
recover the index-`0` polynomial Turán minors. -/
theorem riemannHypothesis_of_forall_polyCauchySchwarz {X : ℝ} (hX : 0 ≤ X)
    (hcs : ∀ f g : Polynomial ℝ,
      0 ≤ (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
        xiPolyFunctional (f * g) X ^ 2).re) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_polyTuranMinor_zero_re_nonneg hX fun p => ?_
  have h := hcs p (Polynomial.X * p)
  rw [xiPolyFunctional_mul_self, xiPolyFunctional_X_mul_self,
    xiPolyFunctional_mul_X_mul] at h
  exact h

/-- **RH is the Cauchy–Schwarz inequality of the resolvent trace functional**: at any one
shift, the Riemann hypothesis is equivalent to
`Re (L (f*f) * L (g*g) - L (f*g)^2) ≥ 0` for all real polynomials `f, g`, where
`L p = sum_q u_q * p (u_q)`. -/
theorem riemannHypothesis_iff_forall_polyCauchySchwarz {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔ ∀ f g : Polynomial ℝ,
      0 ≤ (xiPolyFunctional (f * f) X * xiPolyFunctional (g * g) X -
        xiPolyFunctional (f * g) X ^ 2).re :=
  ⟨fun hRH f g => polyCauchySchwarz_re_nonneg_of_riemannHypothesis hRH hX f g,
    riemannHypothesis_of_forall_polyCauchySchwarz hX⟩

end

end RHTower
