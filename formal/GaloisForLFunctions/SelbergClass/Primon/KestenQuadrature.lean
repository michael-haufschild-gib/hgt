import GaloisForLFunctions.SelbergClass.Primon.KestenJacobiMoments
import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature

/-!
# Positive quadrature for the prime phase law

The phase moment form has coordinate multiplication bounded by two. Together
with orthogonality this places every Gauss node strictly inside `(-2, 2)`.
The nodes are distinct, their Christoffel weights are positive and sum to one,
and polynomial division gives an exact quadrature remainder at every degree.
The first missed monomial has error `1 + p⁻¹`, independently of the number of nodes.
-/

open MeasureTheory Set Polynomial HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem integrable_kestenPolynomialObservable (p : Nat.Primes) (Q : Polynomial ℝ) :
    IntegrableOn (fun t => kestenMcKayDensity p t * Q.eval (2 * Real.cos (Real.pi * t)))
      (Ioo (0 : ℝ) 1) :=
  ((continuous_kestenMcKayDensity p).mul (by fun_prop)).continuousOn.integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

/-- Multiplication by the normalized Hecke coordinate has norm at most two on polynomials. -/
theorem kestenMoment_mulX_sq_le (p : Nat.Primes) (Q : Polynomial ℝ) :
    momentInner (kestenMoment p) (X * Q) (X * Q) ≤
      4 * momentInner (kestenMoment p) Q Q := by
  simp only [momentInner_def, momentFunctional_kestenMoment]
  rw [← integral_const_mul]
  apply integral_mono (integrable_kestenPolynomialObservable p ((X * Q) * (X * Q)))
    ((integrable_kestenPolynomialObservable p (Q * Q)).const_mul 4)
  intro t
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hc : (2 * Real.cos (Real.pi * t)) ^ 2 ≤ 4 := by
    nlinarith only [Real.sin_sq_add_cos_sq (Real.pi * t), sq_nonneg (Real.sin (Real.pi * t))]
  have hw := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (kestenMcKayDensity_nonneg p t)
      (sq_nonneg (Q.eval (2 * Real.cos (Real.pi * t)))))
  nlinarith only [hw]

/-- Every positive-degree prime orthogonal polynomial splits over the reals. -/
theorem kestenPolynomial_splits (p : Nat.Primes) (n : ℕ) :
    (kestenPolynomial p (n + 1)).Splits := by
  rw [← monicOrtho_kestenMoment]
  exact monicOrtho_splits (kestenMoment_positiveMomentForm p) n

/-- All roots of the prime orthogonal polynomials are simple. -/
theorem kestenPolynomial_roots_nodup (p : Nat.Primes) (n : ℕ) :
    (kestenPolynomial p (n + 1)).roots.Nodup := by
  rw [← monicOrtho_kestenMoment]
  exact monicOrtho_roots_nodup (kestenMoment_positiveMomentForm p) n

/-- The level-`n` prime quadrature has exactly `n+1` nodes. -/
theorem kestenGaussNodes_card (p : Nat.Primes) (n : ℕ) :
    (gaussNodes (kestenMoment p) n).card = n + 1 :=
  gaussNodes_card (kestenMoment_positiveMomentForm p) n

/-- Every prime quadrature node is strictly inside the normalized Hecke interval. -/
theorem kestenGaussNodes_subset (p : Nat.Primes) (n : ℕ) :
    (gaussNodes (kestenMoment p) n : Set ℝ) ⊆ Ioo (-2) 2 := by
  intro r hr
  have hroot : (kestenPolynomial p (n + 1)).eval r = 0 := by
    rw [← monicOrtho_kestenMoment]
    exact (mem_gaussNodes_iff n r).mp hr
  obtain ⟨G, hG⟩ : (X - C r) ∣ kestenPolynomial p (n + 1) := dvd_iff_isRoot.mpr hroot
  have hPne := (kestenPolynomial_monic p (n + 1)).ne_zero
  have hGne : G ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hG
    exact hPne hG
  have hnd : (kestenPolynomial p (n + 1)).natDegree = 1 + G.natDegree := by
    rw [hG, natDegree_mul (X_sub_C_ne_zero r) hGne, natDegree_X_sub_C]
  rw [kestenPolynomial_natDegree] at hnd
  have hdeg : G.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hGne]
    exact_mod_cast (by omega : G.natDegree < n + 1)
  have hz : momentFunctional (kestenMoment p) (kestenPolynomial p (n + 1) * G) = 0 := by
    have h := monicOrtho_inner_eq_zero_of_degree_lt (kestenMoment_positiveMomentForm p)
      (n + 1) (n + 1) le_rfl G hdeg
    rwa [monicOrtho_kestenMoment, momentInner_def] at h
  -- Orthogonality turns the cofactor identity into a strict bound on the squared root.
  have hpoly : (X * G) * (X * G) =
      kestenPolynomial p (n + 1) * kestenPolynomial p (n + 1) + C r * (C r * (G * G)) +
        (C r * (kestenPolynomial p (n + 1) * G) + C r * (kestenPolynomial p (n + 1) * G)) := by
    simp only [hG]
    ring
  have he := congrArg (momentFunctional (kestenMoment p)) hpoly
  simp only [momentFunctional_add, momentFunctional_C_mul_favard, hz, mul_zero, add_zero] at he
  have hb := kestenMoment_mulX_sq_le p G
  change momentFunctional (kestenMoment p) ((X * G) * (X * G)) ≤
    4 * momentFunctional (kestenMoment p) (G * G) at hb
  have hP : 0 < momentFunctional (kestenMoment p)
      (kestenPolynomial p (n + 1) * kestenPolynomial p (n + 1)) :=
    (kestenMoment_positiveMomentForm p).pos_of_ne_zero _ hPne
  have hGpos : 0 < momentFunctional (kestenMoment p) (G * G) :=
    (kestenMoment_positiveMomentForm p).pos_of_ne_zero G hGne
  have hr2 : r ^ 2 < 4 := by
    by_contra hnot
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hGpos.le
    nlinarith only [he, hb, hP, hm]
  constructor <;> nlinarith only [hr2, sq_nonneg (r - 2), sq_nonneg (r + 2)]

/-- Christoffel weights of the prime phase form are strictly positive at every point. -/
theorem kestenChristoffel_pos (p : Nat.Primes) (n : ℕ) (x : ℝ) :
    0 < christoffel (kestenMoment p) n x :=
  christoffel_pos (kestenMoment_positiveMomentForm p) n x

/-- Explicit prime quadrature weights in terms of the corrected Chebyshev polynomials. -/
theorem kestenChristoffel_eq (p : Nat.Primes) (n : ℕ) (x : ℝ) :
    christoffel (kestenMoment p) n x =
      (1 + (1 + (p : ℝ)⁻¹)⁻¹ *
        ∑ j ∈ Finset.range n, ((kestenPolynomial p (j + 1)).eval x) ^ 2)⁻¹ := by
  rw [christoffel, cdKernel_eval_self]
  congr 1
  simp only [monicOrtho_kestenMoment, momentInner_kestenPolynomial, ite_true]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    kestenPolynomial_zero, Polynomial.eval_one, one_pow, ite_true, div_one]
  rw [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Prime Gaussian quadrature weights sum to one. -/
theorem sum_kestenChristoffel (p : Nat.Primes) (n : ℕ) :
    (∑ x ∈ gaussNodes (kestenMoment p) n, christoffel (kestenMoment p) n x) = 1 := by
  have h := momentFunctional_eq_gaussSum (kestenMoment_positiveMomentForm p) n 1 (by
    rw [Polynomial.degree_one]
    exact_mod_cast (by omega : 0 < 2 * n + 2))
  simpa only [momentFunctional_one, kestenMoment_zero, Polynomial.eval_one, mul_one] using h.symm

/-- Exact quadrature error at every polynomial degree: divide by the square of the node polynomial. -/
theorem kestenQuadrature_remainder (p : Nat.Primes) (n : ℕ) (Q : Polynomial ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * Q.eval (2 * Real.cos (Real.pi * t))) =
      (∑ x ∈ gaussNodes (kestenMoment p) n, christoffel (kestenMoment p) n x * Q.eval x) +
        ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
          (((kestenPolynomial p (n + 1)).eval (2 * Real.cos (Real.pi * t))) ^ 2 *
            (Q /ₘ (kestenPolynomial p (n + 1)) ^ 2).eval (2 * Real.cos (Real.pi * t))) := by
  classical
  have hsplit := modByMonic_add_div Q ((kestenPolynomial p (n + 1)) ^ 2)
  have hdegree : ((kestenPolynomial p (n + 1)) ^ 2).degree =
      ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (pow_ne_zero 2 (kestenPolynomial_monic p (n + 1)).ne_zero),
      natDegree_pow, kestenPolynomial_natDegree]
    congr 1
  have hrem : (Q %ₘ (kestenPolynomial p (n + 1)) ^ 2).degree <
      ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    have h := degree_modByMonic_lt Q ((kestenPolynomial_monic p (n + 1)).pow 2)
    rwa [hdegree] at h
  have hquad := momentFunctional_eq_gaussSum (kestenMoment_positiveMomentForm p) n
    (Q %ₘ (kestenPolynomial p (n + 1)) ^ 2) hrem
  have hvalues : (∑ x ∈ gaussNodes (kestenMoment p) n, christoffel (kestenMoment p) n x *
      (Q %ₘ (kestenPolynomial p (n + 1)) ^ 2).eval x) =
      ∑ x ∈ gaussNodes (kestenMoment p) n, christoffel (kestenMoment p) n x * Q.eval x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hroot : (kestenPolynomial p (n + 1)).eval x = 0 := by
      rw [← monicOrtho_kestenMoment]
      exact (mem_gaussNodes_iff n x).mp hx
    have he : (Q %ₘ (kestenPolynomial p (n + 1)) ^ 2).eval x = Q.eval x := by
      simpa [hroot] using congrArg (Polynomial.eval x) hsplit
    rw [he]
  have h := congrArg (momentFunctional (kestenMoment p)) hsplit
  rw [momentFunctional_add, hquad, hvalues] at h
  simp only [momentFunctional_kestenMoment, Polynomial.eval_mul, Polynomial.eval_pow] at h
  exact h.symm

/-- The first monomial beyond Gaussian exactness loses exactly the next monic squared norm. -/
theorem kestenQuadrature_first_defect (p : Nat.Primes) (n : ℕ) :
    kestenMoment p (2 * n + 2) -
        ∑ x ∈ gaussNodes (kestenMoment p) n,
          christoffel (kestenMoment p) n x * x ^ (2 * n + 2) =
      1 + (p : ℝ)⁻¹ := by
  have hpos : PositiveMomentFormBelow (kestenMoment p) (n + 2) :=
    ⟨fun Q hQ _ => (kestenMoment_positiveMomentForm p).pos_of_ne_zero Q hQ⟩
  have h := momentFunctional_sub_gaussSum_eq_topCoeff_mul_nextNorm_below
    hpos n (by omega) (X ^ (2 * n + 2)) (by
      rw [degree_X_pow]
      exact_mod_cast (by omega : 2 * n + 2 < 2 * n + 3))
  have hn := monicOrthoNormSq_kestenMoment_succ p n
  change momentInner (kestenMoment p) (monicOrtho (kestenMoment p) (n + 1))
    (monicOrtho (kestenMoment p) (n + 1)) = 1 + (p : ℝ)⁻¹ at hn
  simpa only [momentFunctional_X_pow, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow_self, hn, one_mul] using h

end
end GaloisForLFunctions.SelbergClass.Primon
