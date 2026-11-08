import GaloisForLFunctions.SelbergClass.Primon.KestenOrthogonalPolynomials

/-!
# Exact Jacobi geometry of Kesten–McKay phase averaging

The actual integral moments of the prime phase density equal the existing
Favard construction with one exceptional first edge. Consequently the
moment form is positive definite and Gram–Schmidt produces the explicit
prime polynomials. Every positive-degree member of this family has squared norm
`1 + p⁻¹`; the constant polynomial has squared norm one.
-/

open MeasureTheory Set Polynomial HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Moments of the normalized Hecke coordinate under the actual prime phase density. -/
def kestenMoment (p : Nat.Primes) (n : ℕ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (2 * Real.cos (Real.pi * t)) ^ n

@[simp] theorem kestenMoment_zero (p : Nat.Primes) : kestenMoment p 0 = 1 := by
  simp [kestenMoment, integral_kestenMcKayDensity]

/-- The moment functional is exactly integration of polynomial phase observables. -/
theorem momentFunctional_kestenMoment (p : Nat.Primes) (Q : Polynomial ℝ) :
    momentFunctional (kestenMoment p) Q =
      ∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * Q.eval (2 * Real.cos (Real.pi * t)) := by
  have hi (i : ℕ) : IntegrableOn (fun t : ℝ => Q.coeff i *
      (kestenMcKayDensity p t * (2 * Real.cos (Real.pi * t)) ^ i)) (Ioo 0 1) :=
    (continuous_const.mul ((continuous_kestenMcKayDensity p).mul
      (by fun_prop))).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have he : (fun t : ℝ => kestenMcKayDensity p t * Q.eval (2 * Real.cos (Real.pi * t))) =
      fun t => ∑ i ∈ Q.support, Q.coeff i *
        (kestenMcKayDensity p t * (2 * Real.cos (Real.pi * t)) ^ i) := by
    funext t
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, integral_finsetSum Q.support (fun i _ => hi i), momentFunctional_eq_support_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  rfl

/-- Integration against the density realizes the unique normalized Favard moments. -/
theorem kestenMoment_eq_favard (p : Nat.Primes) :
    kestenMoment p = favardMoment (fun _ => 0) (kestenJacobiLower p) := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hz : momentFunctional (kestenMoment p) (kestenPolynomial p (n + 1)) = 0 := by
        rw [momentFunctional_kestenMoment]
        exact integral_kestenPolynomial_succ p n
      have hs : momentFunctional (kestenMoment p) (kestenPolynomial p (n + 1)) =
          ∑ i ∈ Finset.range (n + 2), (kestenPolynomial p (n + 1)).coeff i * kestenMoment p i := by
        rw [momentFunctional_eq_support_sum]
        have hnd := kestenPolynomial_natDegree p (n + 1)
        rw [show n + 2 = (kestenPolynomial p (n + 1)).natDegree + 1 by omega]
        exact Finset.sum_subset (kestenPolynomial p (n + 1)).supp_subset_range_natDegree_succ
          (fun i _ hi => by rw [Polynomial.notMem_support_iff.mp hi, zero_mul])
      have hlead : (kestenPolynomial p (n + 1)).coeff (n + 1) = 1 := by
        have h := (kestenPolynomial_monic p (n + 1)).coeff_natDegree
        rwa [kestenPolynomial_natDegree] at h
      rw [hs, Finset.sum_range_succ, hlead, one_mul] at hz
      have hsum : (∑ i ∈ Finset.range (n + 1),
          (kestenPolynomial p (n + 1)).coeff i * kestenMoment p i) =
          ∑ i ∈ Finset.range (n + 1), (kestenPolynomial p (n + 1)).coeff i *
            favardMoment (fun _ => 0) (kestenJacobiLower p) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (Finset.mem_range.mp hi)]
      rw [hsum] at hz
      rw [favardMoment_succ]
      change kestenMoment p (n + 1) =
        -∑ i ∈ Finset.range (n + 1), (kestenPolynomial p (n + 1)).coeff i *
          favardMoment (fun _ => 0) (kestenJacobiLower p) i
      linarith only [hz]

/-- The prime phase moment form is strictly positive definite. -/
theorem kestenMoment_positiveMomentForm (p : Nat.Primes) :
    PositiveMomentForm (kestenMoment p) := by
  rw [kestenMoment_eq_favard]
  exact favard_positiveMomentForm _ _ (fun n => kestenJacobiLower_pos p (n + 1))

/-- Gram–Schmidt of the actual phase moments returns the explicit prime polynomials. -/
theorem monicOrtho_kestenMoment (p : Nat.Primes) (n : ℕ) :
    monicOrtho (kestenMoment p) n = kestenPolynomial p n := by
  rw [kestenMoment_eq_favard]
  exact monicOrtho_favardMoment _ _ (fun k => kestenJacobiLower_pos p (k + 1)) n

/-- The diagonal of the prime Jacobi matrix vanishes identically. -/
theorem monicOrthoAlpha_kestenMoment (p : Nat.Primes) (n : ℕ) :
    monicOrthoAlpha (kestenMoment p) n = 0 := by
  rw [kestenMoment_eq_favard]
  exact monicOrthoAlpha_favardMoment _ _ (fun k => kestenJacobiLower_pos p (k + 1)) n

/-- The first lower Jacobi coefficient is `1 + p⁻¹`, and all later ones equal one. -/
theorem monicOrthoBeta_kestenMoment (p : Nat.Primes) (n : ℕ) :
    monicOrthoBeta (kestenMoment p) (n + 1) = kestenJacobiLower p (n + 1) := by
  rw [kestenMoment_eq_favard]
  exact monicOrthoBeta_favardMoment _ _ (fun k => kestenJacobiLower_pos p (k + 1))
    (by omega : 0 < n + 1)

private theorem prod_kestenJacobiLower (p : Nat.Primes) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), kestenJacobiLower p (j + 1)) = 1 + (p : ℝ)⁻¹ := by
  induction n with
  | zero => simp [kestenJacobiLower]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    simp [kestenJacobiLower]

/-- All nonconstant monic prime polynomials have the same squared norm. -/
theorem monicOrthoNormSq_kestenMoment_succ (p : Nat.Primes) (n : ℕ) :
    monicOrthoNormSq (kestenMoment p) (n + 1) = 1 + (p : ℝ)⁻¹ := by
  rw [kestenMoment_eq_favard,
    monicOrthoNormSq_favardMoment _ _ (fun k => kestenJacobiLower_pos p (k + 1)),
    prod_kestenJacobiLower]

/-- The explicit phase integrals have the exact nonconstant orthogonal-polynomial norms. -/
theorem integral_kestenPolynomial_sq_succ (p : Nat.Primes) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ((kestenPolynomial p (n + 1)).eval (2 * Real.cos (Real.pi * t))) ^ 2) =
      1 + (p : ℝ)⁻¹ := by
  have h := monicOrthoNormSq_kestenMoment_succ p n
  rw [monicOrthoNormSq, monicOrtho_kestenMoment, momentInner_def,
    momentFunctional_kestenMoment] at h
  simpa only [Polynomial.eval_mul, pow_two] using h

/-- The algebraic moment Gram matrix is diagonal with the explicit prime norms. -/
theorem momentInner_kestenPolynomial (p : Nat.Primes) (m n : ℕ) :
    momentInner (kestenMoment p) (kestenPolynomial p m) (kestenPolynomial p n) =
      if m = n then (if n = 0 then 1 else 1 + (p : ℝ)⁻¹) else 0 := by
  rw [← monicOrtho_kestenMoment, ← monicOrtho_kestenMoment]
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    cases n with
    | zero => simp [monicOrtho_zero, momentInner_def, momentFunctional_one]
    | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      exact monicOrthoNormSq_kestenMoment_succ p n
  · rw [if_neg hmn]
    exact monicOrtho_inner_eq_zero (kestenMoment_positiveMomentForm p) hmn

/-- Exact Gram matrix of the explicit prime polynomials for the phase integral. -/
theorem integral_kestenPolynomial_gram (p : Nat.Primes) (m n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ((kestenPolynomial p m).eval (2 * Real.cos (Real.pi * t)) *
        (kestenPolynomial p n).eval (2 * Real.cos (Real.pi * t)))) =
      if m = n then (if n = 0 then 1 else 1 + (p : ℝ)⁻¹) else 0 := by
  have he : (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ((kestenPolynomial p m).eval (2 * Real.cos (Real.pi * t)) *
        (kestenPolynomial p n).eval (2 * Real.cos (Real.pi * t)))) =
      momentInner (kestenMoment p) (monicOrtho (kestenMoment p) m)
        (monicOrtho (kestenMoment p) n) := by
    rw [monicOrtho_kestenMoment, monicOrtho_kestenMoment, momentInner_def,
      momentFunctional_kestenMoment]
    simp only [Polynomial.eval_mul]
  rw [he, monicOrtho_kestenMoment, monicOrtho_kestenMoment]
  exact momentInner_kestenPolynomial p m n

/-- No nonzero polynomial observable has zero norm under the prime phase density. -/
theorem integral_kesten_polynomial_sq_pos_iff (p : Nat.Primes) (Q : Polynomial ℝ) :
    (0 < ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      (Q.eval (2 * Real.cos (Real.pi * t))) ^ 2) ↔ Q ≠ 0 := by
  have he : (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      (Q.eval (2 * Real.cos (Real.pi * t))) ^ 2) = momentInner (kestenMoment p) Q Q := by
    rw [momentInner_def, momentFunctional_kestenMoment]
    simp only [Polynomial.eval_mul, pow_two]
  rw [he]
  constructor
  · intro h hQ
    subst Q
    simp at h
  · exact (kestenMoment_positiveMomentForm p).pos_of_ne_zero Q

end
end GaloisForLFunctions.SelbergClass.Primon
