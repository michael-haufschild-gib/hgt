import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

/-!
# Nonzero polynomial-coefficient relations admit upper-half-plane jet detectors

A nonzero multivariate polynomial whose coefficients are one-variable complex polynomials remains
nonzero after specializing the coefficient variable at some arbitrarily high point.  For a finite
injective shift packet, the point can be chosen so that all translated evaluation nodes are
distinct and lie in the upper half-plane.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Specialize the one-variable polynomial coefficients of a multivariate polynomial at `z`. -/
noncomputable def specializePolynomialCoefficients {σ : Type*} (z : ℂ) :
    MvPolynomial σ ℂ[X] →+* MvPolynomial σ ℂ :=
  MvPolynomial.map (Polynomial.evalRingHom z)

/-- A nonzero polynomial-coefficient relation has a nonzero specialization at some point above
every prescribed horizontal line. -/
theorem exists_upper_specializePolynomialCoefficients_ne_zero
    {σ : Type*} (Q : MvPolynomial σ ℂ[X]) (hQ : Q ≠ 0) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧ specializePolynomialCoefficients z Q ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := MvPolynomial.coeff d Q
  let vertical : ℝ → ℂ := fun y => (y : ℂ) * Complex.I
  have hvert : Function.Injective vertical := by
    intro y₁ y₂ h
    have him := congrArg Complex.im h
    simpa [vertical] using him
  have hS : (vertical '' Set.Ioi H).Infinite :=
    (Set.Ioi_infinite H).image hvert.injOn
  have hnot : ¬ vertical '' Set.Ioi H ⊆ {z | q.IsRoot z} := by
    intro hsub
    exact (Polynomial.finite_setOf_isRoot hcoeff).not_infinite (hS.mono hsub)
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := Set.not_subset.mp hnot
  refine ⟨vertical y, ?_, ?_⟩
  · simpa [vertical] using hy
  · intro hzero
    have hc := congrArg (MvPolynomial.coeff d) hzero
    rw [specializePolynomialCoefficients, MvPolynomial.coeff_map] at hc
    have hqeval : q.eval (vertical y) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hz
    exact hqeval (by simpa [q] using hc)

/-- Every finite complex family has a common lower bound for the negatives of its imaginary
parts. -/
theorem finite_complex_family_has_imaginary_lower_bound
    {ι : Type*} [Fintype ι] (shift : ι → ℂ) :
    ∃ H : ℝ, ∀ i, -(shift i).im ≤ H := by
  let H := ∑ i, |(shift i).im|
  refine ⟨H, ?_⟩
  intro i
  have hi : |(shift i).im| ≤ H := by
    refine Finset.single_le_sum (s := Finset.univ)
      (f := fun j => |(shift j).im|) ?_ (Finset.mem_univ i)
    intro j hj
    exact abs_nonneg _
  exact (neg_le_abs _).trans hi

/-- A nonzero polynomial-coefficient relation on a finite injective shift packet has a nonzero
finite-jet detector at distinct upper-half-plane nodes. -/
theorem exists_upper_noncolliding_polynomial_detector
    {ι σ : Type*} [Fintype ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift)
    (Q : MvPolynomial σ ℂ[X]) (hQ : Q ≠ 0) :
    ∃ z : ℂ,
      specializePolynomialCoefficients z Q ≠ 0 ∧
      Function.Injective (fun i => z + shift i) ∧
      ∀ i, 0 < (z + shift i).im := by
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  obtain ⟨z, hzH, hzQ⟩ :=
    exists_upper_specializePolynomialCoefficients_ne_zero Q hQ H
  refine ⟨z, hzQ, ?_, ?_⟩
  · intro i j hij
    exact hshift (add_left_cancel hij)
  · intro i
    rw [Complex.add_im]
    linarith [hH i]

end GaloisForLFunctions.HTGeometry
