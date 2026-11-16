import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LinearMomentQuotient
import GaloisForLFunctions.RepresentationLifting.Spinor.NullPolarization

/-!
# Angular harmonics from null polarizations

Every power of a null linear form is an actual harmonic polynomial.
The polynomial angular Laplacian acts on its degree-`m` component by
`-m(m+D-2)`, providing the complete angular tower from each null lift.
-/

open MvPolynomial
open scoped BigOperators
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate Laplacian on the complex polynomial algebra. -/
def euclideanPolynomialLaplacian (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ i, pderiv i (pderiv i P)

/-- Radial Euler derivation. -/
def polynomialEuler (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ i, X i * pderiv i P

/-- The tangential sphere operator expressed on ambient polynomials. -/
def angularPolynomialLaplacian (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  (∑ i, X i^2) * euclideanPolynomialLaplacian P - polynomialEuler (polynomialEuler P) -
    C ((Fintype.card ι : ℂ)-2) * polynomialEuler P

lemma pderiv_momentLinearForm (a : ι → ℂ) (i : ι) :
    pderiv i (momentLinearForm ℂ a) = C (a i) := by
  simp [momentLinearForm_apply, map_sum, pderiv_X, smul_eq_C_mul, Pi.single_apply]

/-- The second derivatives of a linear-form power contain only its coefficient squares. -/
lemma pderiv_twice_momentLinearForm_pow (a : ι → ℂ) (i : ι) (m : ℕ) :
    pderiv i (pderiv i (momentLinearForm ℂ a ^ (m+2))) =
      C ((m+2 : ℂ)*(m+1)*a i^2) * momentLinearForm ℂ a ^ m := by
  rw [pderiv_pow, pderiv_momentLinearForm]
  rw [show m+2-1 = m+1 by omega]
  have he : ((m+2 : ℕ) : MvPolynomial ι ℂ) * momentLinearForm ℂ a ^ (m+1) * C (a i) =
      C ((m+2 : ℂ)*a i) * momentLinearForm ℂ a ^ (m+1) := by
    simp only [map_mul, map_add, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [he, pderiv_C_mul, pderiv_pow, pderiv_momentLinearForm]
  simp only [Nat.add_sub_cancel, map_mul, map_add, map_natCast, map_ofNat, map_pow, Nat.cast_add, map_one]
  ring

/-- The complete Laplacian contracts the coefficient vector with the Euclidean quadratic form. -/
theorem laplacian_momentLinearForm_pow (a : ι → ℂ) (m : ℕ) :
    euclideanPolynomialLaplacian (momentLinearForm ℂ a ^ (m+2)) =
      C ((m+2 : ℂ)*(m+1) * ∑ i, a i^2) * momentLinearForm ℂ a ^ m := by
  simp only [euclideanPolynomialLaplacian, pderiv_twice_momentLinearForm_pow,
    ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum, mul_assoc]

/-- Null polarizations yield harmonic polynomials in every nonnegative degree. -/
theorem nullPolarization_harmonic (q : Fin d → ℝ) (m : ℕ) :
    euclideanPolynomialLaplacian (momentLinearForm ℂ (nullPolarization q) ^ m) = 0 := by
  have hq : ∑ i, nullPolarization q i ^ 2 = 0 := by
    have h := nullPolarization_square q
    rw [euclideanComplexForm_apply] at h
    simpa only [Fintype.sum_option] using h
  rcases m with _ | _ | m
  · simp only [pow_zero, euclideanPolynomialLaplacian, pderiv_one, map_zero, Finset.sum_const_zero]
  · change euclideanPolynomialLaplacian (momentLinearForm ℂ (nullPolarization q) ^ 1) = 0
    simp only [pow_one, euclideanPolynomialLaplacian, pderiv_momentLinearForm,
      pderiv_C, Finset.sum_const_zero]
  · rw [laplacian_momentLinearForm_pow, hq, mul_zero, map_zero, zero_mul]

omit [DecidableEq ι] in
lemma polynomialEuler_C_mul (c : ℂ) (P : MvPolynomial ι ℂ) :
    polynomialEuler (C c * P) = C c * polynomialEuler P := by
  simp only [polynomialEuler, pderiv_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Euler's homogeneous-degree identity for the actual linear-form powers. -/
theorem polynomialEuler_momentLinearForm_pow (a : ι → ℂ) (m : ℕ) :
    polynomialEuler (momentLinearForm ℂ a ^ m) = C (m : ℂ) * momentLinearForm ℂ a ^ m := by
  cases m with
  | zero => simp [polynomialEuler]
  | succ m =>
    simp only [polynomialEuler, pderiv_pow, pderiv_momentLinearForm, Nat.add_sub_cancel]
    have he (i : ι) : X i * (((m+1 : ℕ) : MvPolynomial ι ℂ) * momentLinearForm ℂ a ^ m * C (a i)) =
        (a i • X i) * (C (m+1 : ℂ) * momentLinearForm ℂ a ^ m) := by
      simp only [smul_eq_C_mul, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
      ring
    simp_rw [he]
    rw [← Finset.sum_mul, ← momentLinearForm_apply, pow_succ]
    simp only [map_natCast, map_add, map_one, Nat.cast_add, Nat.cast_one]
    ring

/-- Every null polarization gives the complete tower of angular Laplacian eigenpolynomials. -/
theorem nullPolarization_angular_eigen (q : Fin d → ℝ) (m : ℕ) :
    angularPolynomialLaplacian (momentLinearForm ℂ (nullPolarization q)^m) =
      C (-(m : ℂ)*((m : ℂ)+d-1)) * momentLinearForm ℂ (nullPolarization q)^m := by
  rw [angularPolynomialLaplacian, nullPolarization_harmonic, mul_zero,
    polynomialEuler_momentLinearForm_pow, polynomialEuler_C_mul,
    polynomialEuler_momentLinearForm_pow]
  simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    map_mul, map_neg, map_sub, map_add, map_natCast, map_one, map_ofNat]
  ring

/-- A concrete null direction supplies nonzero harmonic polynomials in every degree. -/
theorem coordinateNullHarmonics_nonzero (d m : ℕ) :
    momentLinearForm ℂ (nullPolarization (Pi.single (0 : Fin (d+1)) (1:ℝ))) ^ m ≠ 0 := by
  apply pow_ne_zero
  intro hz
  have h := congrArg (pderiv (some (0 : Fin (d+1)))) hz
  rw [pderiv_momentLinearForm, map_zero] at h
  simpa [nullPolarization] using h

#print axioms laplacian_momentLinearForm_pow
#print axioms nullPolarization_harmonic
#print axioms polynomialEuler_momentLinearForm_pow
#print axioms nullPolarization_angular_eigen
#print axioms coordinateNullHarmonics_nonzero

end
end GaloisForLFunctions.RepresentationLifting.Spinor
