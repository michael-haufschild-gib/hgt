import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Scaled Taylor transport to a moving-pole Laurent coordinate

For a polynomial coefficient `p(z)`, a moving simple-pole chart has the form
`z = a + s / T`.  This module packages that substitution as an algebra homomorphism and proves
the exact Laurent coefficient law

`[T^(-b)] p(a + s/T) = hasseDeriv b p evaluated at a, times s^b`.

The construction is faithful whenever the scale is nonzero, has no positive Laurent modes, and
commutes with scalar maps.  It is the coefficient-side interface needed to combine polynomial
coefficient Taylor shifts with scale-separated pole-jet profiles; no analytic expansion or
numerical input is used.
-/

open Polynomial LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

def polynomialDiagonalScaleAlgHom
    {R : Type*} [CommSemiring R] (s : R) : R[X] →ₐ[R] R[X] where
  toRingHom := Polynomial.compRingHom (Polynomial.C s * Polynomial.X)
  commutes' c := by simp

@[simp] theorem polynomialDiagonalScaleAlgHom_C
    {R : Type*} [CommSemiring R] (s c : R) :
    polynomialDiagonalScaleAlgHom s (Polynomial.C c) = Polynomial.C c := by
  simp [polynomialDiagonalScaleAlgHom]

@[simp] theorem polynomialDiagonalScaleAlgHom_X
    {R : Type*} [CommSemiring R] (s : R) :
    polynomialDiagonalScaleAlgHom s Polynomial.X =
      Polynomial.C s * Polynomial.X := by
  simp [polynomialDiagonalScaleAlgHom]

def scaledTaylorAlgHom
    {R : Type*} [CommSemiring R] (a s : R) : R[X] →ₐ[R] R[X] :=
  (polynomialDiagonalScaleAlgHom s).comp (Polynomial.taylorAlgHom a)

theorem scaledTaylorAlgHom_apply
    {R : Type*} [CommSemiring R] (a s : R) (p : R[X]) :
    scaledTaylorAlgHom a s p =
      (Polynomial.taylor a p).comp (Polynomial.C s * Polynomial.X) := rfl

theorem scaledTaylorAlgHom_coeff
    {R : Type*} [CommSemiring R] (a s : R) (p : R[X]) (b : ℕ) :
    (scaledTaylorAlgHom a s p).coeff b =
      (Polynomial.hasseDeriv b p).eval a * s ^ b := by
  rw [scaledTaylorAlgHom_apply, Polynomial.comp_C_mul_X_coeff,
    Polynomial.taylor_coeff]

/-- Hasse--Taylor coefficients commute with scalar maps at mapped centers. -/
theorem hasseDeriv_eval_map
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) (a : R) (b : ℕ) :
    (Polynomial.hasseDeriv b (p.map f)).eval (f a) =
      f ((Polynomial.hasseDeriv b p).eval a) := by
  rw [← Polynomial.taylor_coeff, ← Polynomial.taylor_coeff]
  have h := congrArg (Polynomial.coeff · b)
    (Polynomial.map_taylor p a f)
  simpa only [Polynomial.coeff_map] using h.symm

theorem scaledTaylorAlgHom_injective
    {R : Type*} [CommRing R] [IsDomain R] (a s : R) (hs : s ≠ 0) :
    Function.Injective (scaledTaylorAlgHom a s) := by
  intro p q hpq
  apply Polynomial.taylor_injective a
  apply Polynomial.ext
  intro b
  have h := congrArg (Polynomial.coeff · b) hpq
  change (((Polynomial.taylor a p).comp
      (Polynomial.C s * Polynomial.X)).coeff b) =
    (((Polynomial.taylor a q).comp
      (Polynomial.C s * Polynomial.X)).coeff b) at h
  rw [
    Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff] at h
  exact mul_right_cancel₀ (pow_ne_zero b hs) h

def movingPoleTaylorLaurent
    {R : Type*} [CommRing R] (a s : R) : R[X] →ₐ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp
    (Polynomial.toLaurentAlg.comp (scaledTaylorAlgHom a s))

theorem movingPoleTaylorLaurent_apply
    {R : Type*} [CommRing R] (a s : R) (p : R[X]) :
    movingPoleTaylorLaurent a s p =
      LaurentPolynomial.invert
        (Polynomial.toLaurent (scaledTaylorAlgHom a s p)) := rfl

theorem movingPoleTaylorLaurent_coeff_neg
    {R : Type*} [CommRing R] (a s : R) (p : R[X]) (b : ℕ) :
    movingPoleTaylorLaurent a s p (-(b : ℤ)) =
      (Polynomial.hasseDeriv b p).eval a * s ^ b := by
  rw [movingPoleTaylorLaurent_apply, LaurentPolynomial.invert_apply,
    neg_neg]
  rw [Polynomial.toLaurent_apply]
  change Finsupp.mapDomain (fun n : ℕ => (n : ℤ))
      (scaledTaylorAlgHom a s p).toFinsupp (b : ℤ) = _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) :=
    Int.ofNat_injective
  rw [Finsupp.mapDomain_apply hinj]
  exact scaledTaylorAlgHom_coeff a s p b

theorem movingPoleTaylorLaurent_coeff_pos
    {R : Type*} [CommRing R] (a s : R) (p : R[X])
    (q : ℤ) (hq : 0 < q) :
    movingPoleTaylorLaurent a s p q = 0 := by
  rw [movingPoleTaylorLaurent_apply, LaurentPolynomial.invert_apply,
    Polynomial.toLaurent_apply]
  apply Finsupp.mapDomain_notin_range
  rintro ⟨b, hb⟩
  omega

theorem movingPoleTaylorLaurent_coeff_zero
    {R : Type*} [CommRing R] (a s : R) (p : R[X]) :
    movingPoleTaylorLaurent a s p 0 = p.eval a := by
  simpa using movingPoleTaylorLaurent_coeff_neg a s p 0

theorem movingPoleTaylorLaurent_injective
    {R : Type*} [CommRing R] [IsDomain R] (a s : R) (hs : s ≠ 0) :
    Function.Injective (movingPoleTaylorLaurent a s) := by
  exact LaurentPolynomial.invert.injective.comp
    (Polynomial.toLaurent_injective.comp
      (scaledTaylorAlgHom_injective a s hs))

/-- Evaluating an inverted polynomial Laurent embedding at a unit evaluates
the original polynomial at the inverse unit. -/
theorem eval₂_invert_toLaurent
    {R : Type*} [CommRing R] (u : Rˣ) (p : R[X]) :
    LaurentPolynomial.eval₂ (RingHom.id R) u
        (LaurentPolynomial.invert (Polynomial.toLaurent p)) =
      p.eval ((u⁻¹ : Rˣ) : R) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n c =>
      rw [Polynomial.toLaurent_C_mul_T, map_mul,
        LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        LaurentPolynomial.eval₂_C_mul_T_neg_n]
      simp [Polynomial.eval_monomial]

/-- **Moving Taylor value law.**  Laurent evaluation of the scaled Taylor
transform is exactly substitution at the corresponding moving point. -/
theorem eval₂_movingPoleTaylorLaurent
    {R : Type*} [CommRing R] (a s : R) (u : Rˣ) (p : R[X]) :
    LaurentPolynomial.eval₂ (RingHom.id R) u
        (movingPoleTaylorLaurent a s p) =
      p.eval (a + s * ((u⁻¹ : Rˣ) : R)) := by
  rw [movingPoleTaylorLaurent_apply, eval₂_invert_toLaurent,
    scaledTaylorAlgHom_apply, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [Polynomial.taylor_eval]
  congr 1
  ring

/-- Field-coordinate form of the moving Taylor value law. -/
theorem eval₂_movingPoleTaylorLaurent_inv
    {K : Type*} [Field K] (a s : K) {x : K} (hx : x ≠ 0) (p : K[X]) :
    LaurentPolynomial.eval₂ (RingHom.id K)
        (Units.mk0 x⁻¹ (inv_ne_zero hx))
        (movingPoleTaylorLaurent a s p) =
      p.eval (a + s * x) := by
  rw [eval₂_movingPoleTaylorLaurent]
  congr 2
  simp [Units.mk0]

end

end GaloisForLFunctions
