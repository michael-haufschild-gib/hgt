/-
# Coefficients of products of scaled linear factors

Two elementary facts used to feed the germ-integrality machine: coefficients of
`∏ (C c * X - C vᵢ)` transport along ring homomorphisms, and they are integral over a base ring as
soon as `c` and the `vᵢ` are.  The scaled factor `C c * X - C vᵢ` (rather than `X - C uᵢ`) is what
makes the leading coefficient of the original bivariate polynomial disappear: with `vᵢ = c * uᵢ`,
`∏ (C c * X - C vᵢ) = C (c ^ |S|) * ∏ (X - C uᵢ)`.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

variable {ι R S : Type*} [CommRing R] [CommRing S]

/-- Coefficients of a product of scaled linear factors transport along a ring hom. -/
theorem coeff_prod_map (φ : R →+* S) (T : Finset ι) (c : R) (v : ι → R) (k : ℕ) :
    φ ((∏ i ∈ T, (Polynomial.C c * Polynomial.X - Polynomial.C (v i))).coeff k)
      = (∏ i ∈ T, (Polynomial.C (φ c) * Polynomial.X - Polynomial.C (φ (v i)))).coeff k := by
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  simp

/-- The scaled product is the original product scaled by a power of `c`. -/
theorem prod_scaled_eq (T : Finset ι) (c : R) (u : ι → R) :
    (∏ i ∈ T, (Polynomial.C c * Polynomial.X - Polynomial.C (c * u i)))
      = Polynomial.C (c ^ T.card) * ∏ i ∈ T, (Polynomial.X - Polynomial.C (u i)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Finset.card_insert_of_notMem ha]
      have hfac : Polynomial.C c * Polynomial.X - Polynomial.C (c * u a)
          = Polynomial.C c * (Polynomial.X - Polynomial.C (u a)) := by
        rw [Polynomial.C_mul, mul_sub]
      rw [hfac, pow_succ]
      simp only [Polynomial.C_mul]
      ring

/-- All coefficients of a product of scaled linear factors with integral data are integral. -/
theorem isIntegral_coeff_prod {A : Type*} [CommRing A] [Algebra R A] (T : Finset ι) {c : A}
    (hc : IsIntegral R c) {v : ι → A} (hv : ∀ i, IsIntegral R (v i)) (k : ℕ) :
    IsIntegral R ((∏ i ∈ T, (Polynomial.C c * Polynomial.X - Polynomial.C (v i))).coeff k) := by
  classical
  induction T using Finset.induction_on generalizing k with
  | empty =>
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      by_cases hk : k = 0
      · rw [if_pos hk]; exact isIntegral_one
      · rw [if_neg hk]; exact isIntegral_zero
  | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      set p : Polynomial A := ∏ i ∈ T, (Polynomial.C c * Polynomial.X - Polynomial.C (v i))
        with hp
      have hrw : ((Polynomial.C c * Polynomial.X - Polynomial.C (v a)) * p).coeff k
          = c * (Polynomial.X * p).coeff k - v a * p.coeff k := by
        rw [sub_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_C_mul]
      rw [hrw]
      refine IsIntegral.sub ?_ ((hv a).mul (ih k))
      cases k with
      | zero =>
          simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, mul_zero]
          exact isIntegral_zero
      | succ k =>
          rw [Polynomial.coeff_X_mul]
          exact hc.mul (ih k)

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
