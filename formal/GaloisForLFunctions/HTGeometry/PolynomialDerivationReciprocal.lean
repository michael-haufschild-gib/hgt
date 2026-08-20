import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# The differential of a truncated reciprocal

A derivation extends coefficientwise to polynomials, valued in the polynomial module of its target.
The extension satisfies the Leibniz rule and kills the coefficients of `X ^ L`, so a truncated
inverse relation `X ^ L ∣ f * g - 1` can be differentiated and solved:

```text
polyD_reciprocal :  d (g.coeff l) = -∑_{i+j=l} (g * g).coeff i • d (f.coeff j)   for l < L
```

This is the exact Kähler form of `dY = -Y² dX`, the first-order law governing the reciprocal of a
truncated jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PolynomialModule

variable {K R M : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]

/-- Coefficientwise extension of a derivation to polynomials. -/
private noncomputable def polyD (d : Derivation K R M) (p : R[X]) : PolynomialModule R M :=
  ∑ n ∈ p.support, PolynomialModule.single R n (d (p.coeff n))

@[simp] theorem polyD_coeff (d : Derivation K R M) (p : R[X]) (n : ℕ) :
    (polyD d p).coeff n = d (p.coeff n) := by
  classical
  have h : (polyD d p).coeff n
      = ∑ k ∈ p.support, (if k = n then d (p.coeff k) else 0) := by
    simp [polyD, PolynomialModule.coeff_sum, PolynomialModule.coeff_single,
      Finsupp.single_apply]
  rw [h, Finset.sum_ite_eq' p.support n (fun k => d (p.coeff k))]
  by_cases hn : n ∈ p.support
  · simp [hn]
  · simp only [hn, if_false]
    rw [Polynomial.notMem_support_iff.mp hn, map_zero]

theorem polyD_ext {x y : PolynomialModule R M} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
  apply PolynomialModule.coeff_injective
  ext n
  exact h n

theorem polyD_add (d : Derivation K R M) (p q : R[X]) :
    polyD d (p + q) = polyD d p + polyD d q := by
  refine polyD_ext fun n => ?_
  show (polyD d (p + q)).coeff n = (polyD d p).coeff n + (polyD d q).coeff n
  simp

theorem polyD_mul (d : Derivation K R M) (p q : R[X]) :
    polyD d (p * q) = p • polyD d q + q • polyD d p := by
  refine polyD_ext fun n => ?_
  show (polyD d (p * q)).coeff n
      = (p • polyD d q).coeff n + (q • polyD d p).coeff n
  rw [polyD_coeff, Polynomial.coeff_mul, map_sum,
    PolynomialModule.smul_apply, PolynomialModule.smul_apply]
  simp only [Derivation.leibniz, polyD_coeff]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.Nat.sum_antidiagonal_swap (f := fun z : ℕ × ℕ => q.coeff z.1 • d (p.coeff z.2))

theorem polyD_X_pow (d : Derivation K R M) (L : ℕ) : polyD d ((X : R[X]) ^ L) = 0 := by
  refine polyD_ext fun n => ?_
  show (polyD d ((X : R[X]) ^ L)).coeff n = (0 : M)
  rw [polyD_coeff, Polynomial.coeff_X_pow]
  by_cases h : n = L <;> simp [h]

theorem polyD_one (d : Derivation K R M) : polyD d (1 : R[X]) = 0 := by
  refine polyD_ext fun n => ?_
  show (polyD d (1 : R[X])).coeff n = (0 : M)
  simp only [polyD_coeff, Polynomial.coeff_one]
  by_cases hn : n = 0 <;> simp [hn]

theorem coeff_X_pow_smul_of_lt (L : ℕ) (z : PolynomialModule R M) {l : ℕ} (hl : l < L) :
    ((X : R[X]) ^ L • z).coeff l = 0 := by
  rw [Polynomial.X_pow_eq_monomial, PolynomialModule.monomial_smul_apply, if_neg (by omega)]

/-- **The differential of a truncated reciprocal.**  If `f * g = 1` modulo `X ^ L`, then below
degree `L` the differential of `g` is `-(g * g)` convolved with the differential of `f`. -/
theorem polyD_reciprocal (d : Derivation K R M) {f g : R[X]} {L : ℕ}
    (hfg : (X : R[X]) ^ L ∣ f * g - 1) {l : ℕ} (hl : l < L) :
    d (g.coeff l)
      = -∑ x ∈ Finset.antidiagonal l, (g * g).coeff x.1 • d (f.coeff x.2) := by
  classical
  obtain ⟨h, hh⟩ := hfg
  have hgf : g * f = 1 + (X : R[X]) ^ L * h := by
    rw [mul_comm, ← hh]; ring
  have hD : f • polyD d g + g • polyD d f = (X : R[X]) ^ L • polyD d h := by
    have h1 : polyD d (f * g) = polyD d (1 + (X : R[X]) ^ L * h) := by
      rw [show f * g = 1 + (X : R[X]) ^ L * h by rw [mul_comm]; exact hgf]
    rw [polyD_mul, polyD_add, polyD_mul, polyD_one, polyD_X_pow, smul_zero, add_zero,
      zero_add] at h1
    exact h1
  have hgD := congrArg (fun z => g • z) hD
  simp only [smul_add, smul_smul] at hgD
  rw [hgf, add_smul, one_smul] at hgD
  rw [show ((X : R[X]) ^ L * h) • polyD d g = (X : R[X]) ^ L • (h • polyD d g) from
      mul_smul _ _ _,
    show (g * (X : R[X]) ^ L) • polyD d h = (X : R[X]) ^ L • (g • polyD d h) by
      rw [mul_comm, mul_smul]] at hgD
  have hkey : polyD d g + (g * g) • polyD d f
      = (X : R[X]) ^ L • (g • polyD d h) - (X : R[X]) ^ L • (h • polyD d g) :=
    eq_sub_of_add_eq (by rw [← hgD]; abel)
  have hcoeff := congrArg (fun z : PolynomialModule R M => z.coeff l) hkey
  rw [show ((polyD d g + (g * g) • polyD d f : PolynomialModule R M).coeff l)
      = (polyD d g).coeff l + ((g * g) • polyD d f).coeff l from rfl,
    show ((((X : R[X]) ^ L • (g • polyD d h) - (X : R[X]) ^ L • (h • polyD d g) :
        PolynomialModule R M)).coeff l)
      = ((X : R[X]) ^ L • (g • polyD d h)).coeff l
        - ((X : R[X]) ^ L • (h • polyD d g)).coeff l from rfl,
    coeff_X_pow_smul_of_lt L _ hl, coeff_X_pow_smul_of_lt L _ hl, sub_zero,
    PolynomialModule.smul_apply, polyD_coeff] at hcoeff
  simp only [polyD_coeff] at hcoeff
  exact eq_neg_of_add_eq_zero_left hcoeff

end GaloisForLFunctions.HTGeometry
