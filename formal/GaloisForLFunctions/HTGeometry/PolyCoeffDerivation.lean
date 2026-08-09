import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The coefficient-wise extension of a derivation to a polynomial ring

A derivation `D` of a commutative ring `K` acts on `K[X]` coefficient by coefficient.  The result
`polyD D` is again a derivation, it kills `X`, and it agrees with `D` on constants.  It is the
unique derivation of `K[X]` extending `D` with `polyD D X = 0`.

The point of the construction is the evaluation law `aeval_polyD`: if `D'` is a derivation of an
algebra `L` over `K` extending `D`, then for every `q : K[X]` and every `α : L`

`D' (aeval α q) = aeval α (polyD D q) + aeval α (derivative q) * D' α`,

which is the chain rule separating the motion of the coefficients from the motion of the point.
It is what makes a derivation descend to a root of an irreducible polynomial: the value of `D' α`
is forced by the vanishing of `q` at `α`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- The coefficient-wise action of a derivation `D` of `K` on a polynomial over `K`. -/
noncomputable def polyCoeffFun (D : Derivation R K K) (q : K[X]) : K[X] :=
  ∑ i ∈ q.support, monomial i (D (q.coeff i))

@[simp]
theorem coeff_polyCoeffFun (D : Derivation R K K) (q : K[X]) (i : ℕ) :
    (polyCoeffFun D q).coeff i = D (q.coeff i) := by
  rw [polyCoeffFun, Polynomial.finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hi : i ∈ q.support
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hi h
  · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hi, map_zero]
    intro b hb
    have hbi : b ≠ i := by
      rintro rfl
      exact hi hb
    simp [hbi]

theorem polyCoeffFun_add (D : Derivation R K K) (q r : K[X]) :
    polyCoeffFun D (q + r) = polyCoeffFun D q + polyCoeffFun D r := by
  ext i
  simp

theorem polyCoeffFun_smul (D : Derivation R K K) (c : R) (q : K[X]) :
    polyCoeffFun D (c • q) = c • polyCoeffFun D q := by
  ext i
  simp

theorem polyCoeffFun_mul (D : Derivation R K K) (q r : K[X]) :
    polyCoeffFun D (q * r) = q * polyCoeffFun D r + r * polyCoeffFun D q := by
  rw [mul_comm r (polyCoeffFun D q)]
  ext i
  rw [coeff_polyCoeffFun, Polynomial.coeff_mul, map_sum, Polynomial.coeff_add,
    Polynomial.coeff_mul, Polynomial.coeff_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Derivation.leibniz, coeff_polyCoeffFun, coeff_polyCoeffFun]
  simp only [smul_eq_mul]
  ring

/-- The coefficient-wise action, as an `R`-linear map. -/
noncomputable def polyCoeffLin (D : Derivation R K K) : K[X] →ₗ[R] K[X] where
  toFun := polyCoeffFun D
  map_add' := polyCoeffFun_add D
  map_smul' c q := polyCoeffFun_smul D c q

/-- **The coefficient-wise extension of a derivation to the polynomial ring.** -/
noncomputable def polyD (D : Derivation R K K) : Derivation R K[X] K[X] :=
  Derivation.mk' (polyCoeffLin D) fun q r => by
    show polyCoeffFun D (q * r) = q • polyCoeffFun D r + r • polyCoeffFun D q
    simpa only [smul_eq_mul] using polyCoeffFun_mul D q r

@[simp]
theorem coeff_polyD (D : Derivation R K K) (q : K[X]) (i : ℕ) :
    (polyD D q).coeff i = D (q.coeff i) :=
  coeff_polyCoeffFun D q i

@[simp]
theorem polyD_C (D : Derivation R K K) (a : K) : polyD D (C a) = C (D a) := by
  ext i
  rw [coeff_polyD, Polynomial.coeff_C, Polynomial.coeff_C]
  split_ifs with h
  · rfl
  · exact map_zero D

@[simp]
theorem polyD_X (D : Derivation R K K) : polyD D (X : K[X]) = 0 := by
  ext i
  rw [coeff_polyD, Polynomial.coeff_X, Polynomial.coeff_zero]
  split_ifs with h
  · exact D.map_one_eq_zero
  · exact map_zero D

@[simp]
theorem polyD_monomial (D : Derivation R K K) (n : ℕ) (a : K) :
    polyD D (monomial n a) = monomial n (D a) := by
  ext i
  rw [coeff_polyD, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rfl
  · exact map_zero D

/-- The coefficient-wise extension commutes with the formal derivative in `X`. -/
theorem derivative_polyD (D : Derivation R K K) (q : K[X]) :
    derivative (polyD D q) = polyD D (derivative q) := by
  ext i
  rw [Polynomial.coeff_derivative, coeff_polyD, coeff_polyD, Polynomial.coeff_derivative]
  have h : q.coeff (i + 1) * ((i : K) + 1) = (i + 1) • q.coeff (i + 1) := by
    push_cast [nsmul_eq_mul]
    ring
  rw [h, map_nsmul]
  push_cast [nsmul_eq_mul]
  ring

/-! ## The evaluation law -/

section Eval

variable {L : Type*} [CommRing L] [Algebra R L] [Algebra K L]

/-- **The chain rule at a point of an extension.** For a derivation `D'` of `L` extending a
derivation `D` of `K`, the motion of `aeval α q` splits into the motion of the coefficients and
the motion of the point. -/
theorem aeval_polyD (D : Derivation R K K) (D' : Derivation R L L) (α : L)
    (hD : ∀ a : K, D' (algebraMap K L a) = algebraMap K L (D a)) (q : K[X]) :
    D' (aeval α q) = aeval α (polyD D q) + aeval α (derivative q) * D' α := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [map_add, hp, hr]
      ring
  | monomial n a =>
      rw [polyD_monomial, Polynomial.derivative_monomial, Polynomial.aeval_monomial,
        Polynomial.aeval_monomial, Polynomial.aeval_monomial, Derivation.leibniz, hD,
        Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
      cases n with
      | zero => simp
      | succ n => simp [pow_succ]; ring

end Eval

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Polynomial

@[simp]
theorem polyD_zero {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] :
    polyD (0 : Derivation R K K) = (0 : Derivation R K[X] K[X]) := by
  refine DFunLike.ext _ _ fun q => ?_
  ext i
  rw [coeff_polyD, Derivation.zero_apply, Derivation.zero_apply, Polynomial.coeff_zero]

end GaloisForLFunctions.HTGeometry
