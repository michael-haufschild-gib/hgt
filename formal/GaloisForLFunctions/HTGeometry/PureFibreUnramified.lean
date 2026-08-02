import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The pure critical fibre is unramified

The pure critical fibre consists of the factorisations `A B = 1 + t^L` with `deg A = m` and
`deg B = n`.  Perturbing such a factorisation inside the fibre — that is, moving `A` in degrees below
`m` and `B` in degrees below `n` while keeping the product congruent to one over the horizon — forces
the perturbation to vanish:

`deg dA < m`, `deg dB < n`, `t^L | dA B + A dB`  implies  `dA = 0` and `dB = 0`.

The proof is two steps.  The perturbed product has degree below `L`, so divisibility by `t^L` makes
it *zero*, not merely small; and `A` and `B` are coprime because `1 + t^L` is separable, so `A`
divides `dA`, which has smaller degree.

This is the Jacobian criterion at the pure point: the differential of the observation map is
injective there, hence — the observation space and the jet space having the same dimension — an
isomorphism.  It is what makes the pure fibre reduced, and it is the input a deformation of the
observation needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **The cyclic polynomial of the pure critical fibre is separable.** -/
theorem separable_one_add_X_pow {L : ℕ} (hL : (L : K) ≠ 0) :
    (1 + X ^ L : K[X]).Separable := by
  have h : (1 + X ^ L : K[X]) = X ^ L - C (-1) := by
    rw [map_neg, map_one, sub_neg_eq_add, add_comm]
  rw [h]
  exact separable_X_pow_sub_C (-1) hL (neg_ne_zero.2 one_ne_zero)

/-- **The two factors of a pure critical factorisation are coprime.** -/
theorem isCoprime_of_pureFactorisation {L : ℕ} {A B : K[X]} (hL : (L : K) ≠ 0)
    (h : A * B = 1 + X ^ L) : IsCoprime A B :=
  Polynomial.Separable.isCoprime (by rw [h]; exact separable_one_add_X_pow hL)

/-- The cyclic polynomial is nonzero. -/
theorem one_add_X_pow_ne_zero {L : ℕ} (hL : 0 < L) : (1 + X ^ L : K[X]) ≠ 0 := by
  intro hcon
  have hdeg : (1 + X ^ L : K[X]).natDegree = L := by
    rw [add_comm, ← C_1, natDegree_X_pow_add_C]
  rw [hcon, Polynomial.natDegree_zero] at hdeg
  omega

/-- **The degrees of a pure critical factorisation are exact.** -/
theorem natDegree_pureFactorisation {m n : ℕ} {A B : K[X]} (hL : 0 < m + n)
    (h : A * B = 1 + X ^ (m + n)) (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    A.natDegree = m ∧ B.natDegree = n ∧ A ≠ 0 ∧ B ≠ 0 := by
  have hne : (A * B : K[X]) ≠ 0 := by
    rw [h]
    exact one_add_X_pow_ne_zero hL
  have hA0 : A ≠ 0 := fun hcon => hne (by rw [hcon, zero_mul])
  have hB0 : B ≠ 0 := fun hcon => hne (by rw [hcon, mul_zero])
  have hsum : A.natDegree + B.natDegree = m + n := by
    rw [← Polynomial.natDegree_mul hA0 hB0, h, add_comm, ← C_1, natDegree_X_pow_add_C]
  exact ⟨by omega, by omega, hA0, hB0⟩

/-- **A polynomial of degree below the horizon divisible by the horizon vanishes.** -/
theorem eq_zero_of_X_pow_dvd_of_natDegree_lt {L : ℕ} {P : K[X]}
    (hdvd : (X : K[X]) ^ L ∣ P) (hdeg : P.natDegree < L) : P = 0 := by
  by_contra hcon
  have hle := Polynomial.natDegree_le_of_dvd hdvd hcon
  rw [Polynomial.natDegree_X_pow] at hle
  omega

/-- **The pure critical fibre is unramified.**  A perturbation of a pure factorisation that keeps
the raw coefficients from the critical order on, keeps the reciprocal coefficients from the
reciprocal critical order on, and keeps the product congruent to one over the horizon, is zero.

Equivalently, the differential of the observation map is injective at a pure point. -/
theorem tangent_eq_zero_of_pureFactorisation {m n : ℕ} {A B dA dB : K[X]}
    (hm : 0 < m) (hn : 0 < n) (hL : ((m + n : ℕ) : K) ≠ 0)
    (hAB : A * B = 1 + X ^ (m + n))
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n)
    (hdA : dA.natDegree < m) (hdB : dB.natDegree < n)
    (hdvd : (X : K[X]) ^ (m + n) ∣ dA * B + A * dB) :
    dA = 0 ∧ dB = 0 := by
  obtain ⟨hdegA, hdegB, hA0, _⟩ := natDegree_pureFactorisation (by omega) hAB hA hB
  have hbound : (dA * B + A * dB).natDegree < m + n := by
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (Polynomial.natDegree_mul_le) (by omega)
    · exact lt_of_le_of_lt (Polynomial.natDegree_mul_le) (by omega)
  have hzero : dA * B + A * dB = 0 := eq_zero_of_X_pow_dvd_of_natDegree_lt hdvd hbound
  have hdvdA : A ∣ dA * B := ⟨-dB, by linear_combination hzero⟩
  have hcop : IsCoprime A B := isCoprime_of_pureFactorisation hL hAB
  have hAdA : A ∣ dA := hcop.dvd_of_dvd_mul_right hdvdA
  have hdA0 : dA = 0 := by
    by_contra hcon
    have := Polynomial.natDegree_le_of_dvd hAdA hcon
    omega
  refine ⟨hdA0, ?_⟩
  rw [hdA0, zero_mul, zero_add] at hzero
  exact (mul_eq_zero.1 hzero).resolve_left hA0

end GaloisForLFunctions.HTGeometry
