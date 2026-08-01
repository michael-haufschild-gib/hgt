import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# The conormal pairing of the critical horizon and the uniqueness of a ramified state

The top-coefficient pairing of a low-degree polynomial with a marked tail is the reversal of the
coefficient lists, so it is perfect: a low-degree polynomial pairing to zero against every tail
monomial vanishes.  This is what makes the conormal line at a branch value determine the vertical
tangent pair.

Two states over the same branch value with the same tails then satisfy a syzygy against that tangent
pair.  Coprimality turns the syzygy into a single cofactor, and the surviving low coefficient of a
product forces that cofactor to vanish, so the two states coincide.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The pairing is the reversal of coefficients -/

theorem coeff_mul_X_pow_top {K : Type*} [CommRing K] (U : K[X]) {L i : ℕ} (hi : i < L) :
    (U * Polynomial.X ^ (L - 1 - i)).coeff (L - 1) = U.coeff i := by
  rw [Polynomial.coeff_mul_X_pow' , if_pos (by omega)]
  congr 1
  omega

/-- **The conormal pairing is perfect.**  A polynomial of degree below `m` pairing to zero in the
top coefficient against every tail monomial of order at least `n` vanishes. -/
theorem eq_zero_of_pairing_eq_zero {K : Type*} [CommRing K] {U : K[X]} {m n L : ℕ}
    (hL : L = m + n) (hU : U.natDegree < m)
    (hpair : ∀ j, n ≤ j → j < L → (U * Polynomial.X ^ j).coeff (L - 1) = 0) :
    U = 0 := by
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  by_cases hi : i < m
  · have h := hpair (L - 1 - i) (by omega) (by omega)
    rw [← coeff_mul_X_pow_top U (L := L) (i := i) (by omega)]
    exact h
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## The syzygy of two states over one branch value -/

/-- **A syzygy against a coprime pair factors through a single cofactor.** -/
theorem exists_cofactor_of_syzygy {R : Type*} [CommRing R] [IsDomain R] {U V D E : R}
    (hUV : IsCoprime U V) (hU : U ≠ 0) (h : D * V + E * U = 0) :
    ∃ C, D = C * U ∧ E = -(C * V) := by
  have hdvd : U ∣ D * V := ⟨-E, by linear_combination h⟩
  obtain ⟨C, hC⟩ := hUV.dvd_of_dvd_mul_right hdvd
  refine ⟨C, by rw [hC]; ring, ?_⟩
  have hzero : U * (C * V + E) = 0 := by
    rw [hC] at h
    linear_combination h
  have hCV : C * V + E = 0 := by
    rcases mul_eq_zero.1 hzero with h1 | h1
    · exact absurd h1 hU
    · exact h1
  linear_combination hCV

/-- **Uniqueness of the ramified state.**  Two states over one branch value with the same tails and
the same vertical tangent pair coincide: the syzygy makes their difference a multiple of the tangent,
and the marked tail coefficient makes that multiple vanish. -/
theorem eq_zero_of_syzygy_of_marked_coeff {K : Type*} [Field K] {U V D E S : K[X]} {m n : ℕ}
    (hU : U ≠ 0) (hD : D.natDegree < m)
    (hsyz : D * V + E * U = 0) (hS : S.coeff n ≠ 0)
    (hmul : ∀ k < m + n, (D * S).coeff k = 0) :
    D = 0 ∧ E = 0 := by
  have hD0 : D = 0 := by
    by_contra hne
    exact not_all_low_mul_coeff_zero_of_coeff_ne_zero hne hD hS hmul
  refine ⟨hD0, ?_⟩
  rw [hD0, zero_mul, zero_add] at hsyz
  rcases mul_eq_zero.1 hsyz with h1 | h1
  · exact h1
  · exact absurd h1 hU

end GaloisForLFunctions.HTGeometry
