import GaloisForLFunctions.HTGeometry.MonomialTailFibreCount
import GaloisForLFunctions.HTGeometry.HorizonTruncationCancel

/-!
# The fibre of a general observation

For arbitrary observed tails the truncated compatibility equation says exactly that the two completed
factors multiply to `1 + U V` **modulo the horizon**.  This is the general form; when the tails have
exactly the critical degrees the modulus can be dropped and the factorization becomes exact.

The reciprocal low part of a fibre point is determined by its jet low part, so the fibre is
parametrised by the jet alone and the system is square.  What makes the cancellation legitimate is
that a tail vanishes at the origin, which forces the jet's constant term to be invertible.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The general truncated form -/

/-- The truncated compatibility equation is the factorization equation, term by term. -/
theorem criticalLowProduct_sub_one {K : Type*} [CommRing K] (U V A B : K[X]) :
    criticalLowProduct U V A B - 1 = (A + U) * (B + V) - (1 + U * V) := by
  simp only [criticalLowProduct]
  ring

/-- **For any observation the truncated compatibility says the completed factors multiply to
`1 + U V` modulo the horizon.** -/
theorem dvd_criticalLowProduct_sub_one_iff {K : Type*} [CommRing K] (L : ℕ) (U V A B : K[X]) :
    (X : K[X]) ^ L ∣ (criticalLowProduct U V A B - 1) ↔
      (X : K[X]) ^ L ∣ ((A + U) * (B + V) - (1 + U * V)) := by
  rw [criticalLowProduct_sub_one]

/-! ## The tails contribute nothing to the truncation -/

/-- The product of the two tails already vanishes to the horizon. -/
theorem dvd_mul_of_tails {K : Type*} [CommRing K] {m n : ℕ} {U V : K[X]}
    (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V) :
    (X : K[X]) ^ (m + n) ∣ U * V := by
  rw [pow_add]
  exact mul_dvd_mul hU hV

/-- **The fibre condition is that the completed factors are inverse to the horizon.**  The target
`1 + U V` of the exact factorization is `1` modulo the horizon, because each tail already vanishes to
its own order. -/
theorem dvd_criticalLowProduct_sub_one_iff_mul_sub_one {K : Type*} [CommRing K] {m n : ℕ}
    {U V : K[X]} (hU : (X : K[X]) ^ m ∣ U) (hV : (X : K[X]) ^ n ∣ V) (A B : K[X]) :
    (X : K[X]) ^ (m + n) ∣ (criticalLowProduct U V A B - 1) ↔
      (X : K[X]) ^ (m + n) ∣ ((A + U) * (B + V) - 1) := by
  rw [dvd_criticalLowProduct_sub_one_iff]
  constructor <;> intro h
  · have hid : (A + U) * (B + V) - 1
        = ((A + U) * (B + V) - (1 + U * V)) + U * V := by ring
    rw [hid]
    exact dvd_add h (dvd_mul_of_tails hU hV)
  · have hid : (A + U) * (B + V) - (1 + U * V)
        = ((A + U) * (B + V) - 1) - U * V := by ring
    rw [hid]
    exact dvd_sub h (dvd_mul_of_tails hU hV)

/-! ## The two depths enter symmetrically -/

/-- **The compatibility equation is symmetric in the two depths.**  Exchanging the jet with its
reciprocal and the two observed tails gives the same equation. -/
theorem criticalLowProduct_comm {K : Type*} [CommRing K] (U V A B : K[X]) :
    criticalLowProduct U V A B = criticalLowProduct V U B A := by
  simp only [criticalLowProduct]
  ring

/-- The fibre of an observation. -/
def criticalFibre (K : Type*) [CommRing K] (L : ℕ) (U V : K[X]) : Type _ :=
  {p : K[X] × K[X] // (X : K[X]) ^ L ∣ (criticalLowProduct U V p.1 p.2 - 1)}

/-- **The fibre is the same for the two depths.**  Exchanging the jet with its reciprocal is a
bijection between the fibre of an observation and the fibre of the observation with its two tails
exchanged, so the count is symmetric in the two depths. -/
def criticalFibreSwap {K : Type*} [CommRing K] (L : ℕ) (U V : K[X]) :
    criticalFibre K L U V ≃ criticalFibre K L V U where
  toFun p := ⟨(p.1.2, p.1.1), by
    rw [criticalLowProduct_comm]
    exact p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), by
    rw [criticalLowProduct_comm]
    exact p.2⟩
  left_inv p := rfl
  right_inv p := rfl

/-! ## Degrees below the horizon -/

variable {K : Type*} [Field K]

/-- A polynomial of degree below the horizon divisible by the horizon vanishes. -/
theorem eq_zero_of_dvd_of_degree_lt {L : ℕ} {q : K[X]} (hdvd : (X : K[X]) ^ L ∣ q)
    (hdeg : q.degree < (L : ℕ)) : q = 0 := by
  by_contra h0
  have hle := Polynomial.degree_le_of_dvd hdvd h0
  rw [Polynomial.degree_X_pow] at hle
  exact absurd (lt_of_le_of_lt hle hdeg) (lt_irrefl _)

/-! ## The jet is invertible at the origin -/

/-- **A compatible jet has invertible constant term.**  The observed tails vanish at the origin, so
the constant coefficient of the compatibility equation reads `A(0) B(0) = 1`. -/
theorem coeff_zero_add_ne_zero_of_dvd {L : ℕ} (hL : 0 < L) {U V A B : K[X]}
    (hU : U.coeff 0 = 0) (hV : V.coeff 0 = 0)
    (h : (X : K[X]) ^ L ∣ (criticalLowProduct U V A B - 1)) :
    (A + U).coeff 0 ≠ 0 := by
  obtain ⟨r, hr⟩ := h
  have hzero : (criticalLowProduct U V A B - 1).coeff 0 = 0 := by
    rw [hr, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow,
      if_neg (by omega : ¬ ((0 : ℕ) = L)), zero_mul]
  have hcoeff : (criticalLowProduct U V A B - 1).coeff 0
      = A.coeff 0 * B.coeff 0 + A.coeff 0 * V.coeff 0 + U.coeff 0 * B.coeff 0 - 1 := by
    simp only [criticalLowProduct, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.mul_coeff_zero, Polynomial.coeff_one_zero]
  rw [hcoeff, hU, hV] at hzero
  have hAB : A.coeff 0 * B.coeff 0 = 1 := by linear_combination hzero
  rw [Polynomial.coeff_add, hU, add_zero]
  intro hcon
  rw [hcon, zero_mul] at hAB
  exact zero_ne_one hAB

/-! ## The reciprocal low part is determined -/

/-- **Two compatible reciprocal parts of the same jet agree to the horizon.** -/
theorem dvd_sub_of_criticalLowProduct {L : ℕ} {U V A B B' : K[X]} (hA : (A + U).coeff 0 ≠ 0)
    (h : (X : K[X]) ^ L ∣ (criticalLowProduct U V A B - 1))
    (h' : (X : K[X]) ^ L ∣ (criticalLowProduct U V A B' - 1)) :
    (X : K[X]) ^ L ∣ (B - B') := by
  refine dvd_of_mul_dvd_of_coeff_zero_ne_zero hA ?_
  have hid : (A + U) * (B - B')
      = (criticalLowProduct U V A B - 1) - (criticalLowProduct U V A B' - 1) := by
    simp only [criticalLowProduct]
    ring
  rw [hid]
  exact dvd_sub h h'

/-- **The reciprocal low part of a fibre point is determined by its jet low part**, so the fibre is
parametrised by the jet alone. -/
theorem criticalLowProduct_right_unique {L : ℕ} {U V A B B' : K[X]}
    (hA : (A + U).coeff 0 ≠ 0)
    (h : (X : K[X]) ^ L ∣ (criticalLowProduct U V A B - 1))
    (h' : (X : K[X]) ^ L ∣ (criticalLowProduct U V A B' - 1))
    (hdeg : (B - B').degree < (L : ℕ)) :
    B = B' :=
  sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt (dvd_sub_of_criticalLowProduct hA h h') hdeg)

end GaloisForLFunctions.HTGeometry
