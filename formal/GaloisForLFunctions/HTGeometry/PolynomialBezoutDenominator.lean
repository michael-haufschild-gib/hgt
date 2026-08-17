import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content

/-!
# Bezout with a denominator over an integral domain

Two polynomials over an integral domain that are coprime over the fraction field satisfy a Bezout
identity with a nonzero *constant* right-hand side:

`U·P + V·Q = r`,  `r ≠ 0` in the base ring.

Clearing the denominators of a Bezout identity over the fraction field is all it takes.  The
consequence used downstream is that every common divisor of `P` and `Q` divides that constant, so at
any point where the constant is invertible the two polynomials have no common nonunit factor.

This is the algebraic core of the statement that coprimality of analytic germs propagates to nearby
points: after Weierstrass preparation the germs become distinguished polynomials over the germ ring
in one variable fewer, and the constant of the Bezout identity is the obstruction locus.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {D : Type*} [CommRing D] [IsDomain D] {K : Type*} [Field K] [Algebra D K]
  [IsFractionRing D K]

/-- **Bezout with a denominator.**  Polynomials coprime over the fraction field satisfy a Bezout
identity with a nonzero constant on the right. -/
theorem exists_bezout_of_isCoprime_map {P Q : Polynomial D}
    (h : IsCoprime (P.map (algebraMap D K)) (Q.map (algebraMap D K))) :
    ∃ (U V : Polynomial D) (r : D), r ≠ 0 ∧ U * P + V * Q = Polynomial.C r := by
  classical
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨bu, hbu, hU⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors D) (S := K) u
  obtain ⟨bv, hbv, hV⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors D) (S := K) v
  set U₀ : Polynomial D := IsLocalization.integerNormalization (nonZeroDivisors D) u with hU₀
  set V₀ : Polynomial D := IsLocalization.integerNormalization (nonZeroDivisors D) v with hV₀
  have hsmul : ∀ (c : D) (w : Polynomial K),
      c • w = Polynomial.C (algebraMap D K c) * w := by
    intro c w
    rw [Algebra.smul_def]
    rfl
  rw [hsmul] at hU hV
  refine ⟨bv • U₀, bu • V₀, bu * bv, mul_ne_zero (nonZeroDivisors.ne_zero hbu)
    (nonZeroDivisors.ne_zero hbv), ?_⟩
  refine Polynomial.map_injective (algebraMap D K) (IsFractionRing.injective D K) ?_
  have e1 : ((bv • U₀ : Polynomial D)).map (algebraMap D K)
      = Polynomial.C (algebraMap D K bv) * (Polynomial.C (algebraMap D K bu) * u) := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, hU]
  have e2 : ((bu • V₀ : Polynomial D)).map (algebraMap D K)
      = Polynomial.C (algebraMap D K bu) * (Polynomial.C (algebraMap D K bv) * v) := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_C, hV]
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, e1, e2, Polynomial.map_C,
    map_mul]
  calc Polynomial.C (algebraMap D K bv) * (Polynomial.C (algebraMap D K bu) * u)
          * P.map (algebraMap D K)
        + Polynomial.C (algebraMap D K bu) * (Polynomial.C (algebraMap D K bv) * v)
          * Q.map (algebraMap D K)
      = Polynomial.C (algebraMap D K bu) * Polynomial.C (algebraMap D K bv)
        * (u * P.map (algebraMap D K) + v * Q.map (algebraMap D K)) := by ring
    _ = Polynomial.C (algebraMap D K bu * algebraMap D K bv) := by
        rw [huv, mul_one, ← Polynomial.C_mul]

omit [IsDomain D] [IsFractionRing D K] in
/-- **Every common divisor divides the Bezout constant.** -/
theorem dvd_C_of_dvd_of_dvd {P Q U V : Polynomial D} {r : D}
    (hbez : U * P + V * Q = Polynomial.C r) {h : Polynomial D} (hP : h ∣ P) (hQ : h ∣ Q) :
    h ∣ Polynomial.C r := by
  rw [← hbez]
  exact dvd_add (Dvd.dvd.mul_left hP U) (Dvd.dvd.mul_left hQ V)

end GaloisForLFunctions.HTGeometry
