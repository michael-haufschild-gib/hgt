import GaloisForLFunctions.HTGeometry.RittDenominatorEigen

/-!
# Coefficientwise eigen relations for a pure scaling twist

When the shift moves the coordinate by a pure scaling, `σ t = a·t`, the twisted substitution acts
diagonally on coefficients: the `k`-th coefficient of `R^Φ(aX)` is `Φ(R_k)·a^k`.  So the two exact
identities produced by coprimality,

`Q^Φ(aX) = a^{deg Q}·Q`,   `P^Φ(aX) = a^{deg Q}·(c·P + (αX + β)·Q)`,

split into one scalar equation per coefficient:

`Φ(Q_k) = a^{deg Q − k}·Q_k`,   `Φ(P_k) = a^{deg Q − k}·(c·P_k + ((αX + β)·Q)_k)`.

Every coefficient of the denominator is therefore a twisted eigenvector with its own scalar, and the
scalars are distinct powers of the multiplier.  A denominator all of whose lower coefficients vanish
is a pure power of the coordinate, and coprimality then bounds the numerator's support.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- The coefficients of a twist by a pure scaling. -/
theorem coeff_twistComp_scaling (Φ : K →+* K) (a : K) (R : K[X]) (k : ℕ) :
    (twistComp Φ (C a * X + C 0) R).coeff k = Φ (R.coeff k) * a ^ k := by
  simp only [twistComp, map_zero, add_zero]
  rw [comp_C_mul_X_coeff, coeff_map]

/-- **Every coefficient of the denominator is a twisted eigenvector.** -/
theorem denominator_coeff_eigen (Φ : K →+* K) {a c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + (C α * X + C β) * Q))
    (k : ℕ) :
    Φ (Q.coeff k) * a ^ k = a ^ Q.natDegree * Q.coeff k := by
  have hden := twistComp_denominator_eq Φ ha hc hQ hcop hcross
  have h := congrArg (fun R : K[X] => R.coeff k) hden
  rw [coeff_twistComp_scaling, coeff_C_mul] at h
  exact h

/-- **Every coefficient of the numerator satisfies its own relation.** -/
theorem numerator_coeff_eigen (Φ : K →+* K) {a c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + (C α * X + C β) * Q))
    (k : ℕ) :
    Φ (P.coeff k) * a ^ k
      = a ^ Q.natDegree * (c * P.coeff k + ((C α * X + C β) * Q).coeff k) := by
  have hnum := twistComp_numerator_eq Φ ha hc hQ hcop hcross
  have h := congrArg (fun R : K[X] => R.coeff k) hnum
  rw [coeff_twistComp_scaling, coeff_C_mul, coeff_add, coeff_C_mul] at h
  exact h

/-- A monic polynomial whose lower coefficients all vanish is a power of the coordinate. -/
theorem monic_eq_X_pow_of_coeff_vanishing {Q : K[X]} (hQ : Q.Monic)
    (hlow : ∀ k, k < Q.natDegree → Q.coeff k = 0) : Q = X ^ Q.natDegree := by
  refine Polynomial.ext fun k => ?_
  rw [coeff_X_pow]
  rcases lt_trichotomy k Q.natDegree with h | h | h
  · rw [if_neg (by omega), hlow k h]
  · rw [if_pos h, h, hQ.coeff_natDegree]
  · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt h]

end GaloisForLFunctions.HTGeometry
