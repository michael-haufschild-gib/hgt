import GaloisForLFunctions.HTGeometry.RittAffineSliceResidue

/-!
# Every coefficient of the denominator is an eigenvector of the twist

At the bottom two levels of the jet tower the shift acts on the coordinate by a *pure scaling*:
`σ y_0 = q·y_0` and `σ y_1 = (q/ρ)·y_1`, with no lower-order term.  There the twisted substitution is
diagonal on coefficients, so the eigen-relation `Q^Φ∘(aX) = a^{deg Q}·Q` forced on the denominator by
coprimality is a relation on *every* coefficient separately:

`Φ(Q_j)·a^j = a^{deg Q}·Q_j`.

A denominator with any nonzero coefficient below its degree therefore hands over a nonzero base
element `u` and a nonzero integer `s` with `Φ(u) = a^s·u` — a homogeneous relation whose exponent
cannot cancel.  Only a *monomial* denominator escapes, and being monic that means `Q = X^{deg Q}`.

This is what separates the degenerate branch of the tower descent, where the exponents cancel and
the surviving relation `ψ(u) = u` says nothing, from the informative one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The denominator of a coprime fraction solving an eigen-inhomogeneous relation over a scaled
generator is an eigenvector with scalar `a ^ deg Q`. -/
theorem denominator_eigen_of_scaling_cross (Φ : K →+* K) {a c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X) P * Q
      = twistComp Φ (C a * X) Q * (C c * P + (C α * X + C β) * Q)) :
    twistComp Φ (C a * X) Q = C (a ^ Q.natDegree) * Q := by
  classical
  have hTdeg : (C a * X : K[X]).natDegree = 1 := natDegree_scaleSubst ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcopQ : IsCoprime Q (C c * P + (C α * X + C β) * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right (C α * X + C β)
    have heq : C c * P + Q * (C α * X + C β) = C c * P + (C α * X + C β) * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ (C a * X) Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ (C a * X) P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hde : d = a ^ Q.natDegree := by
    have hj := coeff_eigen_of_twistComp_scale Φ hd Q.natDegree
    rw [hQ.coeff_natDegree, map_one, one_mul, mul_one] at hj
    exact hj.symm
  rw [hd, hde]

/-- **Every denominator coefficient is an eigenvector.** -/
theorem denominator_coeff_eigen_of_scaling_cross (Φ : K →+* K) {a c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X) P * Q
      = twistComp Φ (C a * X) Q * (C c * P + (C α * X + C β) * Q)) (j : ℕ) :
    Φ (Q.coeff j) * a ^ j = a ^ Q.natDegree * Q.coeff j := by
  have h := denominator_eigen_of_scaling_cross Φ ha hc hQ hcop hcross
  exact coeff_eigen_of_twistComp_scale Φ h j

/-- **A non-monomial denominator produces a homogeneous relation with a nonzero exponent.** -/
theorem exists_nondegenerate_relation_of_denominator (Φ : K →+* K) {a c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X) P * Q
      = twistComp Φ (C a * X) Q * (C c * P + (C α * X + C β) * Q))
    {j : ℕ} (hj : j ≠ Q.natDegree) (hQj : Q.coeff j ≠ 0) :
    ∃ (u : K) (s : ℤ), u ≠ 0 ∧ s ≠ 0 ∧ Φ u = a ^ s * u := by
  have h := denominator_coeff_eigen_of_scaling_cross Φ ha hc hQ hcop hcross j
  have hjlt : j < Q.natDegree := lt_of_le_of_ne (le_natDegree_of_ne_zero hQj) hj
  refine ⟨Q.coeff j, (Q.natDegree : ℤ) - j, hQj, by omega, ?_⟩
  rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination h

/-- In the homogeneous case every numerator coefficient is an eigenvector too. -/
theorem numerator_coeff_eigen_of_scaling_cross (Φ : K →+* K) {a c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X) P * Q = twistComp Φ (C a * X) Q * (C c * P)) (j : ℕ) :
    Φ (P.coeff j) * a ^ j = a ^ Q.natDegree * c * P.coeff j := by
  have hcross' : twistComp Φ (C a * X) P * Q
      = twistComp Φ (C a * X) Q * (C c * P + (C 0 * X + C 0) * Q) := by
    rw [hcross]
    simp
  have hQeig := denominator_eigen_of_scaling_cross Φ ha hc hQ hcop hcross'
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hP : twistComp Φ (C a * X) P = C (a ^ Q.natDegree * c) * P := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hQeig, map_mul]
    ring
  exact coeff_eigen_of_twistComp_scale Φ hP j

/-- **A numerator with two nonzero coefficients produces a homogeneous relation with a nonzero
exponent.** -/
theorem exists_nondegenerate_relation_of_numerator (Φ : K →+* K) {a c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X) P * Q = twistComp Φ (C a * X) Q * (C c * P))
    {j j' : ℕ} (hne : j ≠ j') (hPj : P.coeff j ≠ 0) (hPj' : P.coeff j' ≠ 0) :
    ∃ (u : K) (s : ℤ), u ≠ 0 ∧ s ≠ 0 ∧ Φ u = a ^ s * u := by
  have h := numerator_coeff_eigen_of_scaling_cross Φ ha hc hQ hcop hcross j
  have h' := numerator_coeff_eigen_of_scaling_cross Φ ha hc hQ hcop hcross j'
  refine ⟨P.coeff j / P.coeff j', (j' : ℤ) - j, div_ne_zero hPj hPj', by omega, ?_⟩
  have haj : (a : K) ^ j ≠ 0 := pow_ne_zero _ ha
  have haj' : (a : K) ^ j' ≠ 0 := pow_ne_zero _ ha
  have hΦj : Φ (P.coeff j) ≠ 0 := fun h0 => hPj ((map_eq_zero_iff Φ Φ.injective).mp h0)
  have hΦj' : Φ (P.coeff j') ≠ 0 := fun h0 => hPj' ((map_eq_zero_iff Φ Φ.injective).mp h0)
  rw [map_div₀, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
  field_simp
  linear_combination P.coeff j' * h - P.coeff j * h'

end GaloisForLFunctions.HTGeometry
