import GaloisForLFunctions.HTGeometry.RittTranslationSliceDescent

/-!
# The eigen slice over an affinely moved generator

In the jet tower of a linearizer the shift acts on the `k`-th jet affinely over the field generated
by the lower ones: `σ y_k = (q/ρ^k)·y_k + (a base-linear combination of the lower jets)`.  Slicing an
eigen-inhomogeneous relation

`σ W = c·W + (α·t + β)`

in such a coordinate `t`, with `σ t = a·t + b`, again forces the denominator to be an eigenvector —
`Q^Φ∘(aX+b) = a^{deg Q}·Q`, because the substitution multiplies leading coefficients by `a^{deg}` —
and the coefficient at the *top* degree of the numerator identity is already informative whenever the
eigenvalue `c` is not one, which is the case in the tower above jet order one.

The result is a single relation in the coefficient field for the leading coefficient of the
numerator, with no case distinction:

`Φ(u)·a^{deg P} = a^{deg Q}·(c·u + α·Q_{deg P − 1} + β·Q_{deg P})`.

This is the step that lowers the number of jet coordinates by one; iterating it walks the tower down
to the base.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The coefficient of the affine inhomogeneity against a polynomial, above the constant term. -/
theorem coeff_affineInhom_mul (α β : K) (Q : K[X]) (m : ℕ) :
    ((C α * X + C β) * Q).coeff (m + 1) = α * Q.coeff m + β * Q.coeff (m + 1) := by
  rw [add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-- **The eigen slice over an affinely moved generator.**  The leading coefficient of the numerator
of a coprime fraction solving `σ W = c·W + (α·t + β)` satisfies a single relation in the coefficient
field. -/
theorem exists_eigen_relation_of_affine_cross (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    Φ P.leadingCoeff * a ^ P.natDegree
      = a ^ Q.natDegree * (c * P.leadingCoeff
          + ((C α * X + C β) * Q).coeff P.natDegree) := by
  classical
  set T : K[X] := C a * X + C b with hT
  have hTdeg : T.natDegree = 1 := natDegree_linear ha
  have hTlead : T.leadingCoeff = a := leadingCoeff_linear ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  set e : ℕ := Q.natDegree with he
  set D : ℕ := P.natDegree with hD
  -- the denominator is an eigenvector with scalar `a ^ e`
  have hcopQ : IsCoprime Q (C c * P + (C α * X + C β) * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right (C α * X + C β)
    have heq : C c * P + Q * (C α * X + C β) = C c * P + (C α * X + C β) * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ T Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ T P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hde : d = a ^ e := by
    have hlead := leadingCoeff_twistComp Φ hTdeg Q
    rw [hd, hQ.leadingCoeff, map_one, hTlead, one_mul, ← he] at hlead
    rw [leadingCoeff_mul, leadingCoeff_C, hQ.leadingCoeff, mul_one] at hlead
    exact hlead
  -- cancel the denominator
  have hnum : twistComp Φ T P
      = C (a ^ e) * (C c * P + (C α * X + C β) * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hd, hde]
    ring
  -- read the top coefficient
  have hLtop : (twistComp Φ T P).coeff D = Φ P.leadingCoeff * a ^ D := by
    have hnd : (twistComp Φ T P).natDegree = D := by
      rw [natDegree_twistComp Φ hTdeg, ← hD]
    have h2 := leadingCoeff_twistComp Φ hTdeg P
    rw [hTlead, ← hD] at h2
    rw [← hnd] at h2 ⊢
    rw [← leadingCoeff]
    exact h2
  have hcoeff := congrArg (fun p : K[X] => p.coeff D) hnum
  rw [hLtop, coeff_C_mul, coeff_add, coeff_C_mul] at hcoeff
  have hlc : P.coeff D = P.leadingCoeff := by rw [leadingCoeff, ← hD]
  rw [hlc] at hcoeff
  exact hcoeff

end GaloisForLFunctions.HTGeometry
