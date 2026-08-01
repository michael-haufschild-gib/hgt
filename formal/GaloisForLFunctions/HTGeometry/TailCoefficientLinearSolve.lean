import GaloisForLFunctions.HTGeometry.TailCoefficientIndependence
import GaloisForLFunctions.HTGeometry.MvPolynomialPDerivDegree

/-!
# The tail coefficients are linear in the parameter they introduce

The derivative of the `i`-th tail coefficient in the `i`-th parameter is a power of the first
parameter, which no longer involves the `i`-th one.  So subtracting that power times the parameter
leaves something whose derivative in the parameter vanishes, and in characteristic zero that means
the parameter does not occur in it.

Together with the triangularity — the `i`-th coefficient does not involve any later parameter — this
says each tail coefficient is a linear polynomial in the parameter it introduces, with coefficients
in the earlier parameters and leading coefficient a nonzero multiple of a power of the first.  That
is what lets the parameters be solved for one at a time.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The leading coefficient of the `i`-th tail coefficient in the `i`-th parameter. -/
noncomputable def tailLead (K : Type*) [Field K] (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) K :=
  ((n - (i : ℕ) : ℕ) : MvPolynomial (Fin n) K) *
    (MvPolynomial.X (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩ : Fin n)) ^ (n - (i : ℕ) - 1)

omit [CharZero K] in
theorem pderiv_tailCoeff_self (i : Fin n) :
    MvPolynomial.pderiv i (tailCoeff K n i) = tailLead K n i := by
  have h := tailJacobian_diag (K := K) (n := n) i
  rw [tailJacobian, Matrix.of_apply] at h
  exact h

omit [CharZero K] in
theorem pderiv_tailLead {i j : Fin n} (hj : (j : ℕ) ≠ 0) :
    MvPolynomial.pderiv j (tailLead K n i) = 0 := by
  have hne : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩ : Fin n) ≠ j := by
    intro hcon
    exact hj (by rw [← hcon])
  have hC : ((n - (i : ℕ) : ℕ) : MvPolynomial (Fin n) K) =
      MvPolynomial.C (((n - (i : ℕ) : ℕ) : K)) := (map_natCast MvPolynomial.C _).symm
  rw [tailLead, hC, Derivation.leibniz, MvPolynomial.pderiv_C, Derivation.leibniz_pow,
    MvPolynomial.pderiv_X_of_ne hne]
  simp

/-- The part of the `i`-th tail coefficient not carrying the `i`-th parameter. -/
noncomputable def tailRemainder (K : Type*) [Field K] (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) K :=
  tailCoeff K n i - tailLead K n i * MvPolynomial.X i

omit [CharZero K] in
theorem tailCoeff_eq (i : Fin n) :
    tailCoeff K n i = tailLead K n i * MvPolynomial.X i + tailRemainder K n i := by
  rw [tailRemainder]
  ring

omit [CharZero K] in
/-- **The remainder does not involve the parameter, nor any later one.** -/
theorem pderiv_tailRemainder_eq_zero {i j : Fin n} (hi : (i : ℕ) ≠ 0) (hij : (i : ℕ) ≤ (j : ℕ)) :
    MvPolynomial.pderiv j (tailRemainder K n i) = 0 := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  have hcoeff : MvPolynomial.pderiv j (tailCoeff K n i) =
      if (i : ℕ) = (j : ℕ) then tailLead K n i else 0 := by
    by_cases hij' : (i : ℕ) = (j : ℕ)
    · rw [if_pos hij']
      have : i = j := Fin.ext hij'
      rw [← this, pderiv_tailCoeff_self]
    · rw [if_neg hij']
      have hlt : i < j := by
        refine Fin.lt_def.2 ?_
        omega
      have h := tailJacobian_upperTriangular (K := K) (n := n) (i := j) (j := i) hlt
      rw [tailJacobian, Matrix.of_apply] at h
      exact h
  rw [tailRemainder, map_sub, hcoeff, Derivation.leibniz, pderiv_tailLead hj0]
  by_cases hij' : (i : ℕ) = (j : ℕ)
  · have hie : i = j := Fin.ext hij'
    rw [if_pos hij', ← hie, MvPolynomial.pderiv_X_self]
    simp
  · rw [if_neg hij']
    have hne : i ≠ j := fun hcon => hij' (by rw [hcon])
    rw [MvPolynomial.pderiv_X_of_ne hne]
    simp

/-- **The remainder is free of the parameter and of every later one.** -/
theorem degreeOf_tailRemainder_eq_zero {i j : Fin n} (hi : (i : ℕ) ≠ 0) (hij : (i : ℕ) ≤ (j : ℕ)) :
    (tailRemainder K n i).degreeOf j = 0 :=
  degreeOf_eq_zero_of_pderiv_eq_zero (pderiv_tailRemainder_eq_zero hi hij)

omit [CharZero K] in
/-- **The first tail coefficient is a power of the first parameter.** -/
theorem tailCoeff_zero (hn : 0 < n) :
    tailCoeff K n (⟨0, hn⟩ : Fin n) = MvPolynomial.X (⟨0, hn⟩ : Fin n) ^ n := by
  rw [tailCoeff]
  simpa using coeff_zero_tailPoly_pow (K := K) (n := n) hn n

end GaloisForLFunctions.HTGeometry
