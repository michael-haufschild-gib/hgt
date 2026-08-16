import GaloisForLFunctions.HTGeometry.TrailingDegreeSyzygy

/-!
# The conormal functional determines the tangent pair

The conormal pairing sends a low-degree pair `(U, V)` to the functional

```text
(dP, dQ)  ↦  (U · dQ − dP · V).coeff (m + n − 1)
```

on jets with `X^m ∣ dP` and `X^n ∣ dQ`.  Nondegeneracy of that pairing — `eq_zero_of_conormal_vanishing`
— says the only low pair inducing the zero functional is `(0,0)`.  By linearity this upgrades to
determination: two low pairs inducing the same functional are equal, and two low pairs inducing
proportional functionals are proportional.

The proportional form is the one the monodromy argument consumes.  A conormal *line* is what the
geometry supplies, so the tangent pair is pinned only up to scale; the two states over a common
branch value can therefore be scaled to literally the same `(U, V)`, which is the hypothesis of
`criticalState_eq_of_shared_tangent`.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- **A nonzero low pair is seen by some jet.**  The contrapositive of nondegeneracy. -/
theorem exists_conormal_ne_zero {U V : R[X]} {m n : ℕ}
    (hU : U.natDegree < m) (hV : V.natDegree < n) (hne : U ≠ 0 ∨ V ≠ 0) :
    ∃ dP dQ : R[X], (X : R[X]) ^ m ∣ dP ∧ (X : R[X]) ^ n ∣ dQ ∧
      (U * dQ - dP * V).coeff (m + n - 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz := eq_zero_of_conormal_vanishing hU hV fun dP dQ hdP hdQ => hcon dP dQ hdP hdQ
  rcases hne with h | h
  · exact h hz.1
  · exact h hz.2

omit [IsDomain R] in
/-- **The conormal functional determines the tangent pair.**  Two low pairs inducing the same
functional on jets coincide. -/
theorem conormal_determines_tangent {U V U' V' : R[X]} {m n : ℕ}
    (hU : U.natDegree < m) (hV : V.natDegree < n)
    (hU' : U'.natDegree < m) (hV' : V'.natDegree < n)
    (h : ∀ dP dQ : R[X], (X : R[X]) ^ m ∣ dP → (X : R[X]) ^ n ∣ dQ →
      (U * dQ - dP * V).coeff (m + n - 1) = (U' * dQ - dP * V').coeff (m + n - 1)) :
    U = U' ∧ V = V' := by
  have hdU : (U - U').natDegree < m :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le U U') (max_lt hU hU')
  have hdV : (V - V').natDegree < n :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le V V') (max_lt hV hV')
  have hz : (U - U') = 0 ∧ (V - V') = 0 := by
    refine eq_zero_of_conormal_vanishing hdU hdV ?_
    intro dP dQ hdP hdQ
    have hexp : ((U - U') * dQ - dP * (V - V'))
        = (U * dQ - dP * V) - (U' * dQ - dP * V') := by ring
    rw [hexp, Polynomial.coeff_sub, h dP dQ hdP hdQ, sub_self]
  exact ⟨sub_eq_zero.1 hz.1, sub_eq_zero.1 hz.2⟩

omit [IsDomain R] in
/-- **The conormal line determines the tangent pair up to scale.**  A low pair whose functional is
`c` times that of another low pair is `c` times that pair. -/
theorem conormal_determines_tangent_smul {U V U' V' : R[X]} {m n : ℕ} (c : R)
    (hU : U.natDegree < m) (hV : V.natDegree < n)
    (hU' : U'.natDegree < m) (hV' : V'.natDegree < n)
    (h : ∀ dP dQ : R[X], (X : R[X]) ^ m ∣ dP → (X : R[X]) ^ n ∣ dQ →
      (U * dQ - dP * V).coeff (m + n - 1)
        = c * (U' * dQ - dP * V').coeff (m + n - 1)) :
    U = Polynomial.C c * U' ∧ V = Polynomial.C c * V' := by
  refine conormal_determines_tangent hU hV
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c U') hU')
    (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c V') hV') ?_
  intro dP dQ hdP hdQ
  have hexp : (Polynomial.C c * U' * dQ - dP * (Polynomial.C c * V'))
      = Polynomial.C c * (U' * dQ - dP * V') := by ring
  rw [hexp, Polynomial.coeff_C_mul]
  exact h dP dQ hdP hdQ

end GaloisForLFunctions.HTGeometry

end
