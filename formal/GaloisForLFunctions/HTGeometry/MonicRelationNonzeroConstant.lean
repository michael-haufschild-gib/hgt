import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div

/-!
# A monic relation with nonzero constant term

In a domain, a nonzero element with a monic relation over the base has one whose constant term is
nonzero: divide out the factor `X` and cancel the element, which the domain permits.  This is the
cancellation step of the last part of the general simple connectedness of the affine line — it turns
a nonzero kernel element of a section into a contradiction.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- In a domain, a nonzero element with a monic relation has one with nonzero constant term. -/
theorem exists_monic_coeff_zero_ne_zero {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] {k : B} (hk : k ≠ 0) :
    ∀ (d : ℕ) (r : A[X]), r.Monic → r.natDegree = d → Polynomial.aeval k r = 0 →
      ∃ r' : A[X], r'.Monic ∧ Polynomial.aeval k r' = 0 ∧ r'.coeff 0 ≠ 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hrm hrd hrz
    by_cases hc : r.coeff 0 = 0
    · have hdvd : (X : A[X]) ∣ r := Polynomial.X_dvd_iff.mpr hc
      obtain ⟨r', rfl⟩ := hdvd
      have hr'm : r'.Monic := by
        have h := hrm
        rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.monic_X.leadingCoeff,
          one_mul] at h
        exact h
      have hr'z : Polynomial.aeval k r' = 0 := by
        have h := hrz
        rw [map_mul, Polynomial.aeval_X] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact absurd h1 hk
        · exact h1
      have hdeg : r'.natDegree < d := by
        rw [← hrd, Polynomial.natDegree_mul (Polynomial.X_ne_zero) hr'm.ne_zero,
          Polynomial.natDegree_X]
        omega
      exact ih _ hdeg r' hr'm rfl hr'z
    · exact ⟨r, hrm, hrz, hc⟩

end GaloisForLFunctions.HTGeometry
