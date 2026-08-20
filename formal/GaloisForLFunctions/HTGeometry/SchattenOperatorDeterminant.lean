/-
# The order-`p` regularized determinant of an operator is that of its spectrum

Writing the regularized exponent with operator power traces instead of spectral ones defines the
determinant directly on the operator.  Lidskii's identity for every power trace makes the two
agree: the operator determinant is the spectral determinant of the signed greedy eigenvalue
sequence.  This is the identification the completion law needs on the operator side.

Main results:
* `opSchattenDetExp`, `opSchattenDet` — the operator-side order-`p` regularized determinant.
* `opSchattenDetExp_eq_schattenDetExp`, `opSchattenDet_eq_schattenDet` — **the operator
  determinant is the determinant of its spectrum**.
* `opSchattenDet_congr` — **it forgets every trace below `p`** in the operator formulation.
-/
import GaloisForLFunctions.HTGeometry.SchattenSpectralDeterminant
import GaloisForLFunctions.HTGeometry.LidskiiPowerTrace
import GaloisForLFunctions.HTGeometry.TracePowerDeterminant

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The order-`p` regularized exponent of an operator: the power-trace series from `p` upwards. -/
def opSchattenDetExp (p : ℕ) (S : H →L[ℂ] H) (z : ℂ) : ℂ :=
  tracePowerDetExp p (fun m => opTrace (S ^ m)) z

/-- The order-`p` regularized determinant of an operator. -/
def opSchattenDet (p : ℕ) (S : H →L[ℂ] H) (z : ℂ) : ℂ :=
  tracePowerDet p (fun m => opTrace (S ^ m)) z

/-- The spectral power traces of the signed greedy eigenvalues are the operator power traces. -/
theorem schattenTracePower_sgVal_eq_opTrace_pow {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {m : ℕ} (hm : 0 < m) {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) (hS : S ^ m = A ∘L B) :
    schattenTracePower (fun n => ((sgVal S n : ℝ) : ℂ)) m = opTrace (S ^ m) :=
  (opTrace_pow_eq_tsum_sgVal_pow hcpt hsym hm hA hB hS).symm

/-- **The operator regularized exponent is the spectral one.** -/
theorem opSchattenDetExp_eq_schattenDetExp {p : ℕ} (hp : 0 < p) {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric)
    (hfac : ∀ m : ℕ, p ≤ m → ∃ A B : H →L[ℂ] H,
      A.IsHilbertSchmidt ∧ B.IsHilbertSchmidt ∧ S ^ m = A ∘L B) (z : ℂ) :
    opSchattenDetExp p S z = schattenDetExp p (fun n => ((sgVal S n : ℝ) : ℂ)) z := by
  rw [opSchattenDetExp, tracePowerDetExp, schattenDetExp]
  refine tsum_congr fun k => ?_
  obtain ⟨A, B, hA, hB, hS⟩ := hfac (k + p) (Nat.le_add_left p k)
  rw [schattenTracePower_sgVal_eq_opTrace_pow hcpt hsym
    (lt_of_lt_of_le hp (Nat.le_add_left p k)) hA hB hS]

/-- **The operator determinant is the determinant of its spectrum.** -/
theorem opSchattenDet_eq_schattenDet {p : ℕ} (hp : 0 < p) {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric)
    (hfac : ∀ m : ℕ, p ≤ m → ∃ A B : H →L[ℂ] H,
      A.IsHilbertSchmidt ∧ B.IsHilbertSchmidt ∧ S ^ m = A ∘L B) (z : ℂ) :
    opSchattenDet p S z = schattenDet p (fun n => ((sgVal S n : ℝ) : ℂ)) z := by
  show Complex.exp (- opSchattenDetExp p S z)
      = Complex.exp (- schattenDetExp p (fun n => ((sgVal S n : ℝ) : ℂ)) z)
  rw [opSchattenDetExp_eq_schattenDetExp hp hcpt hsym hfac z]

/-- **The operator determinant forgets every trace below `p`.**  Two operators whose power traces
agree from `p` upwards have the same order-`p` regularized determinant. -/
theorem opSchattenDet_congr {p : ℕ} {S T : H →L[ℂ] H}
    (h : ∀ m : ℕ, p ≤ m → opTrace (S ^ m) = opTrace (T ^ m)) (z : ℂ) :
    opSchattenDet p S z = opSchattenDet p T z :=
  tracePowerDet_congr h z

end

end GaloisForLFunctions.HTGeometry
