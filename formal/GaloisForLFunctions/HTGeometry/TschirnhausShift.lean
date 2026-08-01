import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

/-!
# The next-to-leading coefficient after a shift

Shifting the variable of a monic polynomial changes its next-to-leading coefficient by the degree
times the shift, because the Hasse derivative of order one below the degree is a linear polynomial
whose slope is the degree and whose constant term is that coefficient.

So over a ring where the degree is invertible one shift removes the next-to-leading coefficient,
which is the centering used to normalise a polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- **The next-to-leading coefficient of a shifted monic polynomial.** -/
theorem taylor_coeff_pred {p : Polynomial R} {d : ℕ} (hd : 1 ≤ d) (hdeg : p.natDegree = d)
    (hm : p.Monic) (r : R) :
    (Polynomial.taylor r p).coeff (d - 1) = (d : R) * r + p.coeff (d - 1) := by
  rw [Polynomial.taylor_coeff]
  have hle : (Polynomial.hasseDeriv (d - 1) p).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_hasseDeriv_le _ _) ?_
    rw [hdeg]
    omega
  have hc0 : (Polynomial.hasseDeriv (d - 1) p).coeff 0 = p.coeff (d - 1) := by
    rw [Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hc1 : (Polynomial.hasseDeriv (d - 1) p).coeff 1 = (d : R) := by
    rw [Polynomial.hasseDeriv_coeff]
    have hsum : 1 + (d - 1) = d := by omega
    rw [hsum, show p.coeff d = 1 from by rw [← hdeg]; exact hm.coeff_natDegree, mul_one]
    have h2 : d.choose (d - 1) = d := by
      rw [Nat.choose_symm (by omega : 1 ≤ d), Nat.choose_one_right]
    rw [h2]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hle)]
  rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
  ring

/-- **A shift changes each coefficient by a multiple of the shift.**  The constant term of the Hasse
derivative is the coefficient itself, and the rest of the evaluation is divisible by the shift.
This is the triangularity of the change of coefficients under a shift. -/
theorem taylor_coeff_eq_add (r : R) (p : Polynomial R) (k : ℕ) :
    ∃ s : R, (Polynomial.taylor r p).coeff k = p.coeff k + r * s := by
  rw [Polynomial.taylor_coeff]
  have hc : (Polynomial.hasseDeriv k p).coeff 0 = p.coeff k := by
    rw [Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hdvd : (r - 0) ∣
      ((Polynomial.hasseDeriv k p).eval r - (Polynomial.hasseDeriv k p).eval 0) :=
    Polynomial.sub_dvd_eval_sub r 0 _
  rw [sub_zero] at hdvd
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨s, ?_⟩
  rw [← hc, Polynomial.coeff_zero_eq_eval_zero]
  linear_combination hs

end GaloisForLFunctions.HTGeometry
