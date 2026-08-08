import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Coefficients of the formal jets

The `n`-th coefficient of the `j`-th formal derivative of a power series is the `(n+j)`-th
coefficient of the series times the descending factorial `(n+j)(n+j−1)⋯(n+1)`:

`[X^n] F^{(j)} = [X^{n+j}]F · (n+j)_j`.

This is the shape in which the endpoint expansion sees the coefficient sequence: an endpoint term
attached to the jet `j` and the offset `q` reads `[X^{N−q}]F^{(j)} = (N−q+j)_j · a_{N−q+j}`.

The zeroth jet slot of `formalJetsOver` is the variable `X` itself, whose coefficients vanish away
from degree one; so at degrees at least two that slot contributes nothing to an endpoint sum.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The descending-factorial coefficient formula -/

theorem coeff_iterate_derivative {R : Type*} [CommSemiring R] (F : PowerSeries R) (j : ℕ) :
    ∀ n : ℕ, PowerSeries.coeff n ((⇑(d⁄dX R))^[j] F)
      = PowerSeries.coeff (n + j) F * ((((n + j).descFactorial j : ℕ) : R)) := by
  induction j with
  | zero =>
      intro n
      simp
  | succ j ih =>
      intro n
      rw [Function.iterate_succ_apply', PowerSeries.coeff_derivative, ih (n + 1)]
      have hidx : n + 1 + j = n + (j + 1) := by omega
      rw [hidx]
      have hdesc : (n + (j + 1)).descFactorial (j + 1)
          = (n + 1) * (n + (j + 1)).descFactorial j := by
        rw [Nat.descFactorial_succ]
        congr 1
        omega
      rw [hdesc]
      push_cast
      ring

/-! ## The jets of `formalJetsOver` -/

theorem formalJetsOver_zero {R : Type*} [CommSemiring R] (m : ℕ) (F : PowerSeries R) :
    formalJetsOver m F 0 = PowerSeries.X := by
  rw [formalJetsOver]
  exact Fin.cons_zero _ _

theorem formalJetsOver_succ {R : Type*} [CommSemiring R] (m : ℕ) (F : PowerSeries R)
    (j : Fin (m + 1)) :
    formalJetsOver m F j.succ = (⇑(d⁄dX R))^[(j : ℕ)] F := by
  rw [formalJetsOver]
  exact Fin.cons_succ _ _ j

/-- **The endpoint coefficient of a jet.** -/
theorem coeff_formalJetsOver_succ {R : Type*} [CommSemiring R] (m : ℕ) (F : PowerSeries R)
    (j : Fin (m + 1)) (n : ℕ) :
    PowerSeries.coeff n (formalJetsOver m F j.succ)
      = PowerSeries.coeff (n + (j : ℕ)) F
        * ((((n + (j : ℕ)).descFactorial (j : ℕ) : ℕ) : R)) := by
  rw [formalJetsOver_succ, coeff_iterate_derivative]

/-- Away from degree one the zeroth slot contributes nothing. -/
theorem coeff_formalJetsOver_zero_of_ne {R : Type*} [CommSemiring R] (m : ℕ) (F : PowerSeries R)
    {n : ℕ} (hn : n ≠ 1) : PowerSeries.coeff n (formalJetsOver m F 0) = 0 := by
  rw [formalJetsOver_zero, PowerSeries.coeff_X, if_neg hn]

/-- The jets of `PowerSeries.mk a` read off the sequence directly. -/
theorem coeff_formalJetsOver_mk_succ {R : Type*} [CommSemiring R] (m : ℕ) (a : ℕ → R)
    (j : Fin (m + 1)) (n : ℕ) :
    PowerSeries.coeff n (formalJetsOver m (PowerSeries.mk a) j.succ)
      = a (n + (j : ℕ)) * ((((n + (j : ℕ)).descFactorial (j : ℕ) : ℕ) : R)) := by
  rw [coeff_formalJetsOver_succ, PowerSeries.coeff_mk]

end GaloisForLFunctions.HTGeometry
