import GaloisForLFunctions.RHTower.Sieve.GallagherLemma
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistPerron

/-!
# The Möbius Dirichlet polynomial is the twisted Möbius sum

The polynomial of Gallagher's identity at the Möbius coefficients,

    logPoly μ s w = ∑_{n ∈ s} μ(n) n^{2πiw} ,

is the twisted Möbius sum at frequency `τ = -2πw`.  So the bound `M₁` that Gallagher's split bound
consumes on `|w| ≤ W` is exactly what the twisted contour argument supplies, and no separate estimate
is needed.
-/

namespace RHTower.Sieve

open Complex Finset

/-- **The Möbius Dirichlet polynomial is the twisted Möbius sum.** -/
theorem logPoly_moebius_eq (s : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s w
      = ∑ n ∈ s, moebiusTwist (-(2 * Real.pi * w)) n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [moebiusTwist]
  · have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : Complex.log ((n : ℕ) : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log hnR.le]
    rw [moebiusTwist, Complex.cpow_def_of_ne_zero hn0, hlog]
    congr 1
    rw [show ((2 * Real.pi * (w * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I
        = ((Real.log (n : ℝ) : ℝ) : ℂ)
          * -((((-(2 * Real.pi * w)) : ℝ) : ℂ) * Complex.I) by push_cast; ring]

end RHTower.Sieve
