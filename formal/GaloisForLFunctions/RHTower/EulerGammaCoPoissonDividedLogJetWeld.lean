import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg

/-!
# Global Euler condensation of the Gamma/co-Poisson interval-jet tower

The local Gamma/co-Poisson interval cell at logarithmic action `-log n`,
weighted by `Λ(n) / log n`, has a complete confluent jet tower.  Summing
that tower over the ordinary integers gives exactly the corresponding jet
of `ζ'/ζ` on `Re s > 1`.

This is the algebraic all-prime weld between the factorial interval receiver
and the von Mangoldt current.  It does not prove continuity of this weld in
the critical Gamma/co-Poisson/Sonin source-normal topology.
-/

open Complex

namespace RHTower

noncomputable section

open LSeries ArithmeticFunction
open scoped LSeries.notation

/-- The `j`-th confluent Gamma/co-Poisson interval jet at the ordinary
integer action `-log n`, with the Euler-logarithm weight `Λ(n) / log n`.

The zero logarithms at `n = 0, 1` cause no exceptional branch: the von
Mangoldt coefficient vanishes there, and division in `ℂ` gives zero. -/
def eulerGammaCoPoissonJetTerm (j n : ℕ) (s : ℂ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n : ℂ) /
      (Real.log (n : ℝ) : ℂ)) *
    iteratedDeriv j
      (fun z =>
        gammaCoPoissonIntervalCell
          (-(Real.log (n : ℝ) : ℂ)) z (s + 1 / 2))
      (s + 1 / 2)

/-- Iterating the Dirichlet logarithmic twist multiplies the von Mangoldt
coefficient by the corresponding power of `log n`. -/
theorem logMul_iterate_vonMangoldt (j n : ℕ) :
    (LSeries.logMul^[j]
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) n =
      (Complex.log n) ^ j * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
      ring

/-- **Termwise Euler--Gamma/co-Poisson jet weld.**  Every weighted
factorial interval jet is the corresponding signed von Mangoldt
`LSeries.term`, divided by its confluent order `j + 1`. -/
theorem eulerGammaCoPoissonJetTerm_eq_LSeries_term
    (j n : ℕ) (s : ℂ) :
    eulerGammaCoPoissonJetTerm j n s =
      ((-1 : ℂ) ^ (j + 1) / (j + 1 : ℂ)) *
        LSeries.term
          (LSeries.logMul^[j]
            (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
          s n := by
  by_cases hn0 : n = 0
  · subst n
    simp [eulerGammaCoPoissonJetTerm, LSeries.term]
  by_cases hn1 : n = 1
  · subst n
    rw [eulerGammaCoPoissonJetTerm]
    simp [LSeries.term, logMul_iterate_vonMangoldt]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hn2 : 2 ≤ n := by omega
  have hlogR : Real.log (n : ℝ) ≠ 0 := by
    exact (Real.log_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn2))).ne'
  have hlogC : (Real.log (n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogR
  rw [eulerGammaCoPoissonJetTerm,
    iteratedDeriv_gammaCoPoissonIntervalCell_self]
  rw [LSeries.term_of_ne_zero hn0, logMul_iterate_vonMangoldt]
  have hcomplexLog :
      Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hnpos.le).symm.trans (by norm_num)
  rw [hcomplexLog, Complex.cpow_def_of_ne_zero hnC]
  rw [hcomplexLog]
  field_simp [hlogC]
  have hexp :
      -(↑(Real.log ↑n) * (s * 2 + 1 - 1) / 2) =
        -(↑(Real.log ↑n) * s) := by ring
  rw [hexp]
  have hcancel :
      Complex.exp (-(↑(Real.log ↑n) * s)) *
          Complex.exp (↑(Real.log ↑n) * s) = 1 := by
    rw [← Complex.exp_add]
    rw [show -(↑(Real.log ↑n) * s) + ↑(Real.log ↑n) * s = 0 by ring,
      Complex.exp_zero]
  calc
    ↑(Λ n) * Complex.exp (-(↑(Real.log ↑n) * s)) *
          (-↑(Real.log ↑n)) ^ (j + 1) *
          Complex.exp (↑(Real.log ↑n) * s) =
        ↑(Λ n) *
          (Complex.exp (-(↑(Real.log ↑n) * s)) *
            Complex.exp (↑(Real.log ↑n) * s)) *
          (-↑(Real.log ↑n)) ^ (j + 1) := by ring
    _ = ↑(Λ n) * (-↑(Real.log ↑n)) ^ (j + 1) := by
      rw [hcancel, mul_one]
    _ = ↑(Λ n) * ↑(Real.log ↑n) * (-1) ^ (j + 1) *
          ↑(Real.log ↑n) ^ j := by rw [neg_pow, pow_succ]; ring

/-- **Global Euler--Gamma/co-Poisson divided-log jet weld.**
On the Euler half-plane, the sum of every weighted confluent factorial
interval jet is exactly `1 / (j + 1)` times the corresponding jet of
`ζ'/ζ`.

For `j = 0`, this says that the global confluence of the interval cells is
the ordinary von Mangoldt logarithmic current `ζ'/ζ`.  Higher `j` retain
the complete factorial conormal tower. -/
theorem tsum_eulerGammaCoPoissonJetTerm_eq_zetaLogDerivJet
    (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, eulerGammaCoPoissonJetTerm j n s =
      iteratedDeriv j zetaLogDeriv s / (j + 1 : ℂ) := by
  calc
    ∑' n : ℕ, eulerGammaCoPoissonJetTerm j n s =
        ∑' n : ℕ,
          (((-1 : ℂ) ^ (j + 1) / (j + 1 : ℂ)) *
            LSeries.term
              (LSeries.logMul^[j]
                (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
              s n) := by
          apply tsum_congr
          intro n
          exact eulerGammaCoPoissonJetTerm_eq_LSeries_term j n s
    _ = ((-1 : ℂ) ^ (j + 1) / (j + 1 : ℂ)) *
          LSeries
            (LSeries.logMul^[j]
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
            s := by
          rw [LSeries, tsum_mul_left]
    _ = iteratedDeriv j zetaLogDeriv s / (j + 1 : ℂ) := by
          rw [iteratedDeriv_zetaLogDeriv_eq_LSeries j hs]
          ring

end

end RHTower
