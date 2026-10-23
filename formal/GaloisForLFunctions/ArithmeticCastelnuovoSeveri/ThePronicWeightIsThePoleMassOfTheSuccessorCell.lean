import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ResonatorKroneckerLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Monic

/-!
# The pronic weight is the pole mass of the successor cell

On the scaling line the Hecke cycles of `n` and `n + 1` bound the **successor cell**
`[log n, log(n + 1)]`. Its mass under the pole density `e^{−u} du = |e^{−u/2}|² du` — the square of
the pole vector `V` — is the **pronic weight** (`integral_successorCell`)

    ∫_{log n}^{log(n+1)} e^{−u} du = 1/(n(n + 1)),

and the cells tile `[0, log(N + 1)]`, so the pronic weights telescope to the pole mass
`1 − 1/(N + 1)` (`sum_pronic_eq_integral`). This is the Fermi–Nyman cell decomposition of the
Bezout–valuation programme, read in log coordinates: the pronic measure is the pole density read
through the successor cells. Consecutive integers are coprime (Bézout), so the cell's two Hecke
cycles have no prime incidence (`heckeIncidence_succ`): the successor coupling is purely polar and
archimedean.

**Over `𝔽_q[T]` the successor and incidence structures coincide.** For a monic `f` of positive
degree, `f + 1` is monic of the same degree, so `N(f + 1) = N(f)` and the successor cell is
degenerate, of pole mass `0` (`successorCell_functionField`), while `f` and `f + 1` stay coprime:
the successor map preserves every level of the norm grading, i.e. it lies inside the incidence
structure. Over `ℤ` the successor strictly raises the norm, and the pronic weight measures the
transversality of the two structures (`successorCell_integers`).
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- **The pronic weight is the pole mass of the successor cell.** -/
theorem integral_successorCell {n : ℕ} (hn : 1 ≤ n) :
    ∫ u in Real.log n..Real.log (n + 1), Real.exp (-u) = 1 / ((n : ℝ) * (n + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [intervalIntegral.integral_comp_neg (fun u => Real.exp u), integral_exp, Real.exp_neg,
    Real.exp_neg, Real.exp_log hn0, Real.exp_log (by linarith)]
  field_simp
  ring

/-- **The pronic weights telescope to the pole mass.** -/
theorem sum_pronic_eq_integral (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 1)) =
      ∫ u in (0 : ℝ)..Real.log ((N + 1 : ℕ) : ℝ), Real.exp (-u) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => Real.log ((k + 1 : ℕ) : ℝ)) (f := fun u => Real.exp (-u))
    (μ := MeasureTheory.volume) (n := N) fun k _ =>
      (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _
  simp only [zero_add, Nat.cast_one, Real.log_one] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((k + 1 + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    integral_successorCell (by omega)]

theorem integral_pole_mass (N : ℕ) :
    ∫ u in (0 : ℝ)..Real.log (N + 1), Real.exp (-u) = 1 - 1 / ((N : ℝ) + 1) := by
  rw [intervalIntegral.integral_comp_neg (fun u => Real.exp u), integral_exp, neg_zero,
    Real.exp_zero, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- **Over `ℤ` the successor is transverse to the norm grading**: the successor cell has pole mass
`1/(n(n + 1)) > 0`, consecutive integers are coprime, and their Hecke cycles have no prime
incidence. -/
theorem successorCell_integers {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ u in Real.log n..Real.log (n + 1), Real.exp (-u) ∧ Nat.Coprime n (n + 1) ∧
      heckeIncidence n (n + 1) = 0 := by
  refine ⟨?_, Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n), heckeIncidence_succ hn⟩
  rw [integral_successorCell (by omega)]
  positivity

/-- **Over `𝔽_q[T]` the successor lies in the norm grading**: for monic `f` of positive degree,
`f + 1` is monic of the same degree and norm, the successor cell is degenerate, and `f, f + 1` are
coprime. -/
theorem successorCell_functionField {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (hf : f.Monic) (hd : 1 ≤ f.natDegree) :
    (f + 1).Monic ∧ (f + 1).natDegree = f.natDegree ∧
      ∫ u in Real.log ((Fintype.card F : ℝ) ^ f.natDegree)..
        Real.log ((Fintype.card F : ℝ) ^ (f + 1).natDegree), Real.exp (-u) = 0 ∧
      IsCoprime f (f + 1) := by
  have hdeg : (f + 1).natDegree = f.natDegree := by
    rw [show (1 : F[X]) = C 1 from C_1.symm, natDegree_add_C]
  have hmon : (f + 1).Monic := by
    refine hf.add_of_left ?_
    rw [degree_one, degree_eq_natDegree hf.ne_zero]
    exact_mod_cast (show 0 < f.natDegree by omega)
  refine ⟨hmon, hdeg, by rw [hdeg, intervalIntegral.integral_same], ⟨-1, 1, by ring⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
