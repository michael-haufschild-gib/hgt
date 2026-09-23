import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePWeightedChebyshevCredit

/-!
# Route P weighted Chebyshev credit as an exact Abel history

Finite summation by parts eliminates the endpoint `psi` term from the only
signed credit in the normalized history variance. The remaining source term
is a square-root-increment-weighted history of `psi(j)-j`, plus a deterministic
lattice baseline. This is exact at every head; no sign estimate is inserted.
-/

open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace RHTower

private theorem routeP_psi_succ (K : ℕ) :
    Chebyshev.psi ((K + 3 : ℕ) : ℝ) =
      Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
        ArithmeticFunction.vonMangoldt (K + 3) := by
  calc
    Chebyshev.psi ((K + 3 : ℕ) : ℝ) =
        ∑ n ∈ Finset.range (K + 2),
          ArithmeticFunction.vonMangoldt (n + 2) :=
      (centroidAtomExcess_vonMangoldt_shift_two (K + 1)).symm
    _ = (∑ n ∈ Finset.range (K + 1),
          ArithmeticFunction.vonMangoldt (n + 2)) +
          ArithmeticFunction.vonMangoldt (K + 3) := by
      rw [Finset.sum_range_succ]
    _ = _ := by rw [centroidAtomExcess_vonMangoldt_shift_two]

noncomputable def routePWeightedPsiAbelLattice (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    Chebyshev.psi ((j + 2 : ℕ) : ℝ) *
      (Real.sqrt ((j + 3 : ℕ) : ℝ) - Real.sqrt ((j + 2 : ℕ) : ℝ))

theorem routePSqrtChebyshevMoment_eq_psi_terminal_sub_abel (K : ℕ) :
    routePSqrtChebyshevMoment K =
      Chebyshev.psi ((K + 2 : ℕ) : ℝ) * Real.sqrt ((K + 2 : ℕ) : ℝ) -
        routePWeightedPsiAbelLattice K := by
  induction K with
  | zero =>
      rw [← centroidAtomExcess_vonMangoldt_shift_two 0]
      simp [routePSqrtChebyshevMoment, routePWeightedPsiAbelLattice]
  | succ K ih =>
      have hA : routePSqrtChebyshevMoment (K + 1) =
          routePSqrtChebyshevMoment K +
            ArithmeticFunction.vonMangoldt (K + 3) *
              Real.sqrt ((K + 3 : ℕ) : ℝ) := by
        unfold routePSqrtChebyshevMoment
        rw [Finset.sum_range_succ]
      have hB : routePWeightedPsiAbelLattice (K + 1) =
          routePWeightedPsiAbelLattice K +
            Chebyshev.psi ((K + 2 : ℕ) : ℝ) *
              (Real.sqrt ((K + 3 : ℕ) : ℝ) -
                Real.sqrt ((K + 2 : ℕ) : ℝ)) := by
        unfold routePWeightedPsiAbelLattice
        rw [Finset.sum_range_succ]
      rw [hA, hB, routeP_psi_succ, ih]
      ring

theorem routePWeightedChebyshevNullCredit_eq_abel_lattice (K : ℕ) :
    routePWeightedChebyshevNullCredit K =
      ((K + 2 : ℕ) : ℝ) * Real.sqrt ((K + 2 : ℕ) : ℝ) / 3 -
        routePWeightedPsiAbelLattice K := by
  unfold routePWeightedChebyshevNullCredit
  rw [routePSqrtChebyshevMoment_eq_psi_terminal_sub_abel]
  ring

noncomputable def routePLatticeBaseline (K : ℕ) : ℝ :=
  ((K + 2 : ℕ) : ℝ) * Real.sqrt ((K + 2 : ℕ) : ℝ) / 3 -
    ∑ j ∈ Finset.range K,
      ((j + 2 : ℕ) : ℝ) *
        (Real.sqrt ((j + 3 : ℕ) : ℝ) - Real.sqrt ((j + 2 : ℕ) : ℝ))

noncomputable def routePWeightedPsiErrorAbelLattice (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    (Chebyshev.psi ((j + 2 : ℕ) : ℝ) - ((j + 2 : ℕ) : ℝ)) *
      (Real.sqrt ((j + 3 : ℕ) : ℝ) - Real.sqrt ((j + 2 : ℕ) : ℝ))

theorem routePWeightedChebyshevNullCredit_eq_baseline_sub_error (K : ℕ) :
    routePWeightedChebyshevNullCredit K =
      routePLatticeBaseline K - routePWeightedPsiErrorAbelLattice K := by
  rw [routePWeightedChebyshevNullCredit_eq_abel_lattice]
  unfold routePLatticeBaseline routePWeightedPsiErrorAbelLattice
    routePWeightedPsiAbelLattice
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

end RHTower
