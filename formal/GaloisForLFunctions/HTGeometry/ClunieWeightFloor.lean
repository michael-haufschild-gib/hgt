import GaloisForLFunctions.HTGeometry.MultivariateRelationGrouping

/-!
# The Clunie weight under a floor on the grouped coefficient

The Clunie weight contains the term `N · log⁺(1/‖groupedCoeff‖)`, which is the only place where the
grouped coefficient's size enters.  A lower bound on that coefficient therefore bounds the whole
weight by data that does not mention it.

This is the point where a minimum-modulus floor and the Clunie separation meet: a floor `ε` replaces
the unknown coefficient size by `log⁺ε⁻¹`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- **A floor on the grouped coefficient bounds the Clunie weight.** -/
theorem clunieWeight_le_of_floor {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hfloor : ε ≤ ‖groupedCoeff S A x N‖) :
    clunieWeight S A x N
      ≤ (∑ e ∈ S, (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (N : ℝ) * Real.posLog ε⁻¹
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  have hg0 : 0 < ‖groupedCoeff S A x N‖ := lt_of_lt_of_le hε hfloor
  have hinv : 1 / ‖groupedCoeff S A x N‖ ≤ ε⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hε hfloor
  have hnn : (0 : ℝ) ≤ 1 / ‖groupedCoeff S A x N‖ := by positivity
  have hmono : Real.posLog (1 / ‖groupedCoeff S A x N‖) ≤ Real.posLog ε⁻¹ :=
    Real.monotoneOn_posLog (Set.mem_Ici.mpr hnn)
      (Set.mem_Ici.mpr (by positivity)) hinv
  have hstep : (N : ℝ) * Real.posLog (1 / ‖groupedCoeff S A x N‖)
      ≤ (N : ℝ) * Real.posLog ε⁻¹ :=
    mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
  rw [clunieWeight]
  linarith

/-- **The last state is bounded by floor data.**  Combining the Clunie estimate with a floor on the
grouped coefficient removes the coefficient's size from the bound. -/
theorem posLog_norm_last_le_of_floor {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → ℂ} {x : Fin (k + 1) → ℂ} {N : ℕ} {ε : ℝ}
    (hN1 : 1 ≤ N) (hN : ∀ e ∈ S, e (Fin.last k) ≤ N)
    (hrel : ∑ e ∈ S, A e * ∏ i, (x i) ^ (e i) = 0)
    (hε : 0 < ε) (hfloor : ε ≤ ‖groupedCoeff S A x N‖) :
    Real.posLog ‖x (Fin.last k)‖
      ≤ (∑ e ∈ S, (Real.posLog ‖A e‖
            + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖))
        + (N : ℝ) * Real.posLog ε⁻¹
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  have htop : groupedCoeff S A x N ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hfloor
    linarith
  exact le_trans (posLog_norm_last_le_clunieWeight hN1 hN hrel htop)
    (clunieWeight_le_of_floor hε hfloor)

end GaloisForLFunctions.HTGeometry
