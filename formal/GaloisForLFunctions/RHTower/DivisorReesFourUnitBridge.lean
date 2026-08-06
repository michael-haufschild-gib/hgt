import GaloisForLFunctions.RHTower.DivisorReesBoundaryContraction
import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy
import GaloisForLFunctions.RHTower.ChargeTomography

/-!
# The four-unit budget and the off-line Cauchy energy

The graded boundary symbol assigns exactly one unit of relative trace to each divisor point,
whatever its multiplicity, so the four-unit budget is a four-vertex budget.  The off-line Cauchy
energy of a packet of divisor points, on the other hand, exceeds four units per point as soon as
every point is off the critical line, because each self-term alone contributes more than one.

Putting the two together, the Cauchy energy of any finite family of off-line `xi` zeros is
strictly larger than four times the graded relative trace of that same family.  Off-line zeros
therefore break the four-unit budget at their own energy scale, and the budget — which is a
statement about the boundary symbol, not about any chosen zero — is a criterion for the critical
line.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### Off-line data of a divisor point -/

/-- The off-line offset of a spectral point: its distance from the critical line. -/
def xiOfflineOffset (rho : ℂ) : ℝ := |rho.re - 1 / 2|

/-- The height of a spectral point along the critical direction. -/
def xiOfflineHeight (rho : ℂ) : ℝ := rho.im

/-- The divisor multiplicity of a spectral point. -/
def xiDivisorMultiplicity (rho : ℂ) : ℕ := (analyticOrderAt xi rho).toNat

/-- A point off the critical line has positive offset. -/
theorem xiOfflineOffset_pos {rho : ℂ} (h : rho.re ≠ 1 / 2) : 0 < xiOfflineOffset rho :=
  abs_pos.mpr (sub_ne_zero.mpr h)

/-- A divisor point has offset below one half: the divisor lies inside the critical strip. -/
theorem xiOfflineOffset_lt_half {rho : ℂ} (h : xi rho = 0) : xiOfflineOffset rho < 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit h
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A divisor point carries at least one unit of multiplicity. -/
theorem one_le_xiDivisorMultiplicity {rho : ℂ} (h : xi rho = 0) :
    1 ≤ xiDivisorMultiplicity rho :=
  Nat.one_le_iff_ne_zero.mpr fun hz => (xi_orderToNat_eq_zero_iff rho).mp hz h

/-! ### The bridge -/

/-- **An off-line divisor family exceeds four times its own graded relative trace.**  Each divisor
point contributes exactly one unit of relative trace but strictly more than one unit of Cauchy
self-energy once it is off the critical line, so the four-unit budget of the boundary symbol is
broken by the energy of the very same family. -/
theorem four_mul_trace_lt_xiOfflineCauchyEnergy
    {n : ℕ} (hn : 0 < n) {rho : Fin n → ℂ}
    (hz : ∀ j, xi (rho j) = 0) (hoff : ∀ j, (rho j).re ≠ 1 / 2) :
    4 * Matrix.trace (xiGradedBoundarySymbol rho)
      < finiteOfflineCauchyEnergy (fun j => xiOfflineOffset (rho j))
          (fun j => xiOfflineHeight (rho j)) (fun j => xiDivisorMultiplicity (rho j)) := by
  rw [trace_xiGradedBoundarySymbol]
  simpa using finiteOfflineCauchyEnergy_gt_four_card hn
    (fun j => xiOfflineOffset_pos (hoff j))
    (fun j => xiOfflineOffset_lt_half (hz j))
    (fun j => one_le_xiDivisorMultiplicity (hz j))

/-- No off-line divisor family satisfies the four-unit budget at its own energy. -/
theorem not_xiOfflineCauchyEnergy_le_four_mul_trace
    {n : ℕ} (hn : 0 < n) {rho : Fin n → ℂ}
    (hz : ∀ j, xi (rho j) = 0) (hoff : ∀ j, (rho j).re ≠ 1 / 2) :
    ¬ finiteOfflineCauchyEnergy (fun j => xiOfflineOffset (rho j))
        (fun j => xiOfflineHeight (rho j)) (fun j => xiDivisorMultiplicity (rho j))
      ≤ 4 * Matrix.trace (xiGradedBoundarySymbol rho) :=
  not_le.mpr (four_mul_trace_lt_xiOfflineCauchyEnergy hn hz hoff)

/-- **A single off-line zero already breaks four units.**  The one-vertex boundary graph has
relative trace one, so its budget is exactly four. -/
theorem four_lt_xiOfflineCauchyEnergy_single {rho : ℂ} (hz : xi rho = 0)
    (hoff : rho.re ≠ 1 / 2) :
    4 < finiteOfflineCauchyEnergy (fun _ : Fin 1 => xiOfflineOffset rho)
        (fun _ : Fin 1 => xiOfflineHeight rho) (fun _ : Fin 1 => xiDivisorMultiplicity rho) := by
  have h := four_mul_trace_lt_xiOfflineCauchyEnergy (n := 1) one_pos
    (rho := fun _ : Fin 1 => rho) (fun _ => hz) (fun _ => hoff)
  rwa [trace_xiGradedBoundarySymbol, Fintype.card_fin, Nat.cast_one, mul_one] at h

/-- **The four-unit budget is a criterion for the critical line.**  If every divisor point meets
the budget at its own Cauchy energy, then no divisor point is off the critical line. -/
theorem xi_zero_re_eq_half_of_four_unit_budget
    (h : ∀ rho : ℂ, xi rho = 0 →
      finiteOfflineCauchyEnergy (fun _ : Fin 1 => xiOfflineOffset rho)
        (fun _ : Fin 1 => xiOfflineHeight rho) (fun _ : Fin 1 => xiDivisorMultiplicity rho) ≤ 4)
    {rho : ℂ} (hz : xi rho = 0) : rho.re = 1 / 2 := by
  by_contra hne
  exact absurd (h rho hz) (not_le.mpr (four_lt_xiOfflineCauchyEnergy_single hz hne))

end

end RHTower
