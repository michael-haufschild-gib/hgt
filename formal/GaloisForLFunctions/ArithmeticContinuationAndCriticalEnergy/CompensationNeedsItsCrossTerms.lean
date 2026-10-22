import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CriticalEnergyFamilies
import GaloisForLFunctions.BezoutValuationIncidence.DampedChebyshevTangentFormOfTheReceiver

/-!
# Compensation needs its cross terms

Compensation is a bound on a *combined signed expression*, never smallness of its separate terms.
This module fixes that discipline in the receiver's own norm.

* The complete signed decomposition `‖u + v‖² = ‖u‖² + ‖v‖² + 2⟪u, v⟫` in the pronic norm, and the
  equivalence of "the complete energy drops to `θ` times the sector energy" with "the signed cross
  term pays the complement's energy".  The cross term is not an error term to be discarded: it is
  where the statement lives.
* Sector energies may not be added.  `m` copies of one sector have complete energy `m²` times a
  sector energy while the sum of the sector energies is `m` times it, so the ratio of complete
  energy to summed sector energy is unbounded over the number of sectors.
* Ratio smallness is not a bound.  A complete energy can tend to infinity while its ratio to a
  sector energy tends to zero, so a proved ratio limit — such as the complementary-sector
  cancellation — is not by itself an admission statement.  What must improve is the rate, in the
  complete norm, with the horizon and cutoff quantifiers intact.
-/

open Finset Set Filter GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The pronic pairing: the signed cross term of the receiver's quadratic form. -/
def pronicPairing (T : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, u n * v n / ((n : ℝ) * ((n : ℝ) + 1))

/-- **The complete signed decomposition.**  No term is an error term. -/
theorem pronicNorm_add_sq (T : ℕ) (u v : ℕ → ℝ) :
    pronicNorm T (fun n => u n + v n) ^ 2 =
      pronicNorm T u ^ 2 + pronicNorm T v ^ 2 + 2 * pronicPairing T u v := by
  simp only [pronicNorm_sq, pronicPairing, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **Compensation is a statement about the combined expression.**  The complete energy falls to
`θ` times the sector energy exactly when the signed cross term pays both the deficit and the
complement's own energy. -/
theorem pronicNorm_add_sq_le_iff (T : ℕ) (u v : ℕ → ℝ) (θ : ℝ) :
    pronicNorm T (fun n => u n + v n) ^ 2 ≤ θ * pronicNorm T u ^ 2 ↔
      2 * pronicPairing T u v ≤ (θ - 1) * pronicNorm T u ^ 2 - pronicNorm T v ^ 2 := by
  rw [pronicNorm_add_sq]
  constructor <;> intro h <;> nlinarith

/-- Scaling a sector by the number of sectors squares in the energy. -/
theorem pronicNorm_const_mul_sq (T : ℕ) (c : ℝ) (v : ℕ → ℝ) :
    pronicNorm T (fun n => c * v n) ^ 2 = c ^ 2 * pronicNorm T v ^ 2 := by
  simp only [pronicNorm_sq, mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- **Sector energies may not be added.**  For any prescribed factor there is a number of identical
sectors whose complete energy exceeds that factor times the sum of the sector energies. -/
theorem exists_sector_count_complete_energy_gt (T : ℕ) {v : ℕ → ℝ}
    (hv : 0 < pronicNorm T v) (C : ℝ) :
    ∃ m : ℕ, C * ((m : ℝ) * pronicNorm T v ^ 2) <
      pronicNorm T (fun n => (m : ℝ) * v n) ^ 2 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max C 0 + 1)
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hC : C < (m : ℝ) := lt_of_le_of_lt (by linarith [le_max_left C 0]) hm
  have hE : 0 < pronicNorm T v ^ 2 := by positivity
  refine ⟨m, ?_⟩
  rw [pronicNorm_const_mul_sq]
  have : C * (m : ℝ) < (m : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- **Ratio smallness is not a bound.**  The quotient of a complete energy by a sector energy can
tend to zero while the complete energy tends to infinity. -/
theorem exists_ratio_tendsto_zero_and_complete_unbounded :
    ∃ complete sector : ℕ → ℝ, (∀ P, 0 < sector P) ∧
      Tendsto (fun P => complete P / sector P) atTop (nhds 0) ∧
        Tendsto complete atTop atTop := by
  refine ⟨fun P => (P : ℝ) + 1, fun P => ((P : ℝ) + 1) ^ 2, fun P => by positivity, ?_, ?_⟩
  · have heq : (fun P : ℕ => ((P : ℝ) + 1) / ((P : ℝ) + 1) ^ 2) =
        fun P : ℕ => 1 / ((P : ℝ) + 1) := by
      funext P
      have hp : ((P : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
