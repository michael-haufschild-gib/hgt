import GaloisForLFunctions.HTGeometry.PaperRotationWeylOperators
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Integer return times for every rotation phase

Compactness of the unit circle supplies arbitrarily large integer returns. No irrationality
condition is needed: differences of distant members of a Cauchy subsequence give the returns.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

private theorem phase_return_large (t : ℝ) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, N ≤ n ∧ ‖paperRotationPhase ((n : ℝ) * t) - 1‖ < ε := by
  let f : ℕ → ℂ := fun n => paperRotationPhase ((n : ℝ) * t)
  have hm : ∀ n, f n ∈ Metric.sphere (0 : ℂ) 1 := by
    intro n
    simp [f]
  obtain ⟨z, _, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hm
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
  have hgap : φ K + N ≤ φ (K + N) := by
    induction N with
    | zero => simp
    | succ n ih =>
        have hh := hφ (show K + n < K + (n + 1) by omega)
        omega
  have hle : φ K ≤ φ (K + N) := by omega
  refine ⟨φ (K + N) - φ K, by omega, ?_⟩
  have he : ‖paperRotationPhase (((φ (K + N) - φ K : ℕ) : ℝ) * t) - 1‖ =
      dist (f (φ (K + N))) (f (φ K)) := by
    rw [Nat.cast_sub hle, dist_eq_norm]
    calc
      ‖paperRotationPhase (((φ (K + N) : ℝ) - φ K) * t) - 1‖ =
          ‖(paperRotationPhase (((φ (K + N) : ℝ) - φ K) * t) - 1) *
            paperRotationPhase ((φ K : ℝ) * t)‖ := by
              rw [norm_mul, paperRotationPhase_norm, mul_one]
      _ = ‖f (φ (K + N)) - f (φ K)‖ := by
        rw [sub_mul, one_mul, ← paperRotationPhase_add]
        congr 2
        congr 1
        ring
  rw [he]
  exact hK (K + N) (by omega) K le_rfl

/-- Every rotation admits integer return times escaping to infinity. -/
theorem exists_paperRotationReturnSequence (t : ℝ) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
      Tendsto (fun j => paperRotationPhase ((n j : ℝ) * t)) atTop (𝓝 1) := by
  choose n hn hnorm using fun j : ℕ =>
    phase_return_large t j (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨n, tendsto_atTop_mono hn tendsto_id, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun j => norm_nonneg _) (fun j => (hnorm j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Fixed integer return sequence for the given phase. -/
def paperRotationReturnTime (t : ℝ) : ℕ → ℕ :=
  (exists_paperRotationReturnSequence t).choose

theorem paperRotationReturnTime_tendsto (t : ℝ) :
    Tendsto (paperRotationReturnTime t) atTop atTop :=
  (exists_paperRotationReturnSequence t).choose_spec.1

theorem paperRotationReturnPhase_tendsto (t : ℝ) :
    Tendsto (fun j => paperRotationPhase ((paperRotationReturnTime t j : ℝ) * t))
      atTop (𝓝 1) :=
  (exists_paperRotationReturnSequence t).choose_spec.2

end

end GaloisForLFunctions.HTGeometry
