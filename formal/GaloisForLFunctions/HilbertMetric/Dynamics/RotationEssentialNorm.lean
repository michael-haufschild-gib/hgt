import GaloisForLFunctions.HilbertMetric.Dynamics.RotationComposition
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip

/-!
# Essential norm of arbitrary finite rotation-composition sums

Simultaneous recurrence of finitely many unit phases makes every diagonal
value a cluster value at arbitrarily late coordinates. Each such value
survives every compact correction. Hence the essential norm equals the
full operator norm, with no rational-angle restriction.
-/

open Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Dynamics
open HTGeometry _root_.RHTower
noncomputable section

/-- Every exponential-symbol value reappears as a limit along escaping coordinates. -/
theorem phaseRotationSymbol_escaping_cluster {n : ℕ}
    (z : Fin n → Circle) (c : Fin n → ℂ) (k : ℕ) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun m => phaseRotationSymbol z c (j m)) atTop
        (𝓝 (phaseRotationSymbol z c k)) := by
  have hex (m : ℕ) := exists_simultaneous_pow_recurrence
    (fun i => (z i : ℂ)) (fun i => Circle.norm_coe (z i))
    (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity) m
  choose j hj hb using hex
  have hjlim : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have hindex : Tendsto (fun m => k + j m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega) hjlim
  have hphase (i : Fin n) : Tendsto (fun m => (z i : ℂ) ^ j m) atTop (𝓝 1) := by
    have hnorm : Tendsto (fun m => ‖(z i : ℂ) ^ j m - 1‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun m => hb m i)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm)
  refine ⟨fun m => k + j m, hindex, ?_⟩
  have hterm (i : Fin n) (_ : i ∈ Finset.univ) :
      Tendsto (fun m => c i * (z i : ℂ) ^ (k + j m)) atTop
        (𝓝 (c i * (z i : ℂ) ^ k)) := by
    simpa only [pow_add, mul_one] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul (hphase i)))
  exact tendsto_finsetSum Finset.univ hterm

/-- Compact corrections cannot reduce the norm of a finite rotation sum. -/
theorem phaseRotationSum_norm_le_sub_compact {n : ℕ}
    (z : Fin n → Circle) (c : Fin n → ℂ)
    (K : compactOperatorStarAlgebra HardyDisk) :
    ‖phaseRotationSum z c‖ ≤ ‖phaseRotationSum z c - K.val‖ := by
  apply paperBoundedDiagonal_norm_le_of_bound _
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (phaseRotationSymbol_bound z c)
    (norm_nonneg _)
  intro k
  obtain ⟨j, hj, hv⟩ := phaseRotationSymbol_escaping_cluster z c k
  exact paperDiagonalCluster_le_norm_sub_compact _
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (phaseRotationSymbol_bound z c) j hj hv K

/-- The exact essential norm equals the full norm for arbitrary finite disk rotations. -/
theorem phaseRotationSum_compactIdealDistance {n : ℕ}
    (z : Fin n → Circle) (c : Fin n → ℂ) :
    compactIdealDistance (phaseRotationSum z c) = ‖phaseRotationSum z c‖ := by
  apply le_antisymm
  · simpa only [sub_zero] using compactIdealDistance_le (phaseRotationSum z c) 0
      isCompactOperator_zero
  · apply le_compactIdealDistance
    intro K hK
    exact phaseRotationSum_norm_le_sub_compact z c ⟨K, hK⟩

#print axioms phaseRotationSymbol_escaping_cluster
#print axioms phaseRotationSum_norm_le_sub_compact
#print axioms phaseRotationSum_compactIdealDistance
end
end GaloisForLFunctions.HilbertMetric.Dynamics
