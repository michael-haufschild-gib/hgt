import GaloisForLFunctions.RHTower.GaussCubicTripleConvergence

namespace RHTower

open Filter Topology GaloisForLFunctions
open scoped ENNReal

noncomputable section

/-- The literal hard middle vector in cubic propagation vanishes along every escaping frequency
sequence.  This is the operator-level realization of the three-component conservation law. -/
theorem tendsto_norm_gaussCubicOuterDefectPart_doubleDefect_comp
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
        (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖)
      atTop (nhds 0) := by
  have hbound := tendsto_gaussCubicTripleDefectBound_comp k p hι
  rw [ENNReal.tendsto_nhds_zero] at hbound
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hbound (ENNReal.ofReal ((ε / 2) ^ 2)) (by
      simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hmaster := ofReal_norm_gaussCubicOuterDefectPart_doubleDefect_sq_le
    k p hp (ι n)
  have hofReal : ENNReal.ofReal
      (‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ^ (2 : ℝ))
      ≤ ENNReal.ofReal ((ε / 2) ^ 2) := le_trans hmaster (hN n hn)
  have hle :
      ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ^ (2 : ℝ)
        ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 :
      ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ^ (2 : ℕ)
        ≤ (ε / 2) ^ 2 := by
    have hcast :
        ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
            (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ^ (2 : ℕ) =
          ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
            (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast
        (‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal :
      ‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp (ι n)
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp (ι n))‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

end

end RHTower
