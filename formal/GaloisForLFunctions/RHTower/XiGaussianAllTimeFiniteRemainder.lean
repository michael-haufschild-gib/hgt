import GaloisForLFunctions.RHTower.XiGaussianUniformCutoff

/-!
# All-time finite phase remainders for every actual Xi Hankel form

One finite spectral window at each order captures the remaining phase loss
uniformly over all positive times and all coefficient vectors. The infinite
tail is absorbed into the actual real reserve. The finite window is exact:
its off-critical energy is not assumed zero or dominated.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

/-- The complete finite-order trace has an all-time relative lower bound with one exact
finite phase remainder and a coefficient-independent spectral cutoff. -/
theorem exists_xiHeatHankelForm_allTime_relative_finite_remainder (N : ℕ)
    (ε : {ε : ℝ // 0 < ε}) :
    ∃ R : ℝ, 0 < R ∧ ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
      (1 - (ε : ℝ)) * xiGaussianRealChannelEnergy
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t -
          xiGaussianHeadPhaseEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t R ≤
              xiHeatHankelForm N a t := by
  obtain ⟨R, hR, htail⟩ := exists_xiGaussianTailPhase_allTime_relative N ε
  refine ⟨R, hR, ?_⟩
  intro a t
  have h := htail a t
  have he := xiGaussianTrace_eq_realChannel_sub_head_sub_tailPhase
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t R
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at he
  nlinarith only [h, he]

/-- Every finite actual Hankel form retains half of an independent coefficient floor at
every positive time, apart from its exact finite off-critical phase remainder. -/
theorem exists_xiHeatHankelForm_allTime_finite_phase_remainder (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧ ∃ R : ℝ, 0 < R ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (c / 2) * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) -
          xiGaussianHeadPhaseEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t R ≤
              xiHeatHankelForm N a t := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  obtain ⟨R, hR, hbound⟩ :=
    exists_xiHeatHankelForm_allTime_relative_finite_remainder N ⟨1 / 2, by positivity⟩
  refine ⟨c, hc, L, hL, R, hR, ?_⟩
  intro a t
  have hf := hfloor a t
  have hb := hbound a t
  change (1 - (1 / 2 : ℝ)) * xiGaussianRealChannelEnergy _ t - _ ≤ _ at hb
  linarith only [hf, hb]

/-- All-time relative tail control for the actual complete three-by-three polynomial. -/
theorem exists_xiHeatThirdTailPhase_allTime_relative (ε : {ε : ℝ // 0 < ε}) :
    ∃ R : ℝ, 0 < R ∧ ∀ (a b c : ℝ) (t : {t : ℝ // 0 < t}),
      xiGaussianTailPhaseEnergy (xiHeatThirdPolynomial a b c) t R ≤
        (ε : ℝ) * xiGaussianRealChannelEnergy (xiHeatThirdPolynomial a b c) t := by
  obtain ⟨R, hR, hbound⟩ := exists_xiGaussianTailPhase_allTime_relative 3 ε
  refine ⟨R, hR, ?_⟩
  intro a b c t
  simpa [xiHeatThirdPolynomial, Finset.sum_range_succ] using
    hbound (fun n => if n = 0 then a else if n = 1 then b else c) t

/-- Complete three-by-three signed bound at every positive time; every mixed coefficient
term remains in both the actual quadratic form and the exact finite phase remainder. -/
theorem exists_xiHeatThirdQuadratic_allTime_finite_phase_remainder :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧ ∃ R : ℝ, 0 < R ∧
      ∀ (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (c₀ / 2) * Real.exp (-(L * (t : ℝ))) * (a ^ 2 + b ^ 2 + c ^ 2) -
          xiGaussianHeadPhaseEnergy (xiHeatThirdPolynomial a b c) t R ≤
            xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, R, hR, hbound⟩ :=
    exists_xiHeatHankelForm_allTime_finite_phase_remainder 3
  refine ⟨c₀, hc₀, L, hL, R, hR, ?_⟩
  intro a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [xiHeatThirdPolynomial, Finset.sum_range_succ] using
    hbound (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
