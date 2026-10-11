import GaloisForLFunctions.RHTower.PaperThetaSchurModeOperator

/-!
# A compact-correction obstruction on the full theta mode space

The native Hilbert--Schmidt bound turns persistent total quartic charge into persistent
individual modes. Every compact correction disappears along a sequence of modes escaping
in stage. The resulting lower bound is uniform over all Schur choices.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Classical
open scoped Topology NNReal ENNReal

/-- Every persistent escaping mode gives a lower bound against arbitrary compact correction. -/
theorem paperThetaSchurModeOperator_le_norm_sub_compact
    (S : PaperThetaSchurFamily) (j : ℕ → PaperThetaSchurMode)
    (hj : Tendsto (fun n => (j n).1) atTop atTop) (c : ℝ)
    (hc : ∀ n, c ≤ paperThetaSchurModeCharge S (j n))
    (K : compactOperatorStarAlgebra PaperThetaSchurSpace) :
    c ≤ ‖paperThetaSchurModeOperator S - K.1‖ := by
  let b := HilbertSchmidt.lpBasis PaperThetaSchurMode
  have hK := tendsto_norm_compact_of_weaklyNull K.1 K.2 (fun n => b (j n))
    (fun n => (b.orthonormal.1 (j n)).le) (paperThetaSchur_basis_weaklyNull j hj)
  have hlim : Tendsto
      (fun n => ‖paperThetaSchurModeOperator S - K.1‖ + ‖K.1 (b (j n))‖)
      atTop (𝓝 ‖paperThetaSchurModeOperator S - K.1‖) := by
    simpa only [norm_zero, add_zero] using
      (tendsto_const_nhds (x := ‖paperThetaSchurModeOperator S - K.1‖)).add hK.norm
  apply ge_of_tendsto' hlim
  intro n
  have hnorm : ‖paperThetaSchurModeOperator S (b (j n))‖ =
      paperThetaSchurModeCharge S (j n) := by
    rw [paperThetaSchurModeOperator_basis, norm_smul, b.orthonormal.1, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperThetaSchurModeCharge_nonneg S (j n))]
  have hsub := norm_sub_norm_le (paperThetaSchurModeOperator S (b (j n))) (K.1 (b (j n)))
  have hop := (paperThetaSchurModeOperator S - K.1).le_opNorm (b (j n))
  rw [b.orthonormal.1, mul_one, sub_apply] at hop
  rw [hnorm] at hsub
  linarith [hc n]

/-- Failure of RH produces a fixed positive mode threshold at every sufficiently late stage,
uniformly over all Schur realizations. -/
theorem paperThetaSchur_eventually_positive_mode_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ S : ThetaSourceStageSchurPacket k,
      ∃ i, δ < sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im := by
  have hn := hRH
  rw [_root_.RHTower.riemannHypothesis_iff_XiC_zeros_real] at hn
  push Not at hn
  obtain ⟨z, hz, him⟩ := hn
  obtain ⟨c, hc, hevent⟩ :=
    eventually_thetaSourceStageSchurPositiveQuarticCharge_gt_of_XiC_zero_im_ne_zero hz him
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let c' : ℝ≥0 := ⟨c, hc.le⟩
  have hc' : c' ≠ 0 := by
    intro h
    have := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
    exact hc.ne' this
  refine ⟨paperThetaSchurModeThreshold c', paperThetaSchurModeThreshold_pos c' hc', N, ?_⟩
  intro k hk S
  exact exists_mode_paperThetaSchurModeThreshold_lt S c' (hN k hk S)

/-- A positive compact-quotient gap survives every Schur choice when RH fails. -/
theorem paperThetaSchur_uniform_compact_gap_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : PaperThetaSchurFamily,
      ∀ K : compactOperatorStarAlgebra PaperThetaSchurSpace,
        δ ≤ ‖paperThetaSchurModeOperator S - K.1‖ := by
  obtain ⟨δ, hδ, N, hN⟩ := paperThetaSchur_eventually_positive_mode_of_not_rh hRH
  refine ⟨δ, hδ, ?_⟩
  intro S K
  choose i hi using fun n : ℕ => hN (N + n) (Nat.le_add_right N n) (S (N + n))
  let j : ℕ → PaperThetaSchurMode := fun n => ⟨N + n, i n⟩
  have hj : Tendsto (fun n => (j n).1) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop M] with n hn
    change M ≤ N + n
    omega
  exact paperThetaSchurModeOperator_le_norm_sub_compact S j hj δ (fun n => (hi n).le) K

end
end RHTower.HedenmalmThetaSource
