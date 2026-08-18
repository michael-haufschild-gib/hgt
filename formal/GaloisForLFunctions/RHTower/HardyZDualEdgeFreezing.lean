import GaloisForLFunctions.RHTower.HardyZFrozenDualEdgeCellBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualSeriesFreezing

/-!
# The freezing transfer for the dual edge

The tree prices the cost of freezing the dual weights of the reflected Dirichlet series at one
height.  Multiplying that series by the unit-modulus phase `exp(-iθ(τ))` and taking real parts
transfers the bound verbatim to the real dual edge of the Hardy-`Z` smooth AFE, so the genuine dual
edge differs from its frozen version by at most `(A/x)·|τ − u|` times the `3/2`-power majorant.
-/

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem summable_dualEdgeTermAt {x : ℝ} (hx : 0 < x) (u τ : ℝ) :
    Summable (fun n : ℕ => dualEdgeTermAt x u n τ) := by
  obtain ⟨K, hK, hweight⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hmaj : Summable
      (fun n : ℕ => (2 * (K * (1 + |u|)) / x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ))) :=
    hbase.mul_left _
  refine Summable.of_norm (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_)
  have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hY : (0 : ℝ) < ((n : ℝ) + 1) * x := by positivity
  have hb := hweight u hY
  have hre : |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
      ≤ K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹ :=
    le_trans (Complex.abs_re_le_norm _) hb
  have him : |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|
      ≤ K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹ :=
    le_trans (Complex.abs_im_le_norm _) hb
  have hconst : (Real.sqrt ((n : ℝ) + 1))⁻¹ *
      (2 * (K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹))
      = (2 * (K * (1 + |u|)) / x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have h1 : Real.sqrt ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have h2 : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) * ((n : ℝ) + 1)
        = ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
      nth_rewrite 2 [← Real.rpow_one ((n : ℝ) + 1)]
      rw [← Real.rpow_add hy]
      norm_num
    have hhalf : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
    rw [h1, ← h2]
    field_simp
  rw [Real.norm_eq_abs, ← hconst]
  refine le_trans (abs_dualEdgeTermAt_le x u n τ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

theorem dualEdgeTermAt_sub_eq_re (x u : ℝ) (n : ℕ) (τ : ℝ) :
    dualEdgeTermAt x τ n τ - dualEdgeTermAt x u n τ
      = (Complex.exp (-I * (gammaHardyTheta τ : ℂ)) *
          (((n : ℂ) + 1) ^ (linePt τ - 1) *
            (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)
              - smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)))).re := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
  have h := exp_neg_theta_mul_cpow_linePt_sub_one τ hpos
  rw [hcast] at h
  rw [← mul_assoc, h]
  rw [re_ofReal_mul_exp_neg_I_mul]
  unfold dualEdgeTermAt
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- **The freezing transfer.**  The genuine dual edge differs from the edge with the weight frozen
at height `u` by at most the tree's frozen-series cost. -/
theorem abs_tsum_dualEdge_sub_frozen_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {x u τ : ℝ}, 0 < x → 4 ≤ τ → 4 ≤ u →
      |(∑' n : ℕ, dualEdgeTermAt x τ n τ) - ∑' n : ℕ, dualEdgeTermAt x u n τ|
        ≤ (A / x) * |τ - u| * smoothAFEZetaMajorant (3 / 2) := by
  obtain ⟨A, hA, hfreeze⟩ := exists_norm_smoothAFEZetaDualSeriesWeightError_le
  refine ⟨A, hA, ?_⟩
  intro x u τ hx hτ hu
  set G : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (linePt τ - 1) *
    (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)
      - smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)) with hG
  have hsum₁ := smoothAFEZetaDualWeightedSeries_summable hx τ τ
  have hsum₂ := smoothAFEZetaDualWeightedSeries_summable hx τ u
  have hGsummable : Summable G := by
    refine (hsum₁.sub hsum₂).congr fun n => ?_
    rw [hG]
    ring
  have hphase : Summable (fun n : ℕ => Complex.exp (-I * (gammaHardyTheta τ : ℂ)) * G n) :=
    hGsummable.mul_left _
  have hnorm : ‖∑' n : ℕ, G n‖ ≤ (A / x) * |τ - u| * smoothAFEZetaMajorant (3 / 2) := by
    rw [hG]
    exact hfreeze hx hτ hu
  have hre : (∑' n : ℕ, (dualEdgeTermAt x τ n τ - dualEdgeTermAt x u n τ))
      = (∑' n : ℕ, Complex.exp (-I * (gammaHardyTheta τ : ℂ)) * G n).re := by
    have hmap := Complex.reCLM.map_tsum hphase
    simp only [Complex.reCLM_apply] at hmap
    rw [hmap]
    refine tsum_congr fun n => ?_
    rw [hG]
    exact dualEdgeTermAt_sub_eq_re x u n τ
  have hsub : (∑' n : ℕ, dualEdgeTermAt x τ n τ) - ∑' n : ℕ, dualEdgeTermAt x u n τ
      = ∑' n : ℕ, (dualEdgeTermAt x τ n τ - dualEdgeTermAt x u n τ) :=
    ((summable_dualEdgeTermAt hx τ τ).tsum_sub (summable_dualEdgeTermAt hx u τ)).symm
  rw [hsub, hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [tsum_mul_left, norm_mul, Complex.norm_exp]
  have hzero : (-I * (gammaHardyTheta τ : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hzero, Real.exp_zero, one_mul]
  exact hnorm

end RHTower

end
