import GaloisForLFunctions.HTGeometry.StrelitzJetCurveMatchedDichotomy

/-!
# Quadratic decay of selected Strelitz jet-curve roots

The Wiman second-jet estimate and absolute proximity of a selected algebraic root imply that root is
little-o of the square of the central index.  This is the quantitative input that restricts the
matched Newton slope before the global maximum-modulus continuation argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- A selected Strelitz root inherits the quadratic little-o bound of the observed second jet. -/
theorem tendsto_strelitzJetCurveRoot_div_centralIndex_sq_zero
    {ν : ℕ → ℕ} {v root : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hv : ∀ n : ℕ, ‖v n‖ ≤ (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ (2 : ℕ))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    Tendsto (fun n => ‖root n‖ / (ν n : ℝ) ^ (2 : ℕ)) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge b
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h := tendsto_inv_atTop_zero.comp htop
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) at h
    simpa only [one_div] using h
  have hsum : Tendsto (fun n => ‖v n - root n‖ + 1 / ((n : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [zero_add] using hclose.add hinv
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n => div_nonneg (norm_nonneg _) (sq_nonneg _)) ?_ hsum
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hνTop 1
  filter_upwards [eventually_ge_atTop N] with n hn
  have hνnat : 1 ≤ ν n := hN n hn
  have hν : (1 : ℝ) ≤ (ν n : ℝ) := by exact_mod_cast hνnat
  have hνsq : (1 : ℝ) ≤ (ν n : ℝ) ^ (2 : ℕ) := by nlinarith
  have hνsqPos : (0 : ℝ) < (ν n : ℝ) ^ (2 : ℕ) := lt_of_lt_of_le zero_lt_one hνsq
  have hroot : ‖root n‖ ≤ ‖v n - root n‖ + ‖v n‖ := by
    have h := norm_add_le (-(v n - root n)) (v n)
    calc
      ‖root n‖ ≤ ‖root n - v n‖ + ‖v n‖ := by
        simpa only [neg_sub, sub_add_cancel] using h
      _ = ‖v n - root n‖ + ‖v n‖ := by rw [norm_sub_rev]
  have hcloseDiv : ‖v n - root n‖ / (ν n : ℝ) ^ (2 : ℕ) ≤ ‖v n - root n‖ := by
    exact div_le_self (norm_nonneg _) hνsq
  have hvDiv : ‖v n‖ / (ν n : ℝ) ^ (2 : ℕ) ≤ 1 / ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hνsqPos]
    exact hv n
  calc
    ‖root n‖ / (ν n : ℝ) ^ (2 : ℕ)
        ≤ (‖v n - root n‖ + ‖v n‖) / (ν n : ℝ) ^ (2 : ℕ) :=
          div_le_div_of_nonneg_right hroot hνsqPos.le
    _ = ‖v n - root n‖ / (ν n : ℝ) ^ (2 : ℕ) + ‖v n‖ / (ν n : ℝ) ^ (2 : ℕ) := by ring
    _ ≤ ‖v n - root n‖ + 1 / ((n : ℝ) + 1) := add_le_add hcloseDiv hvDiv

end

end GaloisForLFunctions.HTGeometry
