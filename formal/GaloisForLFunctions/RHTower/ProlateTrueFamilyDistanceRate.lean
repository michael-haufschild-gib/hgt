import GaloisForLFunctions.RHTower.ProlateSharpLeakageRatio
import GaloisForLFunctions.RHTower.ProlateNegativeSectorLadder
import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceRate

/-!
# The `O(lambda^{-7})` ground-vector rate at the true prolate family

`min_norm_lp_normalize_sub_twoModeSeed_eventually_le` needs only two things beyond the ladder data:
monotonicity of the leakage sequence, and the single tail ratio

```text
|lam · D 1 / (D 2 − D 1)|  ≤  K (lam^(7 : ℕ))⁻¹ ,
```

which involves the ladder at indices `1` and `2` only — no index-uniform constants.  In the
positive Fourier sector `D lam j = evenProlateSignedLeakage lam (2j)`, so those are the signed
indices `2` and `4`, and the sharp leakage ratio at `n − m = 2` supplies exactly the required power:
`d_2 ≤ C c^{-4} d_4` with `c = 2πlam²` gives `c^{-4} = (2π)^{-4} lam^{-8}`, and one factor of `lam`
from the numerator leaves `lam^{-7}`.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-- **The tail ratio of the positive-sector ladder decays like `lam^{-7}`.** -/
theorem exists_bound_evenProlateLadder_tail_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℝ in atTop,
      |a * evenProlateSignedLeakage a 2
          / (evenProlateSignedLeakage a 4 - evenProlateSignedLeakage a 2)|
        ≤ K * (a ^ (7 : ℕ))⁻¹ := by
  obtain ⟨C, hC, hCe⟩ := exists_bound_signedLeakage_ratio_power 2 4 (by norm_num)
  refine ⟨C / (8 * Real.pi ^ (4 : ℕ)), by positivity, ?_⟩
  have hlt := ladderEnvelope_evenProlateSignedLeakage.lt_succ 1
  filter_upwards [hCe, hlt, eventually_gt_atTop (0 : ℝ),
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (2 * C + 1)]
    with a hratio hstep hapos hcbig
  have hc1 : (1 : ℝ) ≤ signedModeRadialBandwidth a := by linarith
  have hc0 : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  have hcval : signedModeRadialBandwidth a = 2 * Real.pi * a ^ (2 : ℕ) := rfl
  have hstep' : evenProlateSignedLeakage a 2 < evenProlateSignedLeakage a 4 := by
    simpa using hstep
  have hd2 : (0 : ℝ) ≤ evenProlateSignedLeakage a 2 := evenProlateSignedLeakage_nonneg a 2
  have hd4pos : (0 : ℝ) < evenProlateSignedLeakage a 4 := lt_of_le_of_lt hd2 hstep'
  have hratio2 : evenProlateSignedLeakage a 2
      ≤ C / signedModeRadialBandwidth a ^ (4 : ℕ) * evenProlateSignedLeakage a 4 := by
    simpa using hratio
  -- the fourth power dominates the constant
  have hpow : signedModeRadialBandwidth a ≤ signedModeRadialBandwidth a ^ (4 : ℕ) := by
    have h := pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 4)
    simpa using h
  have hchalf : C / signedModeRadialBandwidth a ^ (4 : ℕ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    linarith [hpow, hcbig]
  have hgap : evenProlateSignedLeakage a 4 / 2
      ≤ evenProlateSignedLeakage a 4 - evenProlateSignedLeakage a 2 := by
    have hb : evenProlateSignedLeakage a 2 ≤ 1 / 2 * evenProlateSignedLeakage a 4 :=
      le_trans hratio2 (mul_le_mul_of_nonneg_right hchalf hd4pos.le)
    linarith
  have hgappos : (0 : ℝ) < evenProlateSignedLeakage a 4 - evenProlateSignedLeakage a 2 := by
    linarith [hd4pos, hgap]
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hgappos]
  have hnum : a * evenProlateSignedLeakage a 2
      ≤ a * (C / signedModeRadialBandwidth a ^ (4 : ℕ) * evenProlateSignedLeakage a 4) :=
    mul_le_mul_of_nonneg_left hratio2 hapos.le
  have hrhs : C / (8 * Real.pi ^ (4 : ℕ)) * (a ^ (7 : ℕ))⁻¹ * (evenProlateSignedLeakage a 4 / 2)
      ≤ C / (8 * Real.pi ^ (4 : ℕ)) * (a ^ (7 : ℕ))⁻¹
        * (evenProlateSignedLeakage a 4 - evenProlateSignedLeakage a 2) := by
    refine mul_le_mul_of_nonneg_left hgap ?_
    positivity
  have hid : C / (8 * Real.pi ^ (4 : ℕ)) * (a ^ (7 : ℕ))⁻¹ * (evenProlateSignedLeakage a 4 / 2)
      = a * (C / signedModeRadialBandwidth a ^ (4 : ℕ) * evenProlateSignedLeakage a 4) := by
    rw [hcval]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  linarith [hnum, hrhs, hid.le, hid.ge]

/-- **Equation `(4)` with its rate, at the true prolate family.**  The exact constrained ground
eigenvector of the signed prolate ladder converges to the normalized two-mode seed at rate
`O(lambda^{-7})`. -/
theorem constrainedProlateEven_ground_distance_isBigO :
    ∃ K : ℝ, 0 < K ∧
      (fun lam : ℝ => min
          ‖(‖secularLp (fun j => evenProlateSignedLeakage lam (2 * j))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))‖)⁻¹ •
              secularLp (fun j => evenProlateSignedLeakage lam (2 * j))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))
            - (‖twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)‖)⁻¹ •
                twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)‖
          ‖(‖secularLp (fun j => evenProlateSignedLeakage lam (2 * j))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))‖)⁻¹ •
              secularLp (fun j => evenProlateSignedLeakage lam (2 * j))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖))
            + (‖twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)‖)⁻¹ •
                twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j)‖)‖)
        =O[atTop] fun lam : ℝ => (lam ^ (7 : ℕ))⁻¹ := by
  obtain ⟨K, hK, hKe⟩ := exists_bound_evenProlateLadder_tail_rate
  set a0 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with ha0def
  have ha0pos : (0 : ℝ) < a0 := by rw [ha0def]; positivity
  have ha0 : a0 ≠ 0 := ha0pos.ne'
  have henv := ladderEnvelope_evenProlateSignedLeakage
  have hstruct : ∀ᶠ lam : ℝ in atTop,
      (0 ≤ evenProlateSignedLeakage lam (2 * 0)
        ∧ evenProlateSignedLeakage lam (2 * 0) < evenProlateSignedLeakage lam (2 * 1)
        ∧ evenProlateSignedLeakage lam (2 * 1) < evenProlateSignedLeakage lam (2 * 2))
      ∧ ∀ j, evenProlateSignedLeakage lam (2 * 2)
          ≤ evenProlateSignedLeakage lam (2 * (j + 2)) := by
    filter_upwards [henv.mono, henv.lt_succ 0, henv.lt_succ 1] with lam hmono h01 h12
    exact ⟨⟨henv.nonneg lam 0, h01, h12⟩, fun j => hmono 2 (j + 2) (by omega)⟩
  have hl0 : Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * 0)‖) atTop (𝓝 a0) := by
    have h := tendsto_norm_evenProlateConstraintCoord_atTop 0
    rwa [constrainedProlateHermiteCoordinate_zero_eq] at h
  have hl1 : Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * 1)‖) atTop
      (𝓝 (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))) := by
    have h := tendsto_norm_evenProlateConstraintCoord_atTop 1
    rwa [constrainedProlateHermiteCoordinate_one_eq] at h
  have hL0 : ∀ᶠ lam : ℝ in atTop, ‖evenProlateConstraintCoord lam (2 * 0)‖ ≠ 0 := by
    have h := hl0.eventually (eventually_gt_nhds (by linarith : (0 : ℝ) < a0))
    exact h.mono fun lam hlam => ne_of_gt hlam
  have hL1 : ∀ᶠ lam : ℝ in atTop, ‖evenProlateConstraintCoord lam (2 * 1)‖ ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by positivity
    have h := hl1.eventually (eventually_gt_nhds hpos)
    exact h.mono fun lam hlam => ne_of_gt hlam
  have hL0big : ∀ᶠ lam : ℝ in atTop,
      a0 ^ (2 : ℕ) / 2 ≤ ‖evenProlateConstraintCoord lam (2 * 0)‖ ^ (2 : ℕ) := by
    have h := (hl0.pow 2).eventually (eventually_gt_nhds (by
      have : (0 : ℝ) < a0 ^ (2 : ℕ) := by positivity
      linarith : a0 ^ (2 : ℕ) / 2 < a0 ^ (2 : ℕ)))
    exact h.mono fun lam hlam => hlam.le
  have hKe' : ∀ᶠ lam : ℝ in atTop,
      |lam * evenProlateSignedLeakage lam (2 * 1)
          / (evenProlateSignedLeakage lam (2 * 2) - evenProlateSignedLeakage lam (2 * 1))|
        ≤ K * (lam ^ (7 : ℕ))⁻¹ := by
    filter_upwards [hKe] with lam hlam
    simpa using hlam
  refine ⟨(1 + (16 / a0 ^ (4 : ℕ) + 4 / a0 ^ (2 : ℕ))) * K, by positivity, ?_⟩
  exact isBigO_inv_pow_seven_of_eventually_le
    (K := (1 + (16 / a0 ^ (4 : ℕ) + 4 / a0 ^ (2 : ℕ))) * K)
    (fun lam => le_min (norm_nonneg _) (norm_nonneg _))
    (min_norm_lp_normalize_sub_twoModeSeed_eventually_le
      (D := fun lam j => evenProlateSignedLeakage lam (2 * j))
      (L := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖)
      ha0 hstruct evenProlateLadder_sum evenProlateLadder_bessel hL0 hL1 hL0big hKe')

end RHTower

end
