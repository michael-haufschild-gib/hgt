import GaloisForLFunctions.RHTower.ProlateTrueFamilyDistanceRate
import GaloisForLFunctions.RHTower.ProlateSectorSynthesisIsometry

/-!
# The `O(lambda^{-7})` ground-vector rate of the Fourier-odd sector

The parity card's eigenvector statement is the negative-sector analogue of the parent card's
equation `(4)`: after a choice of sign, the normalized constrained ground eigenvector converges to
the normalized zero-integral `h_2`--`h_6` Hermite contrast at rate `O(lambda^{-7})`.

The mechanism is identical to the Fourier-even case, and the sharp leakage ratio supplies the same
power: in the odd sector `D lam j = evenProlateSignedLeakage lam (2j+1)`, so the indices entering
the tail ratio are the signed indices `3` and `5`, and `exists_bound_signedLeakage_ratio_power` at
`n − m = 2` gives `d_3 ≤ C c^{-4} d_5` with `c = 2πlam²`.  One factor of `lam` from the numerator
leaves `lam^{-7}`.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-- **The tail ratio of the negative-sector ladder decays like `lam^{-7}`.** -/
theorem exists_bound_negativeProlateLadder_tail_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℝ in atTop,
      |a * evenProlateSignedLeakage a 3
          / (evenProlateSignedLeakage a 5 - evenProlateSignedLeakage a 3)|
        ≤ K * (a ^ 7)⁻¹ := by
  obtain ⟨C, hC, hCe⟩ := exists_bound_signedLeakage_ratio_power 3 5 (by norm_num)
  refine ⟨C / (8 * Real.pi ^ 4), by positivity, ?_⟩
  have hlt := ladderEnvelope_evenProlateSignedLeakage_negative.lt_succ 1
  filter_upwards [hCe, hlt, eventually_gt_atTop (0 : ℝ),
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (2 * C + 1)]
    with a hratio hstep hapos hcbig
  have hc1 : (1 : ℝ) ≤ signedModeRadialBandwidth a := by linarith
  have hcval : signedModeRadialBandwidth a = 2 * Real.pi * a ^ 2 := rfl
  have hstep' : evenProlateSignedLeakage a 3 < evenProlateSignedLeakage a 5 := by
    simpa using hstep
  have hd3 : (0 : ℝ) ≤ evenProlateSignedLeakage a 3 := evenProlateSignedLeakage_nonneg a 3
  have hd5pos : (0 : ℝ) < evenProlateSignedLeakage a 5 := lt_of_le_of_lt hd3 hstep'
  have hratio2 : evenProlateSignedLeakage a 3
      ≤ C / signedModeRadialBandwidth a ^ 4 * evenProlateSignedLeakage a 5 := by
    simpa using hratio
  have hpow : signedModeRadialBandwidth a ≤ signedModeRadialBandwidth a ^ 4 := by
    have h := pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 4)
    simpa using h
  have hchalf : C / signedModeRadialBandwidth a ^ 4 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    linarith [hpow, hcbig]
  have hgap : evenProlateSignedLeakage a 5 / 2
      ≤ evenProlateSignedLeakage a 5 - evenProlateSignedLeakage a 3 := by
    have hb : evenProlateSignedLeakage a 3 ≤ 1 / 2 * evenProlateSignedLeakage a 5 :=
      le_trans hratio2 (mul_le_mul_of_nonneg_right hchalf hd5pos.le)
    linarith
  have hgappos : (0 : ℝ) < evenProlateSignedLeakage a 5 - evenProlateSignedLeakage a 3 := by
    linarith [hd5pos, hgap]
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hgappos]
  have hnum : a * evenProlateSignedLeakage a 3
      ≤ a * (C / signedModeRadialBandwidth a ^ 4 * evenProlateSignedLeakage a 5) :=
    mul_le_mul_of_nonneg_left hratio2 hapos.le
  have hrhs : C / (8 * Real.pi ^ 4) * (a ^ 7)⁻¹ * (evenProlateSignedLeakage a 5 / 2)
      ≤ C / (8 * Real.pi ^ 4) * (a ^ 7)⁻¹
        * (evenProlateSignedLeakage a 5 - evenProlateSignedLeakage a 3) := by
    refine mul_le_mul_of_nonneg_left hgap ?_
    positivity
  have hid : C / (8 * Real.pi ^ 4) * (a ^ 7)⁻¹ * (evenProlateSignedLeakage a 5 / 2)
      = a * (C / signedModeRadialBandwidth a ^ 4 * evenProlateSignedLeakage a 5) := by
    rw [hcval]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  linarith [hnum, hrhs, hid.le, hid.ge]

/-- **The parity card's eigenvector rate, at the true prolate family.**  The exact constrained
ground eigenvector of the Fourier-odd signed prolate ladder converges, up to sign, to the
normalized `h_2`--`h_6` two-mode seed at rate `O(lambda^{-7})`. -/
theorem constrainedProlateNegative_ground_distance_isBigO :
    ∃ K : ℝ, 0 < K ∧
      (fun lam : ℝ => min
          ‖(‖secularLp (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))‖)⁻¹ •
              secularLp (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))
            - (‖twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)‖)⁻¹ •
                twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)‖
          ‖(‖secularLp (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))‖)⁻¹ •
              secularLp (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
                (infiniteSecularRoot (fun j => evenProlateSignedLeakage lam (2 * j + 1))
                  (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖))
            + (‖twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)‖)⁻¹ •
                twoModeSeedLp (fun j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)‖)
        =O[atTop] fun lam : ℝ => (lam ^ 7)⁻¹ := by
  obtain ⟨K, hK, hKe⟩ := exists_bound_negativeProlateLadder_tail_rate
  set a0 : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 4) with ha0def
  have ha0pos : (0 : ℝ) < a0 := by rw [ha0def]; positivity
  have ha0 : a0 ≠ 0 := ha0pos.ne'
  have henv := ladderEnvelope_evenProlateSignedLeakage_negative
  have hstruct : ∀ᶠ lam : ℝ in atTop,
      (0 ≤ evenProlateSignedLeakage lam (2 * 0 + 1)
        ∧ evenProlateSignedLeakage lam (2 * 0 + 1) < evenProlateSignedLeakage lam (2 * 1 + 1)
        ∧ evenProlateSignedLeakage lam (2 * 1 + 1) < evenProlateSignedLeakage lam (2 * 2 + 1))
      ∧ ∀ j, evenProlateSignedLeakage lam (2 * 2 + 1)
          ≤ evenProlateSignedLeakage lam (2 * (j + 2) + 1) := by
    filter_upwards [henv.mono, henv.lt_succ 0, henv.lt_succ 1] with lam hmono h01 h12
    exact ⟨⟨henv.nonneg lam 0, h01, h12⟩, fun j => hmono 2 (j + 2) (by omega)⟩
  have hl0 : Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * 0 + 1)‖)
      atTop (𝓝 a0) := by
    have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 0
    rwa [constrainedProlateNegativeCoordinate_zero] at h
  have hl1 : Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * 1 + 1)‖) atTop
      (𝓝 (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4))) := by
    have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 1
    rwa [constrainedProlateNegativeCoordinate_one] at h
  have hL0 : ∀ᶠ lam : ℝ in atTop, ‖evenProlateConstraintCoord lam (2 * 0 + 1)‖ ≠ 0 := by
    have h := hl0.eventually (eventually_gt_nhds (by linarith : (0 : ℝ) < a0))
    exact h.mono fun lam hlam => ne_of_gt hlam
  have hL1 : ∀ᶠ lam : ℝ in atTop, ‖evenProlateConstraintCoord lam (2 * 1 + 1)‖ ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) := by positivity
    have h := hl1.eventually (eventually_gt_nhds hpos)
    exact h.mono fun lam hlam => ne_of_gt hlam
  have hL0big : ∀ᶠ lam : ℝ in atTop,
      a0 ^ 2 / 2 ≤ ‖evenProlateConstraintCoord lam (2 * 0 + 1)‖ ^ 2 := by
    have h := (hl0.pow 2).eventually (eventually_gt_nhds (by
      have : (0 : ℝ) < a0 ^ 2 := by positivity
      linarith : a0 ^ 2 / 2 < a0 ^ 2))
    exact h.mono fun lam hlam => hlam.le
  have hKe' : ∀ᶠ lam : ℝ in atTop,
      |lam * evenProlateSignedLeakage lam (2 * 1 + 1)
          / (evenProlateSignedLeakage lam (2 * 2 + 1)
              - evenProlateSignedLeakage lam (2 * 1 + 1))|
        ≤ K * (lam ^ 7)⁻¹ := by
    filter_upwards [hKe] with lam hlam
    simpa using hlam
  refine ⟨(1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) * K, by positivity, ?_⟩
  exact isBigO_inv_pow_seven_of_eventually_le
    (K := (1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) * K)
    (fun lam => le_min (norm_nonneg _) (norm_nonneg _))
    (min_norm_lp_normalize_sub_twoModeSeed_eventually_le
      (D := fun lam j => evenProlateSignedLeakage lam (2 * j + 1))
      (L := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖)
      ha0 hstruct negativeSector_sum negativeSector_bessel hL0 hL1 hL0big hKe')

/-! ## The operator form -/

theorem sectorLeakage_negative_eq (a : ℝ) :
    sectorLeakage a negativeSectorIndex
      = fun j : ℕ => evenProlateSignedLeakage a (2 * j + 1) := rfl

theorem sectorCoord_negative_eq (a : ℝ) :
    sectorCoord a negativeSectorIndex
      = fun j : ℕ => ‖evenProlateConstraintCoord a (2 * j + 1)‖ := rfl

/-- **The parity card's eigenvector statement in the operator's own terms.**  The unit constrained
ground eigenvector of the compressed leakage operator on the Fourier-odd sector converges, up to
sign, to the normalized `h_2`--`h_6` two-mode seed at rate `O(lambda^{-7})`. -/
theorem constrainedProlateNegative_operator_ground_distance_isBigO :
    ∃ C : ℝ, ∀ᶠ lam : ℝ in atTop,
      ∀ f g : evenSubspace,
        HasSum (fun j : ℕ => ((sectorGroundUnit lam negativeSectorIndex j : ℝ) : ℂ)
          • sectorMode lam negativeSectorIndex j) f →
        HasSum (fun j : ℕ => ((sectorSeedUnit lam negativeSectorIndex j : ℝ) : ℂ)
          • sectorMode lam negativeSectorIndex j) g →
        min ‖f - g‖ ‖f + g‖ ≤ C * (lam ^ 7)⁻¹ := by
  obtain ⟨K, hK, hO⟩ := constrainedProlateNegative_ground_distance_isBigO
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨C, ?_⟩
  have hne0 : constrainedProlateNegativeCoordinate 0 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 0).ne'
  have hne1 : constrainedProlateNegativeCoordinate 1 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 1).ne'
  filter_upwards [hC, ladderEnvelope_evenProlateSignedLeakage_negative.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 0).eventually_ne hne0,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with lam hbd hs h0 h1 hlam f g hf hg
  have hσ : Function.Injective negativeSectorIndex := negativeSectorIndex_injective
  have hsumL : Summable fun j : ℕ => sectorCoord lam negativeSectorIndex j ^ 2 :=
    summable_sectorCoord_sq lam hσ
  have hmem : Memℓp (secularVector (sectorLeakage lam negativeSectorIndex)
      (sectorCoord lam negativeSectorIndex)
      (infiniteSecularRoot (sectorLeakage lam negativeSectorIndex)
        (sectorCoord lam negativeSectorIndex))) 2 :=
    memℓp_secularVector hs.1.2.1 hs.1.2.2 hs.2 hsumL h0 h1
  set P : lp (fun _ : ℕ => ℝ) 2 :=
    (‖secularLp (sectorLeakage lam negativeSectorIndex) (sectorCoord lam negativeSectorIndex)
        (infiniteSecularRoot (sectorLeakage lam negativeSectorIndex)
          (sectorCoord lam negativeSectorIndex))‖)⁻¹ •
      secularLp (sectorLeakage lam negativeSectorIndex) (sectorCoord lam negativeSectorIndex)
        (infiniteSecularRoot (sectorLeakage lam negativeSectorIndex)
          (sectorCoord lam negativeSectorIndex)) with hPdef
  set Q : lp (fun _ : ℕ => ℝ) 2 :=
    (‖twoModeSeedLp (sectorCoord lam negativeSectorIndex)‖)⁻¹ •
      twoModeSeedLp (sectorCoord lam negativeSectorIndex) with hQdef
  have hPfun : (fun j : ℕ => ((sectorGroundUnit lam negativeSectorIndex j : ℝ) : ℂ)
      • sectorMode lam negativeSectorIndex j)
      = fun j : ℕ => ((P j : ℝ) : ℂ) • sectorMode lam negativeSectorIndex j := by
    funext j
    rw [hPdef, sectorGroundUnit_eq hmem j]
  have hQfun : (fun j : ℕ => ((sectorSeedUnit lam negativeSectorIndex j : ℝ) : ℂ)
      • sectorMode lam negativeSectorIndex j)
      = fun j : ℕ => ((Q j : ℝ) : ℂ) • sectorMode lam negativeSectorIndex j := by
    funext j
    rw [hQdef, sectorSeedUnit_eq j]
  rw [hPfun] at hf
  rw [hQfun] at hg
  have hsub : ‖f - g‖ = ‖P - Q‖ := norm_sub_eq_of_hasSum_lp hlam hσ P Q hf hg
  have hadd : ‖f + g‖ = ‖P + Q‖ := norm_add_eq_of_hasSum_lp hlam hσ P Q hf hg
  have hbd' : min ‖P - Q‖ ‖P + Q‖ ≤ C * (lam ^ 7)⁻¹ := by
    have hmin : (0 : ℝ) ≤ min ‖P - Q‖ ‖P + Q‖ := le_min (norm_nonneg _) (norm_nonneg _)
    have hpow : (0 : ℝ) < (lam ^ 7)⁻¹ := by positivity
    have hb : ‖min ‖P - Q‖ ‖P + Q‖‖ ≤ C * ‖(lam ^ 7)⁻¹‖ := hbd
    rwa [Real.norm_eq_abs, abs_of_nonneg hmin, Real.norm_eq_abs, abs_of_pos hpow] at hb
  rw [hsub, hadd]
  exact hbd'

end RHTower

end
