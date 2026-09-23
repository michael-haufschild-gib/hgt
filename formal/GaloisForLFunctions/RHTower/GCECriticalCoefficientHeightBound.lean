import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift

/-!
# The G-CE critical coefficient is the off-line share of Li's first coefficient

The critical Ward coefficient `d = continuedXiAntiCausalWardResponse (1/2)` is the absolutely
convergent sum, over one representative `ρ` of every Schwarz pair of Xi zeros with `Re ρ > 1/2`,
of the pair response `2(1/ρ + 1/ρ̄) = 4 Re(1/ρ) = 4 Re ρ / |ρ|²`.  It is therefore four times the
strict-right part of `Σ_ρ Re(1/ρ)`, the share sum of the zeros at the second pole `s = 0`.

Each off-line zero at height `γ` enters with weight of order `1/γ²`.  Consequently no estimate of
`d` can count zeros: `d ≤ ε` implies only that every strict-right zero satisfies `|ρ|² > 2/ε`.  The
G-CE non-erasing cancellation must be the exact identity `d = 0`, which is the receiver itself.
-/

open Complex

namespace RHTower

noncomputable section

/-- The actual off-line zero carried by a strict-right upper copy, `ρ = 1/2 + (ρ − 1/2)`. -/
def gceOffLineZero (q : XiRightUpperZeroCopy) : ℂ :=
  (1 / 2 : ℂ) + xiRightCenteredZero q.1

/-- The carried point is the divisor point itself. -/
theorem gceOffLineZero_eq_divisorPoint (q : XiRightUpperZeroCopy) :
    gceOffLineZero q = ((q.1.1.1 : XiDivisorSupport) : ℂ) := by
  rw [gceOffLineZero, xiRightCenteredZero, xiSpectralPoint]
  linear_combination (-(((q.1.1.1 : XiDivisorSupport) : ℂ) - 1 / 2)) * Complex.I_sq

/-- The carried point is a zero of the centred `XiC` in the corpus's spectral coordinate. -/
theorem XiC_gceOffLineZero_spectral (q : XiRightUpperZeroCopy) :
    XiC (xiSpectralPoint q.1.1) = 0 ∧
      gceOffLineZero q = (1 / 2 : ℂ) + Complex.I * xiSpectralPoint q.1.1 :=
  ⟨XiC_xiSpectralPoint_eq_zero q.1.1, rfl⟩

theorem gceOffLineZero_re_gt_half (q : XiRightUpperZeroCopy) :
    1 / 2 < (gceOffLineZero q).re := by
  have h := xiRightCenteredZero_re_pos q.1
  simp only [gceOffLineZero, Complex.add_re]
  norm_num
  exact h

theorem gceOffLineZero_ne_zero (q : XiRightUpperZeroCopy) : gceOffLineZero q ≠ 0 := by
  intro h
  have := gceOffLineZero_re_gt_half q
  rw [h, Complex.zero_re] at this
  linarith

/-- One Schwarz pair at the base node is four times the real part of the reciprocal zero. -/
theorem xiAntiCausalWardSchwarzPairResponse_half_eq (q : XiRightUpperZeroCopy) :
    xiAntiCausalWardSchwarzPairResponse q (1 / 2 : ℂ) =
      ((4 * ((gceOffLineZero q)⁻¹).re : ℝ) : ℂ) := by
  rw [xiAntiCausalWardSchwarzPairResponse, xiRightCenteredZero_conj]
  have hconj : ((1 / 2 : ℂ) + (starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹
      = (starRingEnd ℂ) ((gceOffLineZero q)⁻¹) := by
    rw [gceOffLineZero, map_inv₀, map_add]
    have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
    rw [h2]
  rw [hconj]
  show 2 * ((gceOffLineZero q)⁻¹ + (starRingEnd ℂ) ((gceOffLineZero q)⁻¹)) = _
  rw [Complex.add_conj]
  push_cast
  ring

/-- **The G-CE coefficient is the strict-right share sum at the pole `s = 0`.** -/
theorem gceCriticalCoefficient_eq_tsum :
    continuedXiAntiCausalWardResponse (1 / 2 : ℂ) =
      ∑' q : XiRightUpperZeroCopy, ((4 * ((gceOffLineZero q)⁻¹).re : ℝ) : ℂ) := by
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs (by norm_num)]
  exact tsum_congr (fun q => xiAntiCausalWardSchwarzPairResponse_half_eq q)

theorem summable_four_re_inv_gceOffLineZero :
    Summable (fun q : XiRightUpperZeroCopy => 4 * ((gceOffLineZero q)⁻¹).re) := by
  have hw : (0:ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p (1 / 2 : ℂ)).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  refine hreal.congr (fun q => ?_)
  rw [xiAntiCausalWardSchwarzPairResponse_half_eq q, Complex.ofReal_re]

theorem re_gceCriticalCoefficient_eq_tsum :
    (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re =
      ∑' q : XiRightUpperZeroCopy, 4 * ((gceOffLineZero q)⁻¹).re := by
  have hw : (0:ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw, Complex.re_tsum hsum]
  exact tsum_congr (fun q => by rw [xiAntiCausalWardSchwarzPairResponse_half_eq q, Complex.ofReal_re])

theorem four_re_inv_gceOffLineZero_nonneg (q : XiRightUpperZeroCopy) :
    0 ≤ 4 * ((gceOffLineZero q)⁻¹).re := by
  rw [Complex.inv_re]
  have h := gceOffLineZero_re_gt_half q
  have hn : 0 ≤ Complex.normSq (gceOffLineZero q) := Complex.normSq_nonneg _
  have : 0 ≤ (gceOffLineZero q).re / Complex.normSq (gceOffLineZero q) :=
    div_nonneg (by linarith) hn
  linarith

/-- The share of one strict-right zero exceeds `2/|ρ|²`. -/
theorem two_div_norm_sq_lt_share (q : XiRightUpperZeroCopy) :
    2 / ‖gceOffLineZero q‖ ^ (2 : ℕ) < 4 * ((gceOffLineZero q)⁻¹).re := by
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hnorm : 0 < ‖gceOffLineZero q‖ ^ (2 : ℕ) := by
    have := norm_pos_iff.mpr (gceOffLineZero_ne_zero q)
    positivity
  have hre := gceOffLineZero_re_gt_half q
  rw [div_lt_iff₀ hnorm]
  have hcancel : 4 * ((gceOffLineZero q).re / ‖gceOffLineZero q‖ ^ (2 : ℕ)) * ‖gceOffLineZero q‖ ^ (2 : ℕ)
      = 4 * (gceOffLineZero q).re := by
    rw [mul_assoc, div_mul_cancel₀ _ hnorm.ne']
  rw [hcancel]
  linarith

/-- Every single strict-right share is at most the whole coefficient. -/
theorem share_le_re_gceCriticalCoefficient (q : XiRightUpperZeroCopy) :
    4 * ((gceOffLineZero q)⁻¹).re ≤ (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re := by
  rw [re_gceCriticalCoefficient_eq_tsum]
  have hle := summable_four_re_inv_gceOffLineZero.sum_le_tsum ({q} : Finset XiRightUpperZeroCopy)
    (fun p _ => four_re_inv_gceOffLineZero_nonneg p)
  simpa only [Finset.sum_singleton] using hle

/-- **Fixed-point ceiling on the G-CE coefficient.**  Any bound `d ≤ ε` on the critical Ward
coefficient leaves every strict-right zero with `|ρ|² > 2/ε`; it excludes only zeros of bounded
height and can never certify the absence of all of them. -/
theorem gceCriticalCoefficient_le_excludes_low_zeros {ε : ℝ}
    (hε : (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re ≤ ε) (q : XiRightUpperZeroCopy) :
    2 / ε < ‖gceOffLineZero q‖ ^ (2 : ℕ) := by
  have hshare := two_div_norm_sq_lt_share q
  have hterm := share_le_re_gceCriticalCoefficient q
  have hnorm : 0 < ‖gceOffLineZero q‖ ^ (2 : ℕ) := by
    have := norm_pos_iff.mpr (gceOffLineZero_ne_zero q)
    positivity
  have h2 : 2 / ‖gceOffLineZero q‖ ^ (2 : ℕ) < ε := by linarith
  have hεpos : 0 < ε := lt_trans (by positivity) h2
  rw [div_lt_iff₀ hnorm] at h2
  rw [div_lt_iff₀ hεpos]
  linarith

/-- The same ceiling in terms of the modulus: `|ρ| > √(2/ε)`. -/
theorem sqrt_two_div_lt_norm_gceOffLineZero {ε : ℝ}
    (hε : (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re ≤ ε) (q : XiRightUpperZeroCopy) :
    Real.sqrt (2 / ε) < ‖gceOffLineZero q‖ := by
  have h := gceCriticalCoefficient_le_excludes_low_zeros hε q
  have hn : 0 < ‖gceOffLineZero q‖ := norm_pos_iff.mpr (gceOffLineZero_ne_zero q)
  rcases le_or_gt 0 (2 / ε) with h0 | h0
  · rw [← Real.sqrt_sq hn.le]
    exact Real.sqrt_lt_sqrt h0 h
  · rw [Real.sqrt_eq_zero'.mpr h0.le]
    exact hn

end

end RHTower
