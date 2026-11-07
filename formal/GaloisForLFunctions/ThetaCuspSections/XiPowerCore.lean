import GaloisForLFunctions.ThetaCuspSections.ZeroGapResolventBound

/-!
# A power minorant for the complete Xi source

The source-paid resolvent bound makes `Ξ(b)/(1-b²/144)^4` increase on
`[0,12)`. Zero exclusion supplies its sign; the weight vanishes at the
endpoints. The bound retains a radius-twelve core without a Taylor cutoff.
-/

open Complex Set
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower

private theorem hasDerivAt_Xi_real (b : ℝ) : HasDerivAt Xi (deriv Xi b) b := by
  have hh := ((XiC_differentiable (b : ℂ)).hasDerivAt).real_of_complex
  simpa only [XiC_ofReal, XiC_deriv_ofReal, Complex.ofReal_re] using hh

private theorem Xi_abs (b : ℝ) : Xi |b| = Xi b := by
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb]
  · rw [abs_of_neg hb]
    apply Complex.ofReal_injective
    rw [← XiC_ofReal, ← XiC_ofReal, Complex.ofReal_neg, XiC_even]

private theorem Xi_ne_zero_twelve {b : ℝ} (hb : |b| ≤ 12) : Xi b ≠ 0 := by
  intro hh
  apply XiC_ne_zero_of_norm_le_twelve (z := (b : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb)
  rw [XiC_ofReal, hh, Complex.ofReal_zero]

/-- The complete real Xi source stays positive throughout the radius-twelve core. -/
theorem Xi_pos_twelve {b : ℝ} (hb : |b| ≤ 12) : 0 < Xi b := by
  suffices hpos : ∀ t : ℝ, 0 ≤ t → t ≤ 12 → 0 < Xi t by
    simpa only [Xi_abs] using hpos |b| (abs_nonneg b) hb
  intro t ht0 ht
  by_contra hpos
  have hnonpos : Xi t ≤ 0 := not_lt.mp hpos
  have hc : ContinuousOn Xi (Icc 0 t) :=
    fun x _ => (hasDerivAt_Xi_real x).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc' ht0 hc ⟨hnonpos, Xi_zero_pos.le⟩
  have habs : |x| ≤ 12 := by rw [abs_of_nonneg hx.1]; exact hx.2.trans ht
  exact Xi_ne_zero_twelve habs hzero

private theorem Xi_power_derivative_lower {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 12) :
    0 ≤ deriv Xi b * (1 - b ^ 2 / 144) + b / 18 * Xi b := by
  have hX := Xi_pos_twelve (by rw [abs_of_nonneg hb0]; exact hb.le)
  have hw : 0 < 1 - b ^ 2 / 144 := by nlinarith only [hb0, hb]
  have hh := norm_logDeriv_XiC_le_twelve (z := (b : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0] using hb)
  rw [logDeriv_apply, XiC_deriv_ofReal, XiC_ofReal, ← Complex.ofReal_div] at hh
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0] at hh
  have hneg := (abs_le.mp hh).1
  have hd : -(b * Xi b) / (18 * (1 - b ^ 2 / 144)) ≤ deriv Xi b := by
    calc
      _ = (-(b / (18 * (1 - b ^ 2 / 144)))) * Xi b := by ring
      _ ≤ (deriv Xi b / Xi b) * Xi b := mul_le_mul_of_nonneg_right hneg hX.le
      _ = _ := div_mul_cancel₀ _ hX.ne'
  have hpaid := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 18) hw)).mp hd
  nlinarith only [hpaid]

private theorem Xi_ge_power_core_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 12) :
    Xi 0 * (1 - b ^ 2 / 144) ^ 4 ≤ Xi b := by
  let G : ℝ → ℝ := fun x => Xi x / (1 - x ^ 2 / 144) ^ 4
  have hw (x : ℝ) (hx : x ∈ Icc 0 b) : 0 < 1 - x ^ 2 / 144 := by
    have hlt := hx.2.trans_lt hb
    nlinarith only [hx.1, hlt]
  have hD (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivAt G
        (((1 - x ^ 2 / 144) ^ 3 *
          (deriv Xi x * (1 - x ^ 2 / 144) + x / 18 * Xi x)) /
            ((1 - x ^ 2 / 144) ^ 4) ^ 2) x := by
    have hW : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 144) (-x / 72) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub (((hasDerivAt_id x).pow 2).div_const 144) using 1 <;>
        norm_num <;> ring
    apply ((hasDerivAt_Xi_real x).div (hW.pow 4) (pow_ne_zero 4 (hw x hx).ne')).congr_deriv
    norm_num only [Nat.cast_ofNat, Nat.reduceSub]
    ring
  have hmono : MonotoneOn G (Icc 0 b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
      (fun x hx => (hD x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      fun x hx => ?_
    have hxc := interior_subset hx
    rw [(hD x hxc).deriv]
    exact div_nonneg (mul_nonneg (pow_nonneg (hw x hxc).le _)
      (Xi_power_derivative_lower hxc.1 (hxc.2.trans_lt hb))) (sq_nonneg _)
  have hh := hmono (left_mem_Icc.mpr hb0) (right_mem_Icc.mpr hb0) hb0
  change Xi 0 / (1 - 0 ^ 2 / 144) ^ 4 ≤ Xi b / (1 - b ^ 2 / 144) ^ 4 at hh
  norm_num at hh
  exact (le_div_iff₀ (pow_pos (hw b (right_mem_Icc.mpr hb0)) 4)).mp hh

/-- A complete-source power minorant on the whole radius-twelve window. -/
theorem Xi_ge_center_power_core {b : ℝ} (hb : |b| ≤ 12) :
    Xi 0 * (1 - b ^ 2 / 144) ^ 4 ≤ Xi b := by
  rcases eq_or_lt_of_le hb with heq | hlt
  · have hs : b ^ 2 = 144 := by
      have hh := congrArg (fun t : ℝ => t ^ 2) heq
      norm_num only [sq_abs] at hh
      exact hh
    rw [hs]
    norm_num
    exact (Xi_pos_twelve hb).le
  · have hh := Xi_ge_power_core_nonneg (abs_nonneg b) hlt
    simpa only [sq_abs, Xi_abs] using hh

/-- The power core retains an explicit numerical source mass. -/
theorem Xi_ge_power_core {b : ℝ} (hb : |b| ≤ 12) :
    (49 / 100 : ℝ) * (1 - b ^ 2 / 144) ^ 4 ≤ Xi b := by
  have hz : (49 / 100 : ℝ) ≤ Xi 0 := Xi_zero_ge
  exact (mul_le_mul_of_nonneg_right hz (by positivity)).trans (Xi_ge_center_power_core hb)

#print axioms Xi_pos_twelve
#print axioms Xi_ge_center_power_core
#print axioms Xi_ge_power_core

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
