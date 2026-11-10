import GaloisForLFunctions.InfiniteRankPurityTheory.TheIndexBoundIsAttained
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum

/-!
# The exceptional parameter is born at `4π e^{−γ}`

The cleared constant term `(s − 1) ξ(2s) Y^s + s ξ(2s − 1) Y^{1−s}` of the Eisenstein series is of
index one for `Y ≥ 1`: at most one zero right of the line, and it is real. This module decides for
which heights the zero exists.

**Theorem** (`exists_exceptionalParameter_iff`). For `Y ≥ 1` the cleared constant term has a zero
right of the line `Re s = ½` exactly when `Y > 4π e^{−γ}`.

So for `1 ≤ Y ≤ 4π e^{−γ}` the constant term is pure: all its zeros lie on the line
(`re_eq_half_of_constantTerm_eq_zero`). Above the threshold it is pure off the real axis with one
real exceptional pair.

**Proof.** On the real axis the sign of the constant term at `x ∈ (½, 1)` is the sign of
`D_Y(x) = x ξ(2x − 1) − (1 − x) ξ(2x) Y^{2x−1}` (`defect`), which vanishes at `x = ½` for every `Y`
and decreases in `Y`.
- `ξ'(1) = ½ + γ/4 − ¼ log 4π` and `ξ'(0) = −ξ'(1)` (`hasDerivAt_xiReal_one`,
  `hasDerivAt_xiReal_zero`), so `D_Y'(½) = ½ (log(4π e^{−γ}) − log Y)` (`hasDerivAt_defect_half`).
- Above the threshold `D_Y < 0` just right of `½`, and the constant term is `½` at `s = 1`: a zero
  lies between.
- Below the threshold a zero `x₁` at height `Y` gives, at a height `Y₂` between `Y` and the
  threshold, `D_{Y₂}(x₁) < 0` and `D_{Y₂} > 0` just right of `½`: two zeros right of the line, one
  on each side of `x₁`, against the index bound.
- At the threshold a zero `x₁` is excluded by a second point `x' ∈ (½, x₁)`: it is a zero at
  exactly one height `Y'`, and each of `Y' < `, `=`, `>` the threshold gives a zero below the
  threshold or two zeros at one height.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower

noncomputable section

/-- The threshold height `4π e^{−γ}`. -/
def threshold : ℝ := 4 * Real.pi * Real.exp (-Real.eulerMascheroniConstant)

theorem threshold_pos : 0 < threshold := by
  unfold threshold
  positivity

theorem log_threshold :
    Real.log threshold = Real.log (4 * Real.pi) - Real.eulerMascheroniConstant := by
  rw [threshold, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem one_lt_threshold : 1 < threshold := by
  have hγ : Real.eulerMascheroniConstant < 1 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have h1 : Real.exp (-1) < Real.exp (-Real.eulerMascheroniConstant) :=
    Real.exp_lt_exp.mpr (by linarith)
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have h2 : (1 : ℝ) / 3 < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (Real.exp_pos 1)).mpr he
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  unfold threshold
  nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]

/-! ### The derivative of `ξ` at `0` and `1` -/

/-- `ξ'(1) = ½ + γ/4 − ¼ log 4π`. -/
def xiDerivOne : ℝ := 1 / 2 + Real.eulerMascheroniConstant / 4 - Real.log (4 * Real.pi) / 4

theorem xiReal_zero : xiReal 0 = 1 / 2 := by
  rw [xiReal, Complex.ofReal_zero, xi_zero]
  norm_num

theorem xiReal_one : xiReal 1 = 1 / 2 := by
  rw [xiReal, Complex.ofReal_one, xi_one]
  norm_num

theorem xiReal_one_sub (t : ℝ) : xiReal (1 - t) = xiReal t := by
  rw [xiReal, xiReal]
  push_cast
  rw [xi_one_sub]

theorem hasDerivAt_xiReal_one : HasDerivAt xiReal xiDerivOne 1 := by
  have h : HasDerivAt xi (completedRiemannZeta₀ 1 / 2) ((1 : ℝ) : ℂ) := by
    simpa using hasDerivAt_xi_one_archimedeanGenusZeroSum
  have hr := h.real_of_complex
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  have hval : (completedRiemannZeta₀ 1 / 2).re = xiDerivOne := by
    rw [_root_.completedRiemannZeta₀_one, hlog, xiDerivOne]
    have hcast : (((Real.eulerMascheroniConstant : ℂ) - ((Real.log (4 * Real.pi) : ℝ) : ℂ)) / 2 +
        1) / 2 = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1) / 2 : ℝ) := by
      push_cast
      rfl
    rw [hcast, Complex.ofReal_re]
    ring
  rw [hval] at hr
  exact hr

theorem hasDerivAt_xiReal_zero : HasDerivAt xiReal (-xiDerivOne) 0 := by
  have h1 : HasDerivAt xiReal xiDerivOne (1 - (0 : ℝ)) := by
    rw [sub_zero]
    exact hasDerivAt_xiReal_one
  have hin : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hcomp : HasDerivAt (fun t : ℝ => xiReal (1 - t)) (xiDerivOne * -1) 0 := h1.comp 0 hin
  rw [show (fun t : ℝ => xiReal (1 - t)) = xiReal from funext xiReal_one_sub] at hcomp
  simpa using hcomp

/-! ### The defect on the real axis -/

/-- `D_Y(x) = x ξ(2x − 1) − (1 − x) ξ(2x) Y^{2x−1}`: the constant term on the real axis divided by
`Y^{1−x}`. -/
def defect (Y x : ℝ) : ℝ := x * xiReal (2 * x - 1) - (1 - x) * xiReal (2 * x) * Y ^ (2 * x - 1)

theorem constantTermReal_eq_defect {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    constantTermReal Y x = defect Y x * Y ^ (1 - x) := by
  have hsplit : Y ^ x = Y ^ (2 * x - 1) * Y ^ (1 - x) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  rw [constantTermReal, defect, hsplit]
  ring

theorem constantTermReal_pos_of_defect_pos {Y x : ℝ} (hY : 0 < Y) (h : 0 < defect Y x) :
    0 < constantTermReal Y x := by
  rw [constantTermReal_eq_defect hY]
  exact mul_pos h (Real.rpow_pos_of_pos hY _)

theorem constantTermReal_neg_of_defect_neg {Y x : ℝ} (hY : 0 < Y) (h : defect Y x < 0) :
    constantTermReal Y x < 0 := by
  rw [constantTermReal_eq_defect hY]
  exact mul_neg_of_neg_of_pos h (Real.rpow_pos_of_pos hY _)

theorem defect_eq_zero_of_constantTermReal {Y x : ℝ} (hY : 0 < Y)
    (h : constantTermReal Y x = 0) : defect Y x = 0 := by
  rw [constantTermReal_eq_defect hY] at h
  exact (mul_eq_zero.mp h).resolve_right (Real.rpow_pos_of_pos hY _).ne'

theorem defect_half (Y : ℝ) : defect Y (1 / 2) = 0 := by
  rw [defect]
  norm_num [xiReal_zero, xiReal_one]

/-- The defect decreases in the height. -/
theorem defect_lt_of_lt {Y₁ Y₂ x : ℝ} (hY₁ : 0 < Y₁) (h : Y₁ < Y₂) (hx : 1 / 2 < x)
    (hx1 : x < 1) : defect Y₂ x < defect Y₁ x := by
  have hgrow : Y₁ ^ (2 * x - 1) < Y₂ ^ (2 * x - 1) := Real.rpow_lt_rpow hY₁.le h (by linarith)
  have hcoef : 0 < (1 - x) * xiReal (2 * x) := mul_pos (by linarith) (xiReal_pos _)
  rw [defect, defect]
  linarith [mul_lt_mul_of_pos_left hgrow hcoef]

/-- **The slope of the defect at the centre**: `D_Y'(½) = ½ (log(4π e^{−γ}) − log Y)`. -/
theorem hasDerivAt_defect_half {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (defect Y) ((Real.log threshold - Real.log Y) / 2) (1 / 2) := by
  have e0 : (2 * (1 / 2 : ℝ) - 1) = 0 := by norm_num
  have e1 : (2 * (1 / 2 : ℝ)) = 1 := by norm_num
  have hin0 : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1
  have hin1 : HasDerivAt (fun x : ℝ => 2 * x) 2 (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_mul 2
  have hA : HasDerivAt (fun x : ℝ => xiReal (2 * x - 1)) (-xiDerivOne * 2) (1 / 2) := by
    have h0 : HasDerivAt xiReal (-xiDerivOne) (2 * (1 / 2 : ℝ) - 1) := by
      rw [e0]
      exact hasDerivAt_xiReal_zero
    exact h0.comp (1 / 2) hin0
  have hB : HasDerivAt (fun x : ℝ => xiReal (2 * x)) (xiDerivOne * 2) (1 / 2) := by
    have h1 : HasDerivAt xiReal xiDerivOne (2 * (1 / 2 : ℝ)) := by
      rw [e1]
      exact hasDerivAt_xiReal_one
    exact h1.comp (1 / 2) hin1
  have hP : HasDerivAt (fun x : ℝ => Y ^ (2 * x - 1))
      (Real.log Y * 2 * Y ^ (2 * (1 / 2 : ℝ) - 1)) (1 / 2) := hin0.const_rpow hY
  have hx : HasDerivAt (fun x : ℝ => x) 1 (1 / 2) := hasDerivAt_id _
  have h1x : HasDerivAt (fun x : ℝ => 1 - x) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have hD : HasDerivAt (defect Y)
      (1 * xiReal (2 * (1 / 2) - 1) + 1 / 2 * (-xiDerivOne * 2) -
        ((-1 * xiReal (2 * (1 / 2)) + (1 - 1 / 2) * (xiDerivOne * 2)) *
            Y ^ (2 * (1 / 2 : ℝ) - 1) +
          (1 - 1 / 2) * xiReal (2 * (1 / 2)) * (Real.log Y * 2 * Y ^ (2 * (1 / 2 : ℝ) - 1))))
      (1 / 2) := (hx.mul hA).sub ((h1x.mul hB).mul hP)
  refine hD.congr_deriv ?_
  rw [e0, e1, xiReal_zero, xiReal_one, Real.rpow_zero, log_threshold, xiDerivOne]
  ring

/-- Below the threshold the defect is positive just right of the centre. -/
theorem eventually_defect_pos {Y : ℝ} (hY : 0 < Y) (h : Real.log Y < Real.log threshold) :
    ∀ᶠ x in 𝓝[>] (1 / 2 : ℝ), 0 < defect Y x := by
  have hpos : 0 < (Real.log threshold - Real.log Y) / 2 := by linarith
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_defect_half hY)).eventually
    (lt_mem_nhds hpos)
  have hmono : 𝓝[>] (1 / 2 : ℝ) ≤ 𝓝[≠] (1 / 2 : ℝ) :=
    nhdsWithin_mono _ fun y hy => ne_of_gt hy
  filter_upwards [hmono hslope, self_mem_nhdsWithin] with x hx hgt
  rw [slope_def_field, defect_half, sub_zero] at hx
  have hxpos : 0 < x - 1 / 2 := sub_pos.mpr hgt
  by_contra hcon
  have := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hxpos.le
  linarith

/-- Above the threshold the defect is negative just right of the centre. -/
theorem eventually_defect_neg {Y : ℝ} (hY : 0 < Y) (h : Real.log threshold < Real.log Y) :
    ∀ᶠ x in 𝓝[>] (1 / 2 : ℝ), defect Y x < 0 := by
  have hneg : (Real.log threshold - Real.log Y) / 2 < 0 := by linarith
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_defect_half hY)).eventually
    (gt_mem_nhds hneg)
  have hmono : 𝓝[>] (1 / 2 : ℝ) ≤ 𝓝[≠] (1 / 2 : ℝ) :=
    nhdsWithin_mono _ fun y hy => ne_of_gt hy
  filter_upwards [hmono hslope, self_mem_nhdsWithin] with x hx hgt
  rw [slope_def_field, defect_half, sub_zero] at hx
  have hxpos : 0 < x - 1 / 2 := sub_pos.mpr hgt
  by_contra hcon
  have := div_nonneg (not_lt.mp hcon) hxpos.le
  linarith

theorem ofReal_mem_rightHalf {x : ℝ} (hx : 1 / 2 < x) : (x : ℂ) ∈ rightHalf := by
  show (1 : ℝ) / 2 < (x : ℂ).re
  rw [Complex.ofReal_re]
  exact hx

/-! ### The threshold -/

/-- **Above the threshold the exceptional parameter exists.** -/
theorem exists_exceptionalParameter_of_threshold_lt {Y : ℝ} (hY : threshold < Y) :
    ∃ x : ℝ, 1 / 2 < x ∧ x < 1 ∧ constantTerm Y (x : ℂ) = 0 := by
  have hY0 : 0 < Y := threshold_pos.trans hY
  have hlog : Real.log threshold < Real.log Y := Real.log_lt_log threshold_pos hY
  obtain ⟨x₁, hneg, hx₁⟩ := ((eventually_defect_neg hY0 hlog).and
    (Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1))).exists
  obtain ⟨x, h1, h2, h0⟩ := exists_zero_constantTermReal hY0 hx₁.2
    (by rw [defect] at hneg; linarith)
  exact ⟨x, hx₁.1.trans h1, h2, by rw [constantTerm_ofReal hY0, h0, Complex.ofReal_zero]⟩

/-- **Below the threshold there is no exceptional parameter.** -/
theorem constantTerm_ne_zero_of_lt_threshold {Y : ℝ} (hY1 : 1 ≤ Y) (hY : Y < threshold) {s : ℂ}
    (hs : s ∈ rightHalf) : constantTerm Y s ≠ 0 := by
  intro hz
  have hY0 : 0 < Y := by linarith
  obtain ⟨x₁, rfl, hx₁, hx₁'⟩ := exceptionalParameter_mem hY1 hs hz
  have hr₁ : constantTermReal Y x₁ = 0 := by
    rw [constantTerm_ofReal hY0] at hz
    exact_mod_cast hz
  have hd₁ := defect_eq_zero_of_constantTermReal hY0 hr₁
  -- a height between `Y` and the threshold
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂ : ℝ, Y₂ = (Y + threshold) / 2 := ⟨_, rfl⟩
  have h12 : Y < Y₂ := by rw [hY₂]; linarith
  have h2t : Y₂ < threshold := by rw [hY₂]; linarith
  have hY₂0 : 0 < Y₂ := by linarith
  have hY₂1 : 1 ≤ Y₂ := by linarith
  have hneg : defect Y₂ x₁ < 0 := by
    have := defect_lt_of_lt hY0 h12 hx₁ hx₁'
    linarith
  obtain ⟨x', hpos, hx'⟩ := ((eventually_defect_pos hY₂0 (Real.log_lt_log hY₂0 h2t)).and
    (Ioo_mem_nhdsGT hx₁)).exists
  have hc := continuous_constantTermReal hY₂0
  have hfx' := constantTermReal_pos_of_defect_pos hY₂0 hpos
  have hfx₁ := constantTermReal_neg_of_defect_neg hY₂0 hneg
  -- one zero on each side of `x₁`
  obtain ⟨a, ⟨ha1, ha2⟩, ha⟩ := intermediate_value_Ioo' hx'.2.le hc.continuousOn ⟨hfx₁, hfx'⟩
  obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ := intermediate_value_Ioo hx₁'.le hc.continuousOn
    ⟨hfx₁, by rw [constantTermReal_one hY₂0]; norm_num⟩
  have hza : constantTerm Y₂ (a : ℂ) = 0 := by
    rw [constantTerm_ofReal hY₂0, ha, Complex.ofReal_zero]
  have hzb : constantTerm Y₂ (b : ℂ) = 0 := by
    rw [constantTerm_ofReal hY₂0, hb, Complex.ofReal_zero]
  have heq := constantTerm_zero_subsingleton hY₂1
    ⟨ofReal_mem_rightHalf (hx'.1.trans ha1), hza⟩ ⟨ofReal_mem_rightHalf (hx₁.trans hb1), hzb⟩
  have hab : a = b := by exact_mod_cast heq
  linarith

/-- **At the threshold there is no exceptional parameter.** -/
theorem constantTerm_ne_zero_at_threshold {s : ℂ} (hs : s ∈ rightHalf) :
    constantTerm threshold s ≠ 0 := by
  intro hz
  have ht1 := one_lt_threshold
  have ht0 := threshold_pos
  obtain ⟨x₁, rfl, hx₁, hx₁'⟩ := exceptionalParameter_mem ht1.le hs hz
  have hr₁ : constantTermReal threshold x₁ = 0 := by
    rw [constantTerm_ofReal ht0] at hz
    exact_mod_cast hz
  have hd₁ := defect_eq_zero_of_constantTermReal ht0 hr₁
  -- a second point and the one height at which it is a zero
  obtain ⟨x', hx'⟩ : ∃ x' : ℝ, x' = (1 / 2 + x₁) / 2 := ⟨_, rfl⟩
  have hx'1 : 1 / 2 < x' := by rw [hx']; linarith
  have hx'2 : x' < x₁ := by rw [hx']; linarith
  have hx'3 : x' < 1 := by linarith
  have hden : 0 < (1 - x') * xiReal (2 * x') := mul_pos (by linarith) (xiReal_pos _)
  have hnum : 0 < x' * xiReal (2 * x' - 1) := mul_pos (by linarith) (xiReal_pos _)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = x' * xiReal (2 * x' - 1) / ((1 - x') * xiReal (2 * x')) :=
    ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; exact div_pos hnum hden
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℝ, Y' = R ^ (2 * x' - 1)⁻¹ := ⟨_, rfl⟩
  have hY'0 : 0 < Y' := by rw [hY']; exact Real.rpow_pos_of_pos hR0 _
  have hd' : defect Y' x' = 0 := by
    have hpow : Y' ^ (2 * x' - 1) = R := by
      rw [hY']
      exact Real.rpow_inv_rpow hR0.le (by linarith)
    rw [defect, hpow, hR, mul_div_cancel₀ _ hden.ne', sub_self]
  have hr' : constantTermReal Y' x' = 0 := by
    rw [constantTermReal_eq_defect hY'0, hd', zero_mul]
  have hz' : constantTerm Y' (x' : ℂ) = 0 := by
    rw [constantTerm_ofReal hY'0, hr', Complex.ofReal_zero]
  rcases lt_trichotomy Y' threshold with hlt | heq | hgt
  · -- a zero between `x'` and `x₁` at a height below the threshold
    obtain ⟨Ym, hYm⟩ : ∃ Ym : ℝ, Ym = (max Y' 1 + threshold) / 2 := ⟨_, rfl⟩
    have hmax : max Y' 1 < threshold := max_lt hlt ht1
    have h1 : max Y' 1 < Ym := by rw [hYm]; linarith
    have h2 : Ym < threshold := by rw [hYm]; linarith
    have hYm1 : 1 ≤ Ym := (le_max_right _ _).trans h1.le
    have hYmY' : Y' < Ym := (le_max_left _ _).trans_lt h1
    have hYm0 : 0 < Ym := by linarith
    have hneg : defect Ym x' < 0 := by
      have := defect_lt_of_lt hY'0 hYmY' hx'1 hx'3
      linarith
    have hpos : 0 < defect Ym x₁ := by
      have := defect_lt_of_lt hYm0 h2 hx₁ hx₁'
      linarith
    obtain ⟨a, ⟨ha1, -⟩, ha⟩ := intermediate_value_Ioo hx'2.le
      (continuous_constantTermReal hYm0).continuousOn
      ⟨constantTermReal_neg_of_defect_neg hYm0 hneg, constantTermReal_pos_of_defect_pos hYm0 hpos⟩
    exact constantTerm_ne_zero_of_lt_threshold hYm1 h2 (ofReal_mem_rightHalf (hx'1.trans ha1))
      (by rw [constantTerm_ofReal hYm0, ha, Complex.ofReal_zero])
  · -- two zeros at the threshold
    rw [heq] at hz'
    have h := constantTerm_zero_subsingleton ht1.le ⟨ofReal_mem_rightHalf hx'1, hz'⟩ ⟨hs, hz⟩
    have hxx : x' = x₁ := by exact_mod_cast h
    linarith
  · -- the zero `x₁` moves right while `x'` is a zero at the same height
    obtain ⟨x₂, h12, -, hz₂⟩ := exceptionalParameter_mono ht1.le hgt hx₁ hz
    have h := constantTerm_zero_subsingleton (ht1.le.trans hgt.le)
      ⟨ofReal_mem_rightHalf hx'1, hz'⟩ ⟨ofReal_mem_rightHalf (hx₁.trans h12), hz₂⟩
    have hxx : x' = x₂ := by exact_mod_cast h
    linarith

/-- **The exceptional parameter exists exactly above `4π e^{−γ}`.** -/
theorem exists_exceptionalParameter_iff {Y : ℝ} (hY : 1 ≤ Y) :
    (∃ s ∈ rightHalf, constantTerm Y s = 0) ↔
      4 * Real.pi * Real.exp (-Real.eulerMascheroniConstant) < Y := by
  constructor
  · rintro ⟨s, hs, hz⟩
    by_contra hle
    rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
    · exact constantTerm_ne_zero_of_lt_threshold hY hlt hs hz
    · have hY' : Y = threshold := heq
      rw [hY'] at hz
      exact constantTerm_ne_zero_at_threshold hs hz
  · intro h
    obtain ⟨x, hx1, -, hz⟩ := exists_exceptionalParameter_of_threshold_lt (Y := Y) h
    exact ⟨x, ofReal_mem_rightHalf hx1, hz⟩

/-- **Purity up to the threshold.** For `1 ≤ Y ≤ 4π e^{−γ}` every zero of the cleared constant
term lies on the line `Re s = ½`. -/
theorem re_eq_half_of_constantTerm_eq_zero {Y : ℝ} (hY1 : 1 ≤ Y)
    (hY : Y ≤ 4 * Real.pi * Real.exp (-Real.eulerMascheroniConstant)) {s : ℂ}
    (h : constantTerm Y s = 0) : s.re = 1 / 2 := by
  have hnone : ¬ ∃ s ∈ rightHalf, constantTerm Y s = 0 := fun hex =>
    absurd ((exists_exceptionalParameter_iff hY1).mp hex) (not_lt.mpr hY)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine hnone ⟨1 - s, ?_, by rw [constantTerm_one_sub, h, neg_zero]⟩
    show (1 : ℝ) / 2 < (1 - s).re
    simp only [sub_re, one_re]
    linarith
  · exact hnone ⟨s, hgt, h⟩

end

end GaloisForLFunctions.InfiniteRankPurityTheory
