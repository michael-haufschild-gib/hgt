import GaloisForLFunctions.RHTower.DualCarrierWeightOscillation
import GaloisForLFunctions.RHTower.HighBlockDualWeightRightShift

/-!
# Large-argument decay of the dual carrier weight (right contour shift)

The dual carrier weight `A_Y(τ) = χ(s₁)χ(s₂)·W(Y)` on the Levinson lines `s₁ = ½ − d + iτ`,
`s₂ = ½ − d − iτ` is the Mellin integral on `Re w = 1` of the carrier integrand

`J(w) = χ(s₁ − w)·χ(s₂ − w)·Y^{−w} e^{w²}/w`.

`J` is analytic on `Re w > ½` (both `χ` arguments have real part `< 1`, the kernel's only pole is
at `0`), so the contour moves to `Re w = ½ − d + K` (`K ∈ ℕ`, `K ≥ 1`), where both `χ` arguments
sit on the fixed line `Re = −K` and the corpus bound `‖χ(−K + it)‖ ≤ C(1+|t|)^{K+½}` applies.
The horizontal edges vanish by the Gaussian kernel against polynomial strip growth.  Result:

`‖A_Y(τ)‖ ≤ C (1 + |τ|)^{2K+1} Y^{−(½ − d + K)}`,

with `C` depending only on `K`: the decay in `Y ≫ τ²` that truncates the dual series of the
product approximate functional equation at `mn ≍ τ²/x`, uniformly in the displacement.
-/

open Complex MeasureTheory Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The carrier integrand `χ(s₁ − w)·χ(s₂ − w)·Y^{−w}e^{w²}/w`. -/
def carrierIntegrand (d τ Y : ℝ) (w : ℂ) : ℂ :=
  zetaChi (displacedLinePt d τ - w) * zetaChi (displacedLinePt d (-τ) - w)
    * smoothAFEMellinIntegrand Y w

theorem dualCarrierWeight_eq_integral_carrierIntegrand (d Y τ : ℝ) :
    dualCarrierWeight d Y τ
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  unfold dualCarrierWeight
  congr 1

theorem analyticAt_smoothAFEMellinIntegrand {Y : ℝ} (hY : 0 < Y) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (smoothAFEMellinIntegrand Y) w := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : AnalyticAt ℂ (fun w : ℂ => (Y : ℂ) ^ (-w)) w := by
    have : (fun w : ℂ => (Y : ℂ) ^ (-w)) = fun w => Complex.exp (Complex.log Y * (-w)) := by
      funext w
      exact Complex.cpow_def_of_ne_zero hY0 _
    rw [this]
    exact analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id.neg)
  have h2 : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w ^ 2) / w) w :=
    (analyticAt_cexp.comp (analyticAt_id.pow 2)).div analyticAt_id hw
  exact h1.mul h2

theorem analyticAt_zetaChi_displaced_sub (d τ : ℝ) {w : ℂ}
    (hw : -(1 / 2) - d < w.re) :
    AnalyticAt ℂ (fun w : ℂ => zetaChi (displacedLinePt d τ - w)) w := by
  have hG : Gammaℝ (1 - (displacedLinePt d τ - w)) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    linarith
  exact AnalyticAt.comp (g := zetaChi) (f := fun w : ℂ => displacedLinePt d τ - w)
    (zetaChi_analyticAt hG) (analyticAt_const.sub analyticAt_id)

theorem carrierIntegrand_analyticOnNhd_rightHalf {d : ℝ} (hd : 0 < d) (τ : ℝ) {Y : ℝ}
    (hY : 0 < Y) :
    AnalyticOnNhd ℂ (carrierIntegrand d τ Y) {w : ℂ | 1 / 2 < w.re} := by
  intro w hw
  have hw' : (1 / 2 : ℝ) < w.re := hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw'
    simp at hw'
    linarith
  exact ((analyticAt_zetaChi_displaced_sub d τ (by linarith)).mul
    (analyticAt_zetaChi_displaced_sub d (-τ) (by linarith))).mul
    (analyticAt_smoothAFEMellinIntegrand hY hw0)

/-- The rectangle `[1, K] × [−T, T]` has vanishing boundary integral. -/
theorem carrierIntegrand_rectIntegral_eq_zero {d τ Y K T : ℝ} (hd : 0 < d) (hY : 0 < Y)
    (hK : 1 ≤ K) :
    rectIntegral (carrierIntegrand d τ Y) (((1 : ℝ) : ℂ) - (T : ℂ) * I)
      ((K : ℂ) + (T : ℂ) * I) = 0 := by
  apply rectIntegral_eq_zero_of_analyticOnNhd (U := {w : ℂ | 1 / 2 < w.re}) ?_
    (carrierIntegrand_analyticOnNhd_rightHalf hd τ hY)
  intro w hw
  have hre := (Complex.mem_reProdIm.mp hw).1
  have h1 : (((1 : ℝ) : ℂ) - (T : ℂ) * I).re = 1 := by simp
  have h2 : ((K : ℂ) + (T : ℂ) * I).re = K := by simp
  rw [h1, h2, Set.uIcc_of_le hK] at hre
  show (1 / 2 : ℝ) < w.re
  linarith [hre.1]

/-- Pointwise bound on the strip `1 ≤ Re w ≤ K`: the two `χ` factors are left implicit. -/
theorem norm_carrierIntegrand_le_strip {d τ Y K u : ℝ} (hY : 0 < Y) (hu1 : 1 ≤ u)
    (huK : u ≤ K) (t : ℝ) :
    ‖carrierIntegrand d τ Y ((u : ℂ) + (t : ℂ) * I)‖ ≤
      ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I)‖ *
        ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((-τ - t : ℝ) : ℂ) * I)‖ *
        (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(t ^ 2)) := by
  unfold carrierIntegrand
  have harg₁ : displacedLinePt d τ - ((u : ℂ) + (t : ℂ) * I)
      = ((1 / 2 - d - u : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  have harg₂ : displacedLinePt d (-τ) - ((u : ℂ) + (t : ℂ) * I)
      = ((1 / 2 - d - u : ℝ) : ℂ) + ((-τ - t : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [harg₁, harg₂, norm_mul, norm_mul]
  have hmell := norm_smoothAFEMellinIntegrand_vertical_le hY (by linarith : (0 : ℝ) < u) t
  have hY' : Y ^ (-u) ≤ Real.exp (K * |Real.log Y|) := by
    rw [Real.rpow_def_of_pos hY]
    apply Real.exp_le_exp.mpr
    have h1 : -|Real.log Y| ≤ Real.log Y := neg_abs_le _
    nlinarith [abs_nonneg (Real.log Y)]
  have hk : Real.exp (u ^ 2) / u ≤ Real.exp (K ^ 2) := by
    calc Real.exp (u ^ 2) / u ≤ Real.exp (u ^ 2) := div_le_self (Real.exp_pos _).le hu1
      _ ≤ Real.exp (K ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hprod : Y ^ (-u) * (Real.exp (u ^ 2) / u)
      ≤ Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2) :=
    mul_le_mul hY' hk (by positivity) (Real.exp_pos _).le
  refine le_trans (mul_le_mul_of_nonneg_left hmell (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) (by positivity)) ?_
  apply le_of_eq
  ring

/-- Both horizontal edges of the right-shift rectangle vanish (`ε = ±1` selects the edge). -/
theorem tendsto_carrierIntegrand_horizontal {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4) (hY : 0 < Y)
    {K'' : ℕ}
    (hK'' : 1 ≤ K'') (τ : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (1 : ℝ)..(1 / 2 - d + K''),
      carrierIntegrand d τ Y ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨T₀, N, C, hC, hgrow⟩ := hasStripPolyGrowthOffReal_zetaChi (-((K'' : ℝ) + 1)) 0
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  set B : ℝ := C * C * (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ =>
      (K * B) * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) (2 * N)).const_mul (K * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max (|τ| + 1) (|τ| + T₀))] with T hT
  have hTτ : |τ| + 1 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := by linarith [abs_nonneg τ]
  have hTlarge : |τ| + T₀ ≤ T := (le_max_right _ _).trans hT
  have hεsq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  -- the two heights `τ − εT` and `−τ − εT` are both at least `T − |τ|` in modulus
  have hheight : ∀ σ : ℝ, |σ| ≤ |τ| → T₀ ≤ |σ - ε * T| ∧ |σ - ε * T| ≤ |τ| + T := by
    intro σ hσ
    have h1 : |σ - ε * T| ≤ |σ| + |ε * T| := abs_sub _ _
    have h2 : |ε * T| = T := by rw [abs_mul, hεabs, one_mul, abs_of_nonneg hT0]
    have h3 : |ε * T| - |σ| ≤ |σ - ε * T| := by
      have := abs_sub_abs_le_abs_sub (ε * T) σ
      rw [abs_sub_comm] at this
      linarith
    constructor
    · rw [h2] at h3; linarith
    · rw [h2] at h1; linarith
  have hbound : ∀ u ∈ Set.uIoc (1 : ℝ) K,
      ‖carrierIntegrand d τ Y ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le hK1] at hu
    have hu1 : 1 ≤ u := hu.1.le
    have huK : u ≤ K := hu.2
    have hpt := norm_carrierIntegrand_le_strip (d := d) (τ := τ) (K := K) hY hu1 huK (ε * T)
    have hsq : (ε * T) ^ 2 = T ^ 2 := by rw [mul_pow, hεsq, one_mul]
    rw [hsq] at hpt
    have hchi : ∀ σ : ℝ, |σ| ≤ |τ| →
        ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I)‖
          ≤ C * (1 + |τ| + T) ^ N := by
      intro σ hσ
      obtain ⟨hlow, hup⟩ := hheight σ hσ
      have him : ((((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I)).im = σ - ε * T := by
        simp
      have h := hgrow (((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * T : ℝ) : ℂ) * I)
        (by simp; rw [hKdef] at huK; linarith) (by simp; linarith) (by rw [him]; exact hlow)
      rw [him] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity) _ N
      linarith
    have hpow : (1 + |τ| + T) ^ N * (1 + |τ| + T) ^ N = (1 + |τ| + T) ^ (2 * N) := by
      rw [← pow_add, two_mul]
    calc ‖carrierIntegrand d τ Y ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - ε * T : ℝ) : ℂ) * I)‖ *
            ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((-τ - ε * T : ℝ) : ℂ) * I)‖ *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := hpt
      _ ≤ (C * (1 + |τ| + T) ^ N) * (C * (1 + |τ| + T) ^ N) *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := by
          gcongr
          · exact hchi τ le_rfl
          · exact hchi (-τ) (by rw [abs_neg])
      _ = B * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) := by
          rw [hBdef, ← hpow]; ring
  calc ‖∫ u : ℝ in (1 : ℝ)..K, carrierIntegrand d τ Y ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) * |K - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = B * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) * (K - 1) := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ K - 1)]
    _ ≤ B * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) * K :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (K * B) * ((1 + |τ| + T) ^ (2 * N) * Real.exp (-(T ^ 2))) := by ring

/-- Pointwise Gaussian majorant on the shifted line `Re w = ½ − d + K`. -/
theorem norm_carrierIntegrand_right_line_le {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : ℝ, ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ C₁ * (1 + |t|) ^ ((K'' : ℝ) + 1 / 2)) (τ v : ℝ) :
    ‖carrierIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * C₁ * (Y ^ (-(1 / 2 - d + K'')) * Real.exp ((1 / 2 - d + K'') ^ 2))
          * Real.exp ((2 * ((K'' : ℝ) + 1 / 2)) ^ 2))
        * (1 + |τ|) ^ (2 * ((K'' : ℝ) + 1 / 2)) * Real.exp (-(3 / 4) * v ^ 2) := by
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  set p : ℝ := (K'' : ℝ) + 1 / 2 with hpdef
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hKpos : 0 < K := by linarith
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  unfold carrierIntegrand
  have harg₁ : displacedLinePt d τ - ((K : ℂ) + (v : ℂ) * I)
      = (((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    rw [hKdef]
    push_cast
    ring
  have harg₂ : displacedLinePt d (-τ) - ((K : ℂ) + (v : ℂ) * I)
      = (((-(K'' : ℝ)) : ℝ) : ℂ) + ((-τ - v : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    rw [hKdef]
    push_cast
    ring
  rw [harg₁, harg₂, norm_mul, norm_mul]
  have hsum : ∀ σ : ℝ, |σ| ≤ |τ| → 1 + |σ - v| ≤ (1 + |τ|) * (1 + |v|) := by
    intro σ hσ
    have h1 : |σ - v| ≤ |σ| + |v| := abs_sub _ _
    nlinarith [abs_nonneg τ, abs_nonneg v, abs_nonneg σ]
  have hrp : ∀ σ : ℝ, |σ| ≤ |τ| → (1 + |σ - v|) ^ p ≤ (1 + |τ|) ^ p * (1 + |v|) ^ p := by
    intro σ hσ
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (hsum σ hσ) hp0
  have hA₁ : ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I)‖
      ≤ C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p) :=
    (hC₁ (τ - v)).trans (mul_le_mul_of_nonneg_left (hrp τ le_rfl) hC₁0)
  have hA₂ : ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((-τ - v : ℝ) : ℂ) * I)‖
      ≤ C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p) :=
    (hC₁ (-τ - v)).trans (mul_le_mul_of_nonneg_left (hrp (-τ) (by rw [abs_neg])) hC₁0)
  have hM : ‖smoothAFEMellinIntegrand Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2)) := by
    refine (norm_smoothAFEMellinIntegrand_vertical_le hY hKpos v).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le hK1) (by positivity))
      (Real.exp_pos _).le
  have h1 : ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I)‖ *
        ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((-τ - v : ℝ) : ℂ) * I)‖ *
        ‖smoothAFEMellinIntegrand Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) * (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) *
        ((Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2))) :=
    mul_le_mul (mul_le_mul hA₁ hA₂ (norm_nonneg _) (by positivity)) hM (norm_nonneg _)
      (by positivity)
  refine h1.trans ?_
  have h2 := one_add_abs_rpow_mul_exp_neg_sq_le (by positivity : (0 : ℝ) ≤ 2 * p) v
  have hτp : (1 + |τ|) ^ p * (1 + |τ|) ^ p = (1 + |τ|) ^ (2 * p) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  have hvp : (1 + |v|) ^ p * (1 + |v|) ^ p = (1 + |v|) ^ (2 * p) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) * (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) *
        ((Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2)))
      = (C₁ * C₁ * (Y ^ (-K) * Real.exp (K ^ 2)) * (1 + |τ|) ^ (2 * p))
          * ((1 + |v|) ^ (2 * p) * Real.exp (-(v ^ 2))) := by
        rw [← hτp, ← hvp]; ring
    _ ≤ (C₁ * C₁ * (Y ^ (-K) * Real.exp (K ^ 2)) * (1 + |τ|) ^ (2 * p))
          * (Real.exp ((2 * p) ^ 2) * Real.exp (-(3 / 4) * v ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (C₁ * C₁ * (Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp ((2 * p) ^ 2))
          * (1 + |τ|) ^ (2 * p) * Real.exp (-(3 / 4) * v ^ 2) := by ring

/-- Continuity of the carrier integrand along a right line. -/
theorem continuous_carrierIntegrand_right_line {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y)
    {K : ℝ} (hK : 1 ≤ K) (τ : ℝ) :
    Continuous (fun v : ℝ => carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hA : AnalyticAt ℂ (carrierIntegrand d τ Y) ((K : ℂ) + (v : ℂ) * I) :=
    carrierIntegrand_analyticOnNhd_rightHalf hd τ hY _ (by
      show (1 / 2 : ℝ) < ((K : ℂ) + (v : ℂ) * I).re
      simp
      linarith)
  exact ContinuousAt.comp (f := fun v : ℝ => (K : ℂ) + (v : ℂ) * I) hA.continuousAt
    (by fun_prop)

theorem integrable_carrierIntegrand_right_line {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    Integrable (fun v : ℝ =>
      carrierIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zetaChi_negNat_line_le K''
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : (1 : ℝ) ≤ 1 / 2 - d + K'' := by linarith
  have hcont := continuous_carrierIntegrand_right_line hd hY hK1 τ
  have hint : Integrable (fun v : ℝ =>
      ((C₁ * C₁ * (Y ^ (-(1 / 2 - d + K'')) * Real.exp ((1 / 2 - d + K'') ^ 2))
          * Real.exp ((2 * ((K'' : ℝ) + 1 / 2)) ^ 2))
        * (1 + |τ|) ^ (2 * ((K'' : ℝ) + 1 / 2))) * Real.exp (-(3 / 4) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 3 / 4)).const_mul _
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  exact norm_carrierIntegrand_right_line_le hd hd4 hY hK'' hC₁0 hC₁ τ v

/-- Integrability on the base line `Re w = 1`, from the whole-plane carrier envelope. -/
theorem integrable_carrierIntegrand_one_line {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) (τ : ℝ) :
    Integrable (fun v : ℝ => carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le hd hd4
  have hfun : (fun v : ℝ => carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      = fun v : ℝ => chiCarrier d v τ * dualFrequencyKernel Y v := by
    funext v
    unfold carrierIntegrand chiCarrier dualFrequencyKernel levinsonShift
    push_cast
    ring_nf
  rw [hfun]
  have hcont : Continuous (fun v : ℝ => chiCarrier d v τ * dualFrequencyKernel Y v) :=
    ((continuous_chiCarrier_uncurry hd).comp (Continuous.prodMk continuous_const continuous_id)).mul
      (continuous_dualFrequencyKernel hY)
  have hbound : ∀ v : ℝ, ‖chiCarrier d v τ * dualFrequencyKernel Y v‖
      ≤ (C * (1 + |τ|) ^ 4 * (Y⁻¹ * Real.exp 1)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
    intro v
    rw [norm_mul]
    have hG := hC v τ
    have hk := norm_dualFrequencyKernel_le hY v
    have hb1 : 1 + |τ - v| ≤ (1 + |τ|) * (1 + |v|) := by
      have := abs_sub τ v
      nlinarith [abs_nonneg τ, abs_nonneg v]
    have hb2 : 1 + |τ + v| ≤ (1 + |τ|) * (1 + |v|) := by
      have := abs_add_le τ v
      nlinarith [abs_nonneg τ, abs_nonneg v]
    have hG' : ‖chiCarrier d v τ‖ ≤ C * ((1 + |τ|) ^ 4 * (1 + |v|) ^ 4) := by
      refine hG.trans ?_
      apply mul_le_mul_of_nonneg_left _ hC0
      calc (1 + |τ - v|) ^ 2 * (1 + |τ + v|) ^ 2
          ≤ ((1 + |τ|) * (1 + |v|)) ^ 2 * ((1 + |τ|) * (1 + |v|)) ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) hb1 2)
              (pow_le_pow_left₀ (by positivity) hb2 2) (by positivity) (by positivity)
        _ = (1 + |τ|) ^ 4 * (1 + |v|) ^ 4 := by ring
    calc ‖chiCarrier d v τ‖ * ‖dualFrequencyKernel Y v‖
        ≤ (C * ((1 + |τ|) ^ 4 * (1 + |v|) ^ 4)) * ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) :=
          mul_le_mul hG' hk (norm_nonneg _) (by positivity)
      _ = (C * (1 + |τ|) ^ 4 * (Y⁻¹ * Real.exp 1)) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          ring
  exact ((integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul _).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- The line `Re w = 1` and the shifted line `Re w = ½ − d + K` carry the same integral. -/
theorem integral_carrierIntegrand_one_eq_right {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    (∫ v : ℝ, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, carrierIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hbottom' := tendsto_carrierIntegrand_horizontal hd hd4 hY hK'' τ (ε := -1) (Or.inr rfl)
  have htop' := tendsto_carrierIntegrand_horizontal hd hd4 hY hK'' τ (ε := 1) (Or.inl rfl)
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hbottom : Tendsto (fun T : ℝ => ∫ u : ℝ in (1 : ℝ)..K,
      carrierIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
    refine hbottom'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in (1 : ℝ)..K,
      carrierIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine htop'.congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1
    push_cast
    ring
  have hrightK : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_carrierIntegrand_right_line hd hd4 hY hK'' τ)
      tendsto_neg_atTop_atBot tendsto_id
  have hright1 : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_carrierIntegrand_one_line hd hd4 hY τ)
      tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbottom.sub htop).add (hrightK.const_smul I)).sub (hright1.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (1 : ℝ)..K, carrierIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (1 : ℝ)..K, carrierIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (1 : ℝ)..K, carrierIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (1 : ℝ)..K, carrierIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I))
        = 0 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hrect := carrierIntegrand_rectIntegral_eq_zero (d := d) (τ := τ) (Y := Y)
      (K := K) (T := T) hd hY hK1
    simpa [RHTower.rectIntegral, sub_eq_add_neg] using hrect
  have h := tendsto_nhds_unique (hlimit'.congr' hevent) (tendsto_const_nhds (x := (0 : ℂ)))
  have h' : I • ((∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) -
      ∫ v : ℝ, carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) = 0 := by
    rw [smul_sub]
    exact h
  rcases smul_eq_zero.mp h' with hI | hdiff
  · exact absurd hI I_ne_zero
  · exact (sub_eq_zero.mp hdiff).symm

/-- **Large-argument decay of the dual carrier weight.** For every `K ≥ 1` one constant serves
all displacements `0 < d ≤ ¼`, all heights `τ` and all `Y > 0`:
`‖χ(s₁)χ(s₂)W(Y)‖ ≤ C (1 + |τ|)^{2K+1} Y^{−(½ − d + K)}`. -/
theorem exists_norm_dualCarrierWeight_le_rightShift {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d Y τ : ℝ, 0 < d → d ≤ 1 / 4 → 0 < Y →
      ‖dualCarrierWeight d Y τ‖ ≤
        C * (1 + |τ|) ^ (2 * ((K'' : ℝ) + 1 / 2)) * Y ^ (-(1 / 2 - d + K'')) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zetaChi_negNat_line_le K''
  have hG0 : 0 ≤ ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  refine ⟨(1 / (2 * Real.pi)) * (C₁ * C₁ * Real.exp (((K'' : ℝ) + 1 / 2) ^ 2)
    * Real.exp ((2 * ((K'' : ℝ) + 1 / 2)) ^ 2) * ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2)),
    by positivity, fun d Y τ hd hd4 hY => ?_⟩
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hbound := fun v : ℝ =>
    norm_carrierIntegrand_right_line_le hd hd4 hY hK'' hC₁0 hC₁ τ v
  have hW : dualCarrierWeight d Y τ =
      (1 / (2 * Real.pi)) • ∫ v : ℝ,
        carrierIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I) := by
    rw [dualCarrierWeight_eq_integral_carrierIntegrand]
    congr 1
    exact integral_carrierIntegrand_one_eq_right hd hd4 hY hK'' τ
  have hint : Integrable (fun v : ℝ => Real.exp (-(3 / 4) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  set G : ℝ := ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) with hGdef
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  set p : ℝ := (K'' : ℝ) + 1 / 2 with hpdef
  have hKp : K ≤ p := by rw [hKdef, hpdef]; linarith
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hexpK : Real.exp (K ^ 2) ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  set A : ℝ := (C₁ * C₁ * (Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp ((2 * p) ^ 2))
    * (1 + |τ|) ^ (2 * p) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hnorm : ‖∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖ ≤ A * G := by
    calc ‖∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v : ℝ, ‖carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, A * Real.exp (-(3 / 4) * v ^ 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
            (hint.const_mul A) (Filter.Eventually.of_forall fun v => hbound v)
      _ = A * G := by rw [MeasureTheory.integral_const_mul]
  rw [hW, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ, carrierIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (A * G) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 / (2 * Real.pi)) * (C₁ * C₁ * Real.exp (K ^ 2) * Real.exp ((2 * p) ^ 2) * G)
          * (1 + |τ|) ^ (2 * p) * Y ^ (-K) := by
        rw [hAdef]; ring
    _ ≤ (1 / (2 * Real.pi)) * (C₁ * C₁ * Real.exp (p ^ 2) * Real.exp ((2 * p) ^ 2) * G)
          * (1 + |τ|) ^ (2 * p) * Y ^ (-K) := by
        gcongr

end

end RHTower
