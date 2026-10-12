import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.ZetaLowerBound
import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowthGeneralSigma

/-!
# Local zero counts of `ζ` next to the one-line

For `τ ≥ e^{e^{30}} + 1` and `0 < κ ≤ 1/(3·2^{24})`, the zeros of `ζ` in the closed disc of radius
`5κ/2` around `c = 1 + 2κ + iτ`, counted with multiplicity, number at most
`log(M/m)/log(6/5)` (`zeta_disc_zeroCount_le_near_one_line`).  Here
`M = (C_VK + C) · L* · exp(864 κ^{3/2} L* log L*)`, `L* = log(τ+1)`, and `m = (2κ)³/(756 log τ)`.
So the count is `O(κ^{3/2} L log L + log L + log(1/κ))`.

The disc contains every zero `ρ` with `1 − κ/4 ≤ Re ρ` and `|Im ρ − τ| ≤ κ`.

Proof: Jensen's inequality for `ζ` between the radii `5κ/2` and `3κ`.  On the outer circle every
point has depth `1 − Re z ≤ κ`.  Points within the VK width use the corpus bound
`‖ζ‖ ≤ C_VK log τ'`; deeper points use the general-depth bound
`‖ζ‖ ≤ C log τ' · exp(864 (1 − Re z)^{3/2} log τ' log log τ')`.  At the centre, the quartic lower bound
`‖ζ(1+x+iτ)‖⁴ ≥ x³/(756 log τ)` with `x = 2κ` gives `‖ζ(c)‖ ≥ m`.
-/

open Complex MeromorphicOn Metric

namespace RHTower

noncomputable section

open RHTower.Sieve

/-- The sphere bound `M = (C_VK + C) · L* · exp(864 κ^{3/2} L* log L*)`, `L* = log(τ+1)`. -/
def zetaNearOneSphereBound (τ κ : ℝ) : ℝ :=
  (vinogradovKorobovGrowthConstant + vkGeneralGrowthConstant) * Real.log (τ + 1) *
    vkGeneralGrowth κ (Real.log (τ + 1))

/-- The centre bound `m = (2κ)³/(756 log τ)`. -/
def zetaNearOneCentreBound (τ κ : ℝ) : ℝ := (2 * κ) ^ 3 / (756 * Real.log τ)

theorem vkGeneralGrowth_mono {κ κ' L L' : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ κ') (hL1 : 1 ≤ L)
    (hL : L ≤ L') : vkGeneralGrowth κ L ≤ vkGeneralGrowth κ' L' := by
  unfold vkGeneralGrowth
  apply Real.exp_le_exp.mpr
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hl : Real.log L ≤ Real.log L' := Real.log_le_log (by linarith) hL
  have hs : Real.sqrt κ ≤ Real.sqrt κ' := Real.sqrt_le_sqrt hκ
  have h1 : κ * Real.sqrt κ ≤ κ' * Real.sqrt κ' :=
    mul_le_mul hκ hs (Real.sqrt_nonneg _) (by linarith)
  have h2 : 864 * L * Real.log L ≤ 864 * L' * Real.log L' := by
    have := mul_le_mul hL hl hl0 (by linarith)
    nlinarith
  exact mul_le_mul h1 h2 (mul_nonneg (by linarith) hl0) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))

theorem one_le_vkGeneralGrowth {κ L : ℝ} (hκ0 : 0 ≤ κ) (hL1 : 1 ≤ L) : 1 ≤ vkGeneralGrowth κ L := by
  unfold vkGeneralGrowth
  have := Real.log_nonneg hL1
  exact Real.one_le_exp (by positivity)

/-- **The sphere bound.**  On the circle of radius `3κ` around `1 + 2κ + iτ`, `‖ζ‖ ≤ M`. -/
theorem norm_riemannZeta_le_zetaNearOneSphereBound {τ κ : ℝ} (hτ : Real.exp (Real.exp 30) + 1 ≤ τ)
    (hκ0 : 0 < κ) (hκ : κ ≤ 1 / (3 * 2 ^ 24)) {z : ℂ}
    (hz : z ∈ sphere (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I) |3 * κ|) :
    ‖riemannZeta z‖ ≤ zetaNearOneSphereBound τ κ := by
  rw [mem_sphere, dist_eq_norm, abs_of_pos (by linarith)] at hz
  have hre := Complex.abs_re_le_norm (z - (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I))
  have him := Complex.abs_im_le_norm (z - (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I))
  rw [hz] at hre him
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Complex.sub_im,
    Complex.add_im, Complex.mul_im, zero_add] at hre him
  have hκ3 : 3 * κ ≤ 1 := by
    have : (1 : ℝ) / (3 * 2 ^ 24) ≤ 1 / 3 := by norm_num
    linarith
  have hre1 := (abs_le.mp hre).1
  have hre2 := (abs_le.mp hre).2
  have him1 := (abs_le.mp him).1
  have him2 := (abs_le.mp him).2
  set σ := z.re with hσ
  set τ' := z.im with hτ'
  have hz' : z = (σ : ℂ) + (τ' : ℂ) * I := (Complex.re_add_im z).symm
  have hτ'big : Real.exp (Real.exp 30) ≤ τ' := by linarith
  have hτ'0 : 0 < τ' := lt_of_lt_of_le (Real.exp_pos _) hτ'big
  have hL' : Real.exp 30 ≤ Real.log τ' := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hτ'big
  have hL'1 : 1 ≤ Real.log τ' := le_trans (Real.one_le_exp (by norm_num)) hL'
  have hLL : Real.log τ' ≤ Real.log (τ + 1) := Real.log_le_log hτ'0 (by linarith)
  have hE := one_le_vkGeneralGrowth (κ := κ) hκ0.le (hL'1.trans hLL)
  have hCV : 0 ≤ vinogradovKorobovGrowthConstant := by
    unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant; positivity
  have hCG : 0 ≤ vkGeneralGrowthConstant := by unfold vkGeneralGrowthConstant; positivity
  have hLpos : 0 ≤ Real.log (τ + 1) := by linarith
  rw [hz', zetaNearOneSphereBound]
  by_cases hw : 1 - vinogradovKorobovWidth (Real.log τ') ≤ σ
  · have h := norm_riemannZeta_le_vinogradovKorobov hτ'big hw (by linarith)
    calc ‖riemannZeta ((σ : ℂ) + (τ' : ℂ) * I)‖ ≤ vinogradovKorobovGrowthConstant * Real.log τ' := h
      _ ≤ (vinogradovKorobovGrowthConstant + vkGeneralGrowthConstant) * Real.log (τ + 1) * 1 := by
          nlinarith
      _ ≤ _ := by gcongr
  · push Not at hw
    have hw0 := vinogradovKorobovWidth_pos hL'
    have h := norm_riemannZeta_le_vinogradovKorobov_general hτ'big hw.le (by linarith)
    have hmono := vkGeneralGrowth_mono (κ := 1 - σ) (κ' := κ) (by linarith) (by linarith) hL'1 hLL
    have hE' := one_le_vkGeneralGrowth (κ := 1 - σ) (by linarith) hL'1
    calc ‖riemannZeta ((σ : ℂ) + (τ' : ℂ) * I)‖
        ≤ vkGeneralGrowthConstant * Real.log τ' * vkGeneralGrowth (1 - σ) (Real.log τ') := h
      _ ≤ vkGeneralGrowthConstant * Real.log (τ + 1) * vkGeneralGrowth κ (Real.log (τ + 1)) := by
          gcongr
      _ ≤ _ := by
          have : 0 ≤ Real.log (τ + 1) * vkGeneralGrowth κ (Real.log (τ + 1)) := by positivity
          nlinarith

/-- **The centre bound.** `‖ζ(1 + 2κ + iτ)‖ ≥ (2κ)³/(756 log τ)`. -/
theorem zetaNearOneCentreBound_le {τ κ : ℝ} (hτ : 9 ≤ τ) (hκ0 : 0 < κ) (hκ : κ ≤ 1 / 2) :
    zetaNearOneCentreBound τ κ ≤ ‖riemannZeta (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  have h4 := pow_four_norm_riemannZeta_ge (x := 2 * κ) (t := τ) (by rw [abs_of_pos (by linarith)]; exact hτ)
    (by linarith) (by linarith)
  rw [abs_of_pos (by linarith)] at h4
  set Z := ‖riemannZeta (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I)‖
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hlog : 2 < Real.log τ := by
    have he : Real.exp 2 < 9 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
  have hm1 : zetaNearOneCentreBound τ κ ≤ 1 := by
    unfold zetaNearOneCentreBound
    rw [div_le_one (by positivity)]
    have : (2 * κ) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith
  unfold zetaNearOneCentreBound at hm1 ⊢
  rcases le_or_gt 1 Z with hZ1 | hZ1
  · linarith
  · have hZ4 : Z ^ 4 ≤ Z := by
      calc Z ^ 4 = Z * Z ^ 3 := by ring
        _ ≤ Z * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hZ0 hZ1.le) hZ0
        _ = Z := mul_one Z
    have : (2 * κ) ^ 3 / (756 * Real.log τ) ≤ Z ^ 4 := by exact_mod_cast h4
    linarith

/-- **Local zero count next to the one-line.**  The zeros of `ζ` in the closed disc of radius
`5κ/2` around `1 + 2κ + iτ`, counted with multiplicity, number at most `log(M/m)/log(6/5)`. -/
theorem zeta_disc_zeroCount_le_near_one_line {τ κ : ℝ} (hτ : Real.exp (Real.exp 30) + 1 ≤ τ)
    (hκ0 : 0 < κ) (hκ : κ ≤ 1 / (3 * 2 ^ 24)) :
    ((∑ᶠ u, (MeromorphicOn.divisor riemannZeta
        (closedBall (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I) |5 / 2 * κ|)) u : ℤ) : ℝ) ≤
      Real.log (zetaNearOneSphereBound τ κ / zetaNearOneCentreBound τ κ) / Real.log (6 / 5) := by
  have hκ3 : 3 * κ ≤ 1 := by
    have : (1 : ℝ) / (3 * 2 ^ 24) ≤ 1 / 3 := by norm_num
    linarith
  have hτ9 : 9 ≤ τ := by
    have : (9 : ℝ) ≤ Real.exp (Real.exp 30) := by
      have h1 : (9 : ℝ) ≤ Real.exp 30 := by
        have := Real.add_one_le_exp (30 : ℝ); linarith
      have h2 : Real.exp 30 ≤ Real.exp (Real.exp 30) := by
        have := Real.add_one_le_exp (Real.exp 30); linarith
      linarith
    linarith
  have hτbig : Real.exp (Real.exp 30) ≤ τ := by linarith
  have hL1 : 1 ≤ Real.log (τ + 1) := by
    have h : Real.exp 1 ≤ τ + 1 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hM : 1 ≤ zetaNearOneSphereBound τ κ := by
    unfold zetaNearOneSphereBound
    have hE := one_le_vkGeneralGrowth (κ := κ) hκ0.le hL1
    have hCV : 1 ≤ vinogradovKorobovGrowthConstant := by
      unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant
      have := Real.exp_pos 21; linarith
    have hCG : 0 ≤ vkGeneralGrowthConstant := by unfold vkGeneralGrowthConstant; positivity
    have h1 : 1 ≤ (vinogradovKorobovGrowthConstant + vkGeneralGrowthConstant) * Real.log (τ + 1) := by
      nlinarith
    nlinarith
  have hlogτ : 0 < Real.log τ := Real.log_pos (by linarith)
  have hm : 0 < zetaNearOneCentreBound τ κ := by unfold zetaNearOneCentreBound; positivity
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I) |3 * κ|) := by
    have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    refine (hd.analyticOnNhd isOpen_ne).mono ?_
    intro z hz
    rw [mem_closedBall, dist_eq_norm, abs_of_pos (by linarith)] at hz
    have him := Complex.abs_im_le_norm (z - (((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I))
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at him
    have hbound : |z.im - τ| ≤ 3 * κ := by simpa using him.trans hz
    intro h1
    rw [h1] at hbound
    simp only [Complex.one_im, zero_sub, abs_neg] at hbound
    rw [abs_of_pos (by linarith)] at hbound
    linarith
  have h := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds
    (c := ((1 + 2 * κ : ℝ) : ℂ) + (τ : ℂ) * I) (r := 5 / 2 * κ) (R := 3 * κ)
    (M := zetaNearOneSphereBound τ κ) (m := zetaNearOneCentreBound τ κ) (f := riemannZeta)
    (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith) hM hm hf
    (zetaNearOneCentreBound_le hτ9 hκ0 (by linarith))
    (fun z hz => norm_riemannZeta_le_zetaNearOneSphereBound hτ hκ0 hκ hz)
  refine h.trans (le_of_eq ?_)
  congr 1
  congr 1
  field_simp
  ring

end

end RHTower
