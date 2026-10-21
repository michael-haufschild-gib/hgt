import GaloisForLFunctions.ArithmeticCriticalityTheory.QuarticGaugeWindowPotential
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity

/-!
# Weil positivity on `[−13/50, 13/50]` from a quartic even gauge

The parity fold (`ParityFoldedCurvedGaugeWeilPositivity`) makes the negative pole density free on even
tests; what remains is a pointwise potential bound for an even gauge. Quadratic gauges stop near
`R ≈ 0.25`: their curvature, needed at the window centre, is paid near the edge, where the inward
neighbours of a point are higher. The quartic gauge `q P`, `q(y) = 1 − 13.1 y² + 20 y⁴`, radius
`261/1000`, collar `1/1000`, flattens the edge. With the sharp Lévy moments and
the cubic killing of `QuarticGaugeWindowPotential`, its potential at a plateau point is at least

    q(y) (D − ½ log(1 − y²/R²)) + 1.21347 − 21.96291 y² + 44.0322 y⁴ + 0.7315 y⁶ − 0.2084 y⁸,

`D = −log 2R − R/2 − (γ + log π) ≥ −1.20254` (`evenQuarticGauge_constant_ge`), and ten anchored pieces
bound this below by `1/250` on `[0, 13/50]` (`quarticGauge_window_inequality`); the minimum `≈ 0.0099`
sits near `y ≈ 0.235`, the centre value is `≈ 0.0109`.

**Theorem** (`fullZeroForm_ge_of_support_le_quarticFolded`). Every real `F ∈ C²_c` vanishing outside
`[−13/50, 13/50]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`; hence `μ(A) ≥ 1/250` for every aperture
`A ≤ 13/50` (`one_div_250_le_ccmRestrictedWeilGroundEnergy_quartic`). The reach is `2.48` times the
Markov window `21/200` and `0.925` of the plastic threshold `log ρ`, the boundary of the even fold.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The constants -/

/-- `−log(261/500) − 261/2000 − (γ + log π) ≥ −1.20254`. -/
theorem evenQuarticGauge_constant_ge :
    -1.20254 ≤ -Real.log (2 * (261 / 1000)) - 261 / 1000 / 2 - 2 * archConstantReal := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-(11 / 250) : ℝ)| < 1 by norm_num) 3
  rw [show (1 : ℝ) - -(11 / 250) = 261 / 250 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hsplit : Real.log (2 * (261 / 1000)) = Real.log (261 / 250) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hC := two_mul_archConstantReal_lt_sharp
  linarith [h.1, h.2]

/-! ### The quartic window inequality -/

/-- **The quartic window inequality.** For `0 ≤ y ≤ 13/50` and `D ≥ −1.20254`, with
`q = 1 − 13.1 y² + 20 y⁴`: `1/250 ≤ q (D − ½ log(1 − (1000/261)² y²)) + Q(y²)`. On ten pieces the
logarithm is replaced by its tangent at an anchor `(3/4)^k`, the cube of `y²` by its tangent at the
midpoint and the fourth power by its chord; the remainder is a concave quadratic in `y²`. -/
theorem quarticGauge_window_inequality {y D : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 13 / 50)
    (hD : -1.20254 ≤ D) :
    1 / 250 ≤ (1 - 13.1 * y ^ 2 + 20 * y ^ 4) *
        (D + -(1 / 2) * Real.log (1 - 1000000 / 68121 * y ^ 2)) +
      (1.21347 - 21.96291 * y ^ 2 + 44.0322 * y ^ 4 + 0.7315 * y ^ 6 - 0.2084 * y ^ 8) := by
  have hy2 : y ^ 2 ≤ (13 / 50) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hq : 0 ≤ 1 - 13.1 * y ^ 2 + 20 * y ^ 4 := by nlinarith
  have hs : 1000000 / 68121 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_pow (s := 1000000 / 68121 * y ^ 2) hs k) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 68121 * y ^ 2) with hℓ
  have piece : ∀ (lo hi : ℝ), lo ≤ y → y ≤ hi → 0 ≤ lo →
      (lo ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ hi ^ 2 ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2) ∧
        0 ≤ (y ^ 2 - (lo ^ 2 + hi ^ 2) / 2) ^ 2 * (y ^ 2 + (lo ^ 2 + hi ^ 2)) ∧
        y ^ 4 * y ^ 4 ≤ hi ^ 4 * y ^ 4) := by
    intro lo hi hl hh h0
    have h1 : lo ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
    have h2 : y ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (h0.trans hl) hh 2
    have h4 : y ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hy0 hh 4
    refine ⟨h1, h2, mul_nonneg (by linarith) (by linarith),
      mul_nonneg (sq_nonneg _) (by nlinarith), mul_le_mul_of_nonneg_right h4 (by positivity)⟩
  rcases le_or_gt y 0.12 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0 0.12 hy0 h0 (by norm_num)
    have h := anc 0; norm_num at h; linarith
  rcases le_or_gt y 0.165 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.12 0.165 h0.le h1 (by norm_num)
    have h := anc 1; norm_num at h; linarith
  rcases le_or_gt y 0.19 with h2 | h2
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.165 0.19 h1.le h2 (by norm_num)
    have h := anc 2; norm_num at h; linarith
  rcases le_or_gt y 0.21 with h3 | h3
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.19 0.21 h2.le h3 (by norm_num)
    have h := anc 3; norm_num at h; linarith
  rcases le_or_gt y 0.222 with h4 | h4
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.21 0.222 h3.le h4 (by norm_num)
    have h := anc 4; norm_num at h; linarith
  rcases le_or_gt y 0.232 with h5 | h5
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.222 0.232 h4.le h5 (by norm_num)
    have h := anc 5; norm_num at h; linarith
  rcases le_or_gt y 0.239 with h6 | h6
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.232 0.239 h5.le h6 (by norm_num)
    have h := anc 6; norm_num at h; linarith
  rcases le_or_gt y 0.245 with h7 | h7
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.239 0.245 h6.le h7 (by norm_num)
    have h := anc 7; norm_num at h; linarith
  rcases le_or_gt y 0.252 with h8 | h8
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.245 0.252 h7.le h8 (by norm_num)
    have h := anc 8; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.252 (13 / 50) h8.le hy (by norm_num)
    have h := anc 9; norm_num at h; linarith

/-! ### The potential of the even quartic gauge -/

/-- **The potential bound of the even quartic gauge** `M`: `−𝒲M(x) + 2 ∫ M(y) cosh((x − y)/2) dy ≥ 1/250`
on `[−13/50, 13/50]`. -/
theorem quarticGauge_potential_ge {x : ℝ} (hx : |x| ≤ 13 / 50) :
    1 / 250 ≤ -poleFreeWeilOperator (quarticWindowGauge (131 / 10) 20 (261 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (131 / 10) 20 (261 / 1000) (1 / 1000) y * Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 20 := by norm_num
  have hdc : 6 * 20 * (261 / 1000 : ℝ) ^ 2 ≤ 131 / 10 := by norm_num
  have hdc2 : 2 * 20 * (261 / 1000 : ℝ) ^ 2 ≤ 131 / 10 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 131 / 10 * (261 / 1000) ^ 2 + 20 * (261 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 261 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  -- evenness of the gauge
  have hWy : poleFreeWeilOperator (quarticWindowGauge (131 / 10) 20 (261 / 1000) (1 / 1000)) x =
      poleFreeWeilOperator (quarticWindowGauge (131 / 10) 20 (261 / 1000) (1 / 1000)) y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge (c := 131 / 10) (d := 20)
    (R := 261 / 1000) (δ := 1 / 1000) (x := y) hd hdc hqR hδ (by norm_num) hy0 (by linarith)
  have hbr := cubicGauge_bracket_ge (R := 261 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (261 / 1000) ^ 2 = 1000000 / 68121 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (131 / 10) 20 y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 131 / 10) (d := 20) (R := 261 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  have h1D := quarticGauge_window_inequality hy0 (by linarith) evenQuarticGauge_constant_ge
  have p2 := pow_nonneg hy0 2
  have p4 := pow_nonneg hy0 4
  have p6 := pow_nonneg hy0 6
  have p8 := pow_nonneg hy0 8
  simp only [levyMomentPoly, levyMomentErr, Nat.cast_ofNat] at hW
  unfold quarticProfile at hW hqbr
  linarith [hW, hqbr, hG, h1D, p2, p4, p6, p8]

/-! ### Even-sector positivity on `[−13/50, 13/50]` -/

/-- **Weil positivity of every even test supported in `[−13/50, 13/50]`.** Every even `F ∈ C²_c`
vanishing outside `[−13/50, 13/50]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`. -/
theorem fullZeroForm_ge_of_even_support_le_quartic {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (heven : ∀ x, F (-x) = F x)
    (hsupp : ∀ x, 13 / 50 < |x| → F x = 0) :
    1 / 250 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := quarticWindowGauge (131 / 10) 20 (261 / 1000) (1 / 1000) with hMdef
  set u : ℝ → ℝ := fun x => F x * (quarticProfile (131 / 10) 20 x)⁻¹ with hudef
  have hd : (0 : ℝ) ≤ 20 := by norm_num
  have hdc2 : 2 * 20 * (261 / 1000 : ℝ) ^ 2 ≤ 131 / 10 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 131 / 10 * (261 / 1000) ^ 2 + 20 * (261 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hMd : ContDiff ℝ 2 M := contDiff_quarticWindowGauge _ _ _ _
  have hMcs : HasCompactSupport M := hasCompactSupport_quarticWindowGauge _ _ _ hδ
  have hnn : ∀ y, 0 ≤ M y := quarticWindowGauge_nonneg hd hdc2 hqR hδ
  have hle : ∀ y, M y ≤ 1 := quarticWindowGauge_le_one hd hdc2 hqR hδ
  have hzero : ∀ y, 261 / 1000 ≤ |y| → M y = 0 := fun y hy =>
    quarticWindowGauge_eq_zero _ _ hδ hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 261 / 1000 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hMe : ∀ y, M (-y) = M y := quarticWindowGauge_neg _ _ _ _
  have hlog2 : 2 * (261 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have hqpos : ∀ y, |y| ≤ 261 / 1000 → 0 < quarticProfile (131 / 10) 20 y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    norm_num at this
    linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 261 / 1000
    · exact hF.contDiffAt.mul ((contDiff_quarticProfile _ _).contDiffAt.inv
        (hqpos y hy.le).ne' |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 13 / 50 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 13 / 50 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hue : ∀ x, u (-x) = u x := fun x => by
    simp only [hudef]
    rw [heven, quarticProfile_neg]
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 13 / 50
    · have hq := (hqpos x (by linarith)).ne'
      simp only [hudef, hMdef]
      rw [quarticWindowGauge_eq _ _ hδ (by linarith : |x| ≤ 261 / 1000 - 1 / 1000)]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part is a folded nonnegative energy
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hfoldI : 0 ≤ ∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t :=
    integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold hMd.continuous hu.continuous hMe hue hnn
      hle hzero huL (by norm_num) measurable_weilJumpDensity (C := 4) (by norm_num)
      (fun t ht0 ht1 => abs_weilJumpDensity_le ht0 (by linarith))
      (fun s x hs hx hxs => weilJumpDensity_fold_nonneg hs hx (by linarith))
  have hjump : 0 ≤ (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    have e : (∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t) =
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
          2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
      rw [← integral_const_mul, ← integral_sub hωI (hcI.integrableOn.const_mul 2)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      unfold weilJumpDensity
      ring
    rw [← e]
    exact hfoldI
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (261 / 1000)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 261 / 1000
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  have hu2M : Continuous fun x => u x ^ 2 * M x := (hu.continuous.pow 2).mul hMd.continuous
  have hu2Mc : HasCompactSupport fun x => u x ^ 2 * M x := (hasCompactSupport_sq huc).mul_right
  have i1 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (hu2M.mul hW).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i2 : Integrable fun x => u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    (hu2M.mul hG).integrable_of_hasCompactSupport hu2Mc.mul_right
  -- the pointwise potential
  have hpt : ∀ x, 1 / 250 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) := by
    intro x
    by_cases hx : |x| ≤ 13 / 50
    · have hpot := quarticGauge_potential_ge hx
      rw [← hMdef] at hpot
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      rw [hFx]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hnn x)
      have hM1 := hle x
      nlinarith [mul_le_mul_of_nonneg_left hpot hu2, mul_nonneg hu2 (by linarith : 0 ≤ 1 - M x)]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 250 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) =
      u x ^ 2 * M x * -poleFreeWeilOperator M x +
        2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) := fun x => by ring
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) :=
    (i1.add (i2.const_mul 2)).congr (Eventually.of_forall fun x => (e x).symm)
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2))) =
      (∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1
        (i2.const_mul 2), integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hjump, hint, hsplit]

/-! ### All profiles on `[−13/50, 13/50]` -/

/-- **Weil positivity on `[−13/50, 13/50]` from the quartic even gauge.** Every real `F ∈ C²_c`
vanishing outside `[−13/50, 13/50]` satisfies `Ẑ(F) ≥ (1/250) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_quarticFolded {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 13 / 50 < |x| → F x = 0) :
    1 / 250 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hse : ∀ x, 13 / 50 < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, 7 / 25 < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hsupp x (by linarith), hsupp (-x) (by rw [abs_neg]; linarith)]
    norm_num
  have he := fullZeroForm_ge_of_even_support_le_quartic (contDiff_evenPartReal hF)
    (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hse
  have ho := fullZeroForm_ge_of_odd_support_le (contDiff_oddPartReal hF)
    (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hso
  have hnn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hFc, integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−13/50, 13/50]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_quarticFolded {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(13 / 50)) (13 / 50)) :
    1 / 250 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 13 / 50 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_quarticFolded hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_quarticFolded him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **The quartic-fold floor**: `μ(A) ≥ 1/250` for every aperture `A ≤ 13/50`. -/
theorem one_div_250_le_ccmRestrictedWeilGroundEnergy_quartic {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 13 / 50) : 1 / 250 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(13 / 50)) (13 / 50) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_quarticFolded
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `13/50`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_quarticFolded {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 13 / 50 < A.1 := by
  by_contra hA
  have := one_div_250_le_ccmRestrictedWeilGroundEnergy_quartic (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
