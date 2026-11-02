import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential
import GaloisForLFunctions.RHTower.MarkovTwoCellTelescopingAndFortyFiveRatioPBAP

/-!
# A cubic ground state for odd logarithmic jumps

On the positive half-interval, the odd fold has kernel
`1/(2|x-y|) - 1/(2(x+y))`. The gauge `h(x)=x(1-4x²/5)` gives an exact
ground-state potential. Together with reflected and exterior killing, it
pays the uniform gap `log 2 + 7/5` for Lipschitz tests vanishing at both endpoints.
The origin is controlled by `h(x)≥x/5` and the test's linear vanishing;
squared differences control the jump diagonal.
-/

open Real MeasureTheory Set
open RHTower

noncomputable section
namespace GaloisForLFunctions.LatticeSectionTheory

private theorem neg_half_log_tangent {v s : ℝ} (hv : v < 1) (hs : 0 < s) :
    -(Real.log s + (1 - v) / s - 1) / 2 ≤ -Real.log (1 - v) / 2 := by
  have h := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hv) hs)
  rw [Real.log_div (sub_pos.mpr hv).ne' hs.ne'] at h
  linarith

private theorem log_forty_sevenths_lower : (87 / 50 : ℝ) ≤ Real.log (40 / 7) := by
  have h := log_sub_log_le_artanh_degree_nine (a := 1) (b := 7 / 5)
    (by norm_num) (by norm_num)
  norm_num at h
  have he : Real.log (40 / 7) = 3 * Real.log 2 - Real.log (7 / 5) := by
    rw [show (40 / 7 : ℝ) = 2 ^ (3 : ℕ) / (7 / 5) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

/-- A logarithmic barrier for the odd cubic gauge. -/
theorem odd_cubic_log_barrier {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (26 / 75 : ℝ) * v / (1 - 4 * v / 5) ≤ -Real.log (1 - v) / 2 := by
  have hd : 0 < 1 - 4 * v / 5 := by linarith
  apply (div_le_iff₀ hd).mpr
  by_cases h1 : v ≤ 1 / 4
  · have ht := neg_half_log_tangent (s := 1) hv1 (by norm_num)
    simp only [Real.log_one, div_one, zero_add] at ht
    have hm := mul_le_mul_of_nonneg_right ht hd.le
    nlinarith only [hm, hv0, mul_nonneg hv0 (show 1 / 4 - v ≥ 0 by linarith)]
  have hvq : 1 / 4 ≤ v := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : v ≤ 1 / 2
  · have ht := neg_half_log_tangent (s := 2 / 3) hv1 (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at ht
    have ha : 3 * v / 4 - 1 / 20 ≤ -Real.log (1 - v) / 2 := by
      linarith only [ht, four_panel_artanh_log_three_lower, four_panel_artanh_log_two_upper]
    have hm := mul_le_mul_of_nonneg_right ha hd.le
    nlinarith only [hm, hvq, h2, mul_nonneg (show 0 ≤ v - 1 / 4 by linarith)
      (show 0 ≤ 1 / 2 - v by linarith)]
  have hvh : 1 / 2 ≤ v := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : v ≤ 3 / 4
  · have ht := neg_half_log_tangent (s := 1 / 3) hv1 (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at ht
    have ha : 3 * v / 2 - 91 / 200 ≤ -Real.log (1 - v) / 2 := by
      linarith only [ht, four_panel_artanh_log_three_lower]
    have hm := mul_le_mul_of_nonneg_right ha hd.le
    nlinarith only [hm, hvh, h3, mul_nonneg (show 0 ≤ v - 1 / 2 by linarith)
      (show 0 ≤ 3 / 4 - v by linarith)]
  have hvt : 3 / 4 ≤ v := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : v ≤ 7 / 8
  · have ht := neg_half_log_tangent (s := 7 / 40) hv1 (by norm_num)
    have he : Real.log (7 / 40) = -Real.log (40 / 7) := by
      rw [show (7 / 40 : ℝ) = (40 / 7)⁻¹ by norm_num, Real.log_inv]
    rw [he] at ht
    have ha : 20 * v / 7 - 1041 / 700 ≤ -Real.log (1 - v) / 2 := by
      linarith only [ht, log_forty_sevenths_lower]
    have hm := mul_le_mul_of_nonneg_right ha hd.le
    nlinarith only [hm, hvt, h4, mul_nonneg (show 0 ≤ v - 3 / 4 by linarith)
      (show 0 ≤ 7 / 8 - v by linarith)]
  have hvs : 7 / 8 ≤ v := le_of_lt (lt_of_not_ge h4)
  by_cases h5 : v ≤ 15 / 16
  · have ht := neg_half_log_tangent (s := 3 / 32) hv1 (by norm_num)
    have he : Real.log (3 / 32) = Real.log 3 - 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [he] at ht
    have ha : 16 * v / 3 - 274 / 75 ≤ -Real.log (1 - v) / 2 := by
      linarith only [ht, four_panel_artanh_log_three_upper, Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_right ha hd.le
    nlinarith only [hm, hvs, h5, mul_nonneg (show 0 ≤ v - 7 / 8 by linarith)
      (show 0 ≤ 15 / 16 - v by linarith)]
  have hvf : 15 / 16 ≤ v := le_of_lt (lt_of_not_ge h5)
  have ht := neg_half_log_tangent (s := 1 / 16) hv1 (by norm_num)
  have he : Real.log (1 / 16) = -4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
    ring
  rw [he] at ht
  have ha : 8 * v - 153 / 25 ≤ -Real.log (1 - v) / 2 := by
    linarith only [ht, Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right ha hd.le
  nlinarith only [hm, hvf, hv1, mul_nonneg (show 0 ≤ v - 15 / 16 by linarith)
    (show 0 ≤ 1 - v by linarith)]

open ArithmeticIncidencePositivity

/-- The positive half of the odd cubic ground-state gauge. -/
def oddCubicGauge (x : ℝ) : ℝ := x * (1 - 4 * x ^ 2 / 5)

/-- The reflected principal jump kernel on the positive half-interval. -/
def principalOddKernel (x y : ℝ) : ℝ :=
  1 / (2 * |x - y|) - 1 / (2 * (x + y))

private theorem oddCubicGauge_eq (x : ℝ) :
    oddCubicGauge x = cubicGauge 0 1 0 (-4 / 5) x := by
  unfold oddCubicGauge cubicGauge
  ring

theorem oddCubicGauge_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 5 ≤ oddCubicGauge x := by
  have hs : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1]
  have hm := mul_nonneg hx (sub_nonneg.mpr hs)
  unfold oddCubicGauge
  nlinarith only [hm]

private theorem oddCubicGauge_divDiff {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |oddCubicGauge x - oddCubicGauge y| ≤ 17 / 5 * |x - y| := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
  have hxy : x * y ≤ 1 := (mul_le_mul hx.2 hy.2 hy.1 (by norm_num)).trans (by norm_num)
  have hp : |1 - 4 / 5 * (x ^ 2 + x * y + y ^ 2)| ≤ 17 / 5 := by
    rw [abs_le]
    constructor <;> nlinarith only [hx2, hy2, hxy, sq_nonneg x, sq_nonneg y,
      mul_nonneg hx.1 hy.1]
  have he : oddCubicGauge x - oddCubicGauge y =
      (x - y) * (1 - 4 / 5 * (x ^ 2 + x * y + y ^ 2)) := by
    unfold oddCubicGauge
    ring
  rw [he, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

private theorem principalOddKernel_bounds {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 ≤ principalOddKernel x y ∧ principalOddKernel x y ≤ 1 / (2 * |x - y|) := by
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hs : 0 < x + y := add_pos hx hy
  have hds : |x - y| ≤ x + y := by
    rw [abs_le]
    constructor <;> linarith only [hx, hy]
  unfold principalOddKernel
  constructor
  · apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hds])
  · linarith only [show 0 ≤ 1 / (2 * (x + y)) by positivity]

private theorem principalOddKernel_gauge_bound {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)| ≤ 17 / 10 := by
  by_cases he : x = y
  · simp only [he, sub_self, mul_zero, abs_zero]
    norm_num
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
  obtain ⟨hk0, hk1⟩ := principalOddKernel_bounds hx.1 hy.1 he
  have hg := oddCubicGauge_divDiff ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
  rw [abs_mul, abs_of_nonneg hk0]
  calc
    principalOddKernel x y * |oddCubicGauge x - oddCubicGauge y| ≤
        (1 / (2 * |x - y|)) * (17 / 5 * |x - y|) :=
      mul_le_mul hk1 hg (abs_nonneg _) (by positivity)
    _ = 17 / 10 := by field_simp; ring

/-- The exact principal potential of the cubic gauge. -/
theorem principalOddKernel_gauge_integral {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ y in Ioo (0 : ℝ) 1,
      principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)) =
        cubicSurplusMain 1 0 (-4 / 5) 1 x := by
  simp_rw [principalOddKernel, oddCubicGauge_eq]
  rw [← integral_Ioc_eq_integral_Ioo]
  exact (integral_principalSurplus_cubicGauge 0 1 0 (-4 / 5) hx hx1).2

/-- Exterior killing and the cubic potential pay a uniform logarithmic spectral gap. -/
theorem oddCubicGauge_potential_lower {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Real.log 2 + 7 / 5 ≤
      Real.log 2 - Real.log (1 - x ^ 2) / 2 + (Real.log (x + 1) - Real.log x) +
        cubicSurplusMain 1 0 (-4 / 5) 1 x / oddCubicGauge x := by
  have hx2 : x ^ 2 < 1 := by nlinarith only [hx, hx1]
  have hd : 0 < 1 - 4 * x ^ 2 / 5 := by linarith only [hx2]
  have hd5 : 5 - x ^ 2 * 4 ≠ 0 := by linarith only [hd]
  have he : (Real.log (x + 1) - Real.log x) +
      cubicSurplusMain 1 0 (-4 / 5) 1 x / oddCubicGauge x =
      7 / 5 - (26 / 75 : ℝ) * x ^ 2 / (1 - 4 * x ^ 2 / 5) := by
    unfold cubicSurplusMain oddCubicGauge
    field_simp [hx.ne', hd5]
    ring
  have hb := odd_cubic_log_barrier (sq_nonneg x) hx2
  linarith only [he, hb]

private theorem cubic_transform_bound {F : ℝ → ℝ} {K x y : ℝ}
    (hF0 : F 0 = 0)
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |F x ^ 2 / oddCubicGauge x *
      (principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y))| ≤ 17 / 2 * K ^ 2 := by
  have hg := oddCubicGauge_lower hx.1.le hx.2.le
  have hg0 : 0 < oddCubicGauge x := by linarith only [hg, hx.1]
  have hf := hFL x ⟨hx.1.le, hx.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩
  rw [hF0, sub_zero, sub_zero, abs_of_pos hx.1] at hf
  have hf2 : F x ^ 2 ≤ K ^ 2 * x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) hf 2
    simpa only [sq_abs, mul_pow] using h
  have hs : x ^ 2 ≤ x := by nlinarith only [hx.1, hx.2]
  have hq : F x ^ 2 / oddCubicGauge x ≤ 5 * K ^ 2 := by
    rw [div_le_iff₀ hg0]
    nlinarith only [hf2, mul_le_mul_of_nonneg_left hs (sq_nonneg K),
      mul_le_mul_of_nonneg_left hg (show 0 ≤ 5 * K ^ 2 by positivity)]
  rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hg0.le)]
  calc
    F x ^ 2 / oddCubicGauge x *
        |principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)| ≤
        (5 * K ^ 2) * (17 / 10) :=
      mul_le_mul hq (principalOddKernel_gauge_bound hx hy) (abs_nonneg _) (by positivity)
    _ = 17 / 2 * K ^ 2 := by ring

private theorem principal_energy_bound {F : ℝ → ℝ} {K x y : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |principalOddKernel x y * (F x - F y) ^ 2| ≤ K ^ 2 / 2 := by
  by_cases he : x = y
  · simp only [he, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, abs_zero]
    positivity
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hd1 : |x - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]
  obtain ⟨hk0, hk1⟩ := principalOddKernel_bounds hx.1 hy.1 he
  have hf := hFL x ⟨hx.1.le, hx.2.le⟩ y ⟨hy.1.le, hy.2.le⟩
  have hf2 : (F x - F y) ^ 2 ≤ K ^ 2 * |x - y| ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x - F y)) hf 2
    simpa only [sq_abs, mul_pow] using h
  rw [abs_mul, abs_of_nonneg hk0, abs_of_nonneg (sq_nonneg _)]
  calc
    principalOddKernel x y * (F x - F y) ^ 2 ≤
        1 / (2 * |x - y|) * (K ^ 2 * |x - y| ^ 2) :=
      mul_le_mul hk1 hf2 (sq_nonneg _) (by positivity)
    _ = K ^ 2 / 2 * |x - y| := by field_simp
    _ ≤ K ^ 2 / 2 := by nlinarith only [mul_le_mul_of_nonneg_left hd1 (sq_nonneg K)]

private theorem integrable_unit_square {G : ℝ × ℝ → ℝ} {C : ℝ} (hG : Measurable G)
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, |G (x, y)| ≤ C) :
    Integrable G ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hG.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [Real.norm_eq_abs]
  exact hb p.1 hp.1 p.2 hp.2

/-- Lipschitz differences cancel the diagonal singularity of the reflected jump kernel. -/
theorem principalOddKernel_energy_integrable {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    Integrable (fun p : ℝ × ℝ => principalOddKernel p.1 p.2 * (F p.1 - F p.2) ^ 2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply integrable_unit_square (C := K ^ 2 / 2)
  · unfold principalOddKernel
    fun_prop
  · intro x hx y hy
    exact principal_energy_bound hFL hx hy

/-- The odd cubic gauge converts reflected interior jumps into its exact potential. -/
theorem principalOddKernel_energy_ge {F : ℝ → ℝ} (hFc : Continuous F) (hF0 : F 0 = 0)
    {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    IntegrableOn (fun x => F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x)
        (Ioo (0 : ℝ) 1) ∧
      2 * (∫ x in Ioo (0 : ℝ) 1,
        F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x) ≤
        ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
          principalOddKernel x y * (F x - F y) ^ 2 := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 ^ 2 / oddCubicGauge p.1 *
    (principalOddKernel p.1 p.2 * (oddCubicGauge p.1 - oddCubicGauge p.2))
  let E : ℝ × ℝ → ℝ := fun p => principalOddKernel p.1 p.2 * (F p.1 - F p.2) ^ 2
  have hmG : Measurable G := by unfold G principalOddKernel oddCubicGauge; fun_prop
  have hmE : Measurable E := by unfold E principalOddKernel; fun_prop
  have hIG := integrable_unit_square hmG (fun x hx y hy => cubic_transform_bound hF0 hFL hx hy)
  have hIGs : Integrable (fun p : ℝ × ℝ => G (p.2, p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    integrable_unit_square (hmG.comp (measurable_snd.prodMk measurable_fst))
      (fun x hx y hy => cubic_transform_bound hF0 hFL hy hx)
  have hIE := integrable_unit_square hmE (fun x hx y hy => principal_energy_bound hFL hx hy)
  have hp : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      G (x, y) + G (y, x) ≤ E (x, y) := by
    intro x hx y hy
    by_cases he : x = y
    · simp only [he, G, E, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, le_refl]
    have hhx : 0 < oddCubicGauge x := by
      linarith only [oddCubicGauge_lower hx.1.le hx.2.le, hx.1]
    have hhy : 0 < oddCubicGauge y := by
      linarith only [oddCubicGauge_lower hy.1.le hy.2.le, hy.1]
    have hk := (principalOddKernel_bounds hx.1 hy.1 he).1
    have hb := mul_le_mul_of_nonneg_left (sq_sub_ge_groundState (F x) (F y) hhx hhy) hk
    have hcomm : principalOddKernel y x = principalOddKernel x y := by
      unfold principalOddKernel
      rw [abs_sub_comm, add_comm]
    have heq : G (x, y) + G (y, x) = principalOddKernel x y *
        (F x ^ 2 * (1 - oddCubicGauge y / oddCubicGauge x) +
          F y ^ 2 * (1 - oddCubicGauge x / oddCubicGauge y)) := by
      dsimp [G]
      rw [hcomm]
      field_simp
    rw [heq]
    exact hb
  have hcmp : (∫ p, G p + G (p.2, p.1)
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ≤
      ∫ p, E p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply integral_mono_ae (hIG.add hIGs) hIE
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp'
    exact hp p.1 hp'.1 p.2 hp'.2
  have hinner : ∀ x ∈ Ioo (0 : ℝ) 1, (∫ y in Ioo (0 : ℝ) 1, G (x, y)) =
      F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x := by
    intro x hx
    dsimp [G]
    rw [integral_const_mul, principalOddKernel_gauge_integral hx.1 hx.2.le]
  have hIP : IntegrableOn (fun x => F x ^ 2 / oddCubicGauge x *
      cubicSurplusMain 1 0 (-4 / 5) 1 x) (Ioo (0 : ℝ) 1) := by
    apply hIG.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hinner x hx
  refine ⟨hIP, ?_⟩
  rw [integral_add hIG hIGs,
    ← integral_integral (f := fun x y => G (x, y)) hIG,
    ← integral_integral (f := fun x y => G (y, x)) hIGs,
    ← integral_integral (f := fun x y => E (x, y)) hIE] at hcmp
  have hs : (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (y, x)) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (x, y) :=
    integral_integral_swap (f := fun x y => G (y, x)) hIGs
  change (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (x, y)) +
      (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (y, x)) ≤ _ at hcmp
  rw [hs, setIntegral_congr_fun measurableSet_Ioo hinner] at hcmp
  linarith only [hcmp]

/-- Killing from reflected and exterior logarithmic jumps. -/
def oddLogKilling (x : ℝ) : ℝ :=
  Real.log 2 - Real.log (1 - x ^ 2) / 2 + Real.log (x + 1) - Real.log x

private theorem oddLogKilling_bounds {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    0 ≤ oddLogKilling x ∧ oddLogKilling x ≤ 1 + 1 / x + 1 / (2 * (1 - x)) := by
  have hx2 : x ^ 2 < 1 := by nlinarith only [hx, hx1]
  have hp : 0 < 1 - x ^ 2 := by linarith only [hx2]
  have hl0 : Real.log (1 - x ^ 2) ≤ 0 := by
    have h := Real.log_le_log hp (show 1 - x ^ 2 ≤ 1 by nlinarith only [sq_nonneg x])
    simpa only [Real.log_one] using h
  have hr0 : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl2u : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  have hr : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < x + 1) hx)
    rw [Real.log_div (by linarith) hx.ne'] at h
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rwa [he] at h
  have hl : -Real.log (1 - x ^ 2) ≤ 1 / (1 - x) := by
    have hm := Real.log_le_log (sub_pos.mpr hx1)
      (show 1 - x ≤ 1 - x ^ 2 by nlinarith only [hx, hx1])
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hx1))
    rw [Real.log_inv] at h
    simp only [one_div]
    linarith only [hm, h]
  unfold oddLogKilling
  constructor
  · linarith only [hl0, hr0, hl2]
  · have he : 1 / (2 * (1 - x)) = (1 / (1 - x)) / 2 := by field_simp
    rw [he]
    linarith only [hl2u, hr, hl]

private theorem oddLogKilling_mass_bound {F : ℝ → ℝ} {K x : ℝ}
    (hF0 : F 0 = 0) (hF1 : F 1 = 0)
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |F x ^ 2 * oddLogKilling x| ≤ 5 / 2 * K ^ 2 := by
  have h0 := hFL x ⟨hx.1.le, hx.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hFL x ⟨hx.1.le, hx.2.le⟩ 1 ⟨zero_le_one, le_rfl⟩
  rw [hF0, sub_zero, sub_zero, abs_of_pos hx.1] at h0
  rw [hF1, sub_zero, abs_of_neg (sub_neg.mpr hx.2)] at h1
  have hs0 : F x ^ 2 ≤ K ^ 2 * x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) h0 2
    simpa only [sq_abs, mul_pow] using h
  have hs1 : F x ^ 2 ≤ K ^ 2 * (1 - x) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) h1 2
    simp only [sq_abs, mul_pow, neg_sq] at h
    nlinarith only [h]
  have hm0 : F x ^ 2 / x ≤ K ^ 2 := by
    rw [div_le_iff₀ hx.1]
    have hxx : x ^ 2 ≤ x := by nlinarith only [hx.1, hx.2]
    exact hs0.trans (mul_le_mul_of_nonneg_left hxx (sq_nonneg K))
  have hm1 : F x ^ 2 / (1 - x) ≤ K ^ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr hx.2)]
    have hxx : (1 - x) ^ 2 ≤ 1 - x := by nlinarith only [hx.1, hx.2]
    exact hs1.trans (mul_le_mul_of_nonneg_left hxx (sq_nonneg K))
  have hm : F x ^ 2 ≤ K ^ 2 := by
    have hxx : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    exact hs0.trans ((mul_le_mul_of_nonneg_left hxx (sq_nonneg K)).trans_eq (mul_one _))
  obtain ⟨hk0, hk1⟩ := oddLogKilling_bounds hx.1 hx.2
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hk0)]
  have h := mul_le_mul_of_nonneg_left hk1 (sq_nonneg (F x))
  have he : F x ^ 2 * (1 + 1 / x + 1 / (2 * (1 - x))) =
      F x ^ 2 + F x ^ 2 / x + (F x ^ 2 / (1 - x)) / 2 := by
    field_simp
  rw [he] at h
  linarith only [h, hm, hm0, hm1]

/-- Vanishing at the endpoints controls both logarithmic killing singularities. -/
theorem oddLogKilling_integrable {F : ℝ → ℝ} (hFc : Continuous F)
    (hF0 : F 0 = 0) (hF1 : F 1 = 0) {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    IntegrableOn (fun x => F x ^ 2 * oddLogKilling x) (Ioo (0 : ℝ) 1) := by
  have hm : Measurable (fun x => F x ^ 2 * oddLogKilling x) := by
    unfold oddLogKilling
    fun_prop
  refine Measure.integrableOn_of_bounded (M := 5 / 2 * K ^ 2) (by simp)
    hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  exact oddLogKilling_mass_bound hF0 hF1 hFL hx

/-- The folded logarithmic jump count has gap `log 2 + 7/5` on odd Dirichlet tests. -/
theorem folded_logarithmic_jump_gap {F : ℝ → ℝ} (hFc : Continuous F)
    (hF0 : F 0 = 0) (hF1 : F 1 = 0) {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    (Real.log 2 + 7 / 5) * (2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2) ≤
      (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2) +
      2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x := by
  obtain ⟨hIP, hgap⟩ := principalOddKernel_energy_ge hFc hF0 hFL
  have hIK := oddLogKilling_integrable hFc hF0 hF1 hFL
  have hIF : IntegrableOn (fun x => F x ^ 2) (Ioo (0 : ℝ) 1) :=
    (hFc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hp : (Real.log 2 + 7 / 5) * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2) ≤
      (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x) +
        ∫ x in Ioo (0 : ℝ) 1,
          F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x := by
    rw [← integral_const_mul, ← integral_add hIK hIP]
    apply setIntegral_mono_on (hIF.const_mul _) (hIK.add hIP) measurableSet_Ioo
    intro x hx
    have h := mul_le_mul_of_nonneg_left (oddCubicGauge_potential_lower hx.1 hx.2)
      (sq_nonneg (F x))
    unfold oddLogKilling
    change (Real.log 2 + 7 / 5) * F x ^ 2 ≤
      F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2 + Real.log (x + 1) - Real.log x) +
        F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x
    calc
      (Real.log 2 + 7 / 5) * F x ^ 2 = F x ^ 2 * (Real.log 2 + 7 / 5) := by ring
      _ ≤ F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2 +
          (Real.log (x + 1) - Real.log x) +
          cubicSurplusMain 1 0 (-4 / 5) 1 x / oddCubicGauge x) := h
      _ = F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2 + Real.log (x + 1) - Real.log x) +
          F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x := by ring
  nlinarith only [hp, hgap]

end GaloisForLFunctions.LatticeSectionTheory
