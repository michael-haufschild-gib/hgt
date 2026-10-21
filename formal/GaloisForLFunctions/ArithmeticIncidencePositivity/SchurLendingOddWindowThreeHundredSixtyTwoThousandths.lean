import GaloisForLFunctions.ArithmeticIncidencePositivity.OffStripGroundStateSchurRectangles
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurLendingWindowNumeratorBounds

/-!
# Odd-sector Weil positivity on `[−181/500, 181/500]`: the middle of the window borrows

Past `9/25` the binding region of the window is its archimedean middle, `x ≈ 0.2`, where the
ground-state potential has the least slack above the pole. Two Schur rectangles of the off-strip
transform (`OffStripGroundStateSchurRectangles`) lend it potential:

* from the **origin region** `H_A = [11/250, 7/100]`, where the killing `log((x + r)/x)` is large,
  with `β_A = 9/25`, `s_A = 33/1000`: on `Z × H_A` the kernel is at least `31/50` and
  `q = h(y)/h(x) ≥ 1/3`;
* from the **prime strip** `H_B = [207/625, 181/500]`, where the even part of the atom
  (`PrimeAtomEvenPartPotential`, `t = 4/5`) leaves the potential `(49/125) h − 97/10000 ≥ 0.0057`, with
  `β_B = 1`, `s_B = 89/500`: on `Z × H_B` the kernel is at least `5/4` and `q ≥ 1/2`.

Both lend to `Z = [7/50, 27/100]`, which gains `(24/25)(s_A|H_A| + s_B|H_B|) ≥ 0.0060` per unit of
mass, `86%` of it from the strip: the origin pairs are far apart and the gauge ratio is small, so
`kβq²/(k + βq) ≤ kq² ≈ 0.07`. In units of the gauge the numerator may drop to `−38/100000` on `Z`;
it must exceed `173/100000` on `H_A` and needs nothing extra on `H_B`
(`lendFoldWindow_potential_ge`). The gauge is that of the window `9/25` dilated to `181/500`.

**Theorem** (`fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`). Every odd
`F ∈ C²_c` vanishing outside `[−181/500, 181/500]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The gauge on the three intervals -/

/-- The gauge on the borrowing interval: `641/10000 ≤ h ≤ 778/10000` on `[7/50, 27/100]`. -/
theorem lendFoldGauge_middle_bounds {x : ℝ} (h1 : 7 / 50 ≤ x) (h2 : x ≤ 27 / 100) :
    641 / 10000 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x ∧ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x ≤ 778 / 10000 := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  constructor
  · nlinarith [mul_nonneg hm (by linarith : (0 : ℝ) ≤ x), mul_nonneg hm (sq_nonneg x),
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 3, pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 4]
  · nlinarith [sq_nonneg (x - 23 / 100), mul_nonneg hm (sq_nonneg (x - 23 / 100)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg (x - 23 / 100)),
      mul_nonneg (sq_nonneg x) (sq_nonneg (x - 23 / 100))]

/-- The gauge on the origin hub: `2594/100000 ≤ h ≤ 385/10000` on `[11/250, 7/100]`. -/
theorem lendFoldGauge_hubA_bounds {y : ℝ} (h1 : 11 / 250 ≤ y) (h2 : y ≤ 7 / 100) :
    2594 / 100000 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y ∧ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y ≤ 385 / 10000 := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  constructor <;> nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 11 / 250) h1 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y) h2 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 11 / 250) h1 4,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y) h2 4, mul_nonneg hm (by linarith : (0 : ℝ) ≤ y)]

/-- The gauge on the strip: `h ≥ 79/2000` on `[3311/10000, 181/500]`. -/
theorem lendFoldGauge_strip_ge {x : ℝ} (h1 : 3311 / 10000 ≤ x) (h2 : x ≤ 181 / 500) :
    79 / 2000 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 3311 / 10000) h1 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 3311 / 10000) h1 4,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 4, mul_nonneg hm (by linarith : (0 : ℝ) ≤ x)]

/-! ### The two lending rectangles -/

/-- **The kernel of the origin rectangle.** For `x ∈ [7/50, 27/100]`, `y ∈ [11/250, 7/100]`:
`k(x, y) ≥ 31/50`, from `k ≥ y/(x² − y²) + 2y/48 − (x + y)³/250`. -/
theorem surplusKernel_ge_lendHubA {x y : ℝ} (hx1 : 7 / 50 ≤ x) (hx2 : x ≤ 27 / 100)
    (hy1 : 11 / 250 ≤ y) (hy2 : y ≤ 7 / 100) : 31 / 50 ≤ surplusKernel x y := by
  have hxy : y < x := by linarith
  have h := abs_surplusKernel_sub_secondOrder_le (show 0 < x by linarith) (show 0 < y by linarith)
    (by linarith : x ≠ y) (by linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < x - y), abs_le] at h
  have hA : 6195 / 10000 ≤ 1 / (2 * (x - y)) - 1 / (2 * (x + y)) := by
    rw [div_sub_div _ _ (by linarith) (by linarith), le_div_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul hx2 hx2 (by linarith) (by norm_num), mul_le_mul hy1 hy1 (by norm_num)
      (by linarith)]
  have hC : (x + y) ^ 3 ≤ (34 / 100) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hB : 88 / 1000 / 48 ≤ (x + y - (x - y)) / 48 + x * y / 8 := by nlinarith
  linarith [h.1]

/-- **The kernel of the strip rectangle.** For `x ∈ [7/50, 27/100]`, `y ∈ [207/625, 181/500]`:
`k(x, y) ≥ 5/4`, from `k ≥ x/(y² − x²) − (x + y)³/250`. -/
theorem surplusKernel_ge_lendHubB {x y : ℝ} (hx1 : 7 / 50 ≤ x) (hx2 : x ≤ 27 / 100)
    (hy1 : 207 / 625 ≤ y) (hy2 : y ≤ 181 / 500) : 5 / 4 ≤ surplusKernel x y := by
  have h := abs_surplusKernel_sub_secondOrder_le (show 0 < x by linarith) (show 0 < y by linarith)
    (by linarith : x ≠ y) (by linarith)
  rw [abs_of_neg (by linarith : x - y < 0), neg_sub, abs_le] at h
  have hA : 1256 / 1000 ≤ 1 / (2 * (y - x)) - 1 / (2 * (x + y)) := by
    rw [div_sub_div _ _ (by linarith) (by linarith), le_div_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul hy2 hy2 (by linarith) (by norm_num), mul_le_mul hx1 hx1 (by norm_num)
      (by linarith)]
  have hC : (x + y) ^ 3 ≤ (632 / 1000) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hB : 0 ≤ (x + y - (y - x)) / 48 + x * y / 8 := by nlinarith
  linarith [h.1]

/-- **The Schur weight of the origin rectangle**: `kβq²/(k + βq) ≥ 33/1000`, `β = 9/25`,
`q = h(y)/h(x) ≥ 1/3`. -/
theorem lendFold_pairWeightA_ge {x y : ℝ} (hx1 : 7 / 50 ≤ x) (hx2 : x ≤ 27 / 100)
    (hy1 : 11 / 250 ≤ y) (hy2 : y ≤ 7 / 100) :
    33 / 1000 ≤ surplusKernel x y * (9 / 25) * (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x) ^ 2 /
      (surplusKernel x y + 9 / 25 * (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x)) := by
  have hk := surplusKernel_ge_lendHubA hx1 hx2 hy1 hy2
  obtain ⟨hx3, hx4⟩ := lendFoldGauge_middle_bounds hx1 hx2
  obtain ⟨hy3, -⟩ := lendFoldGauge_hubA_bounds hy1 hy2
  have hq : 1 / 3 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  set q := quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x with hqdef
  set k := surplusKernel x y with hkdef
  clear_value q k
  rw [le_div_iff₀ (by nlinarith)]
  have e1 : 0 ≤ (k - 31 / 50) * (9 / 25 * q ^ 2 - 33 / 1000) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hq)]

/-- **The Schur weight of the strip rectangle**: `kβq²/(k + βq) ≥ 89/500`, `β = 1`,
`q = h(y)/h(x) ≥ 1/2`. -/
theorem lendFold_pairWeightB_ge {x y : ℝ} (hx1 : 7 / 50 ≤ x) (hx2 : x ≤ 27 / 100)
    (hy1 : 207 / 625 ≤ y) (hy2 : y ≤ 181 / 500) :
    89 / 500 ≤ surplusKernel x y * 1 * (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x) ^ 2 /
      (surplusKernel x y + 1 * (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x)) := by
  have hk := surplusKernel_ge_lendHubB hx1 hx2 hy1 hy2
  obtain ⟨hx3, hx4⟩ := lendFoldGauge_middle_bounds hx1 hx2
  have hy3 := lendFoldGauge_strip_ge (by linarith) hy2
  have hq : 1 / 2 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  set q := quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) y / quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x with hqdef
  set k := surplusKernel x y with hkdef
  clear_value q k
  rw [le_div_iff₀ (by nlinarith)]
  have e1 : 0 ≤ (k - 5 / 4) * (q ^ 2 - 89 / 500) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hq)]

/-! ### The weights of the potential -/

/-- The indicator of the strip `[log 2 − 181/500, 181/500]`. -/
def lendStripWeight (x : ℝ) : ℝ :=
  (Icc (Real.log 2 - 181 / 500) (181 / 500)).indicator (fun _ => (1 : ℝ)) x

/-- The lending redistribution: `Z = [7/50, 27/100]` gains `s_A|H_A| + s_B|H_B|`, the origin hub
`[11/250, 7/100]` pays `β_A|Z|`, the strip hub `[207/625, 181/500]` pays `β_B|Z|`. -/
def schurLendWeight (x : ℝ) : ℝ :=
  (33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500)) *
      (Icc (7 / 50 : ℝ) (27 / 100)).indicator (fun _ => (1 : ℝ)) x -
    9 / 25 * (13 / 100) * (Icc (11 / 250 : ℝ) (7 / 100)).indicator (fun _ => (1 : ℝ)) x -
    13 / 100 * (Icc (207 / 625 : ℝ) (181 / 500)).indicator (fun _ => (1 : ℝ)) x

theorem integral_sq_mul_lendStripWeight {F : ℝ → ℝ} (hF : Integrable fun x => F x ^ 2) :
    IntegrableOn (fun x => F x ^ 2 * lendStripWeight x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), F x ^ 2 * lendStripWeight x =
        ∫ x in (Real.log 2 - 181 / 500)..(181 / 500), F x ^ 2 := by
  have e : (fun x => F x ^ 2 * lendStripWeight x) =
      (Icc (Real.log 2 - 181 / 500) (181 / 500)).indicator (fun x => F x ^ 2) := by
    funext x
    unfold lendStripWeight
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  have hi := hF.indicator (measurableSet_Icc (a := Real.log 2 - 181 / 500) (b := (181 / 500 : ℝ)))
  rw [e]
  refine ⟨hi.integrableOn, ?_⟩
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have i1 : Ioi (0 : ℝ) ∩ Icc (Real.log 2 - 181 / 500) (181 / 500) =
      Icc (Real.log 2 - 181 / 500) (181 / 500) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < Real.log 2 - 181 / 500 by linarith).trans_le hx.1
  rw [setIntegral_indicator measurableSet_Icc, i1, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

theorem integral_sq_mul_schurLendWeight {F : ℝ → ℝ} (hF : Integrable fun x => F x ^ 2) :
    IntegrableOn (fun x => F x ^ 2 * schurLendWeight x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), F x ^ 2 * schurLendWeight x =
        (33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500)) * (∫ x in Icc (7 / 50 : ℝ) (27 / 100), F x ^ 2) -
          9 / 25 * (13 / 100) * (∫ y in Icc (11 / 250 : ℝ) (7 / 100), F y ^ 2) -
          13 / 100 * ∫ y in Icc (207 / 625 : ℝ) (181 / 500), F y ^ 2 := by
  have e : (fun x => F x ^ 2 * schurLendWeight x) = fun x =>
      (33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500)) * (Icc (7 / 50 : ℝ) (27 / 100)).indicator (fun x => F x ^ 2) x -
        9 / 25 * (13 / 100) * (Icc (11 / 250 : ℝ) (7 / 100)).indicator (fun x => F x ^ 2) x -
        13 / 100 * (Icc (207 / 625 : ℝ) (181 / 500)).indicator (fun x => F x ^ 2) x := by
    funext x
    unfold schurLendWeight
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  have hZ := (hF.indicator (measurableSet_Icc (a := (7 / 50 : ℝ)) (b := 27 / 100))).const_mul
    (33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500))
  have hA := (hF.indicator (measurableSet_Icc (a := (11 / 250 : ℝ)) (b := 7 / 100))).const_mul
    (9 / 25 * (13 / 100))
  have hB := (hF.indicator (measurableSet_Icc (a := (207 / 625 : ℝ)) (b := 181 / 500))).const_mul
    (13 / 100)
  have hZA : Integrable (fun x =>
      (33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500)) *
        (Icc (7 / 50 : ℝ) (27 / 100)).indicator (fun x => F x ^ 2) x -
      9 / 25 * (13 / 100) * (Icc (11 / 250 : ℝ) (7 / 100)).indicator (fun x => F x ^ 2) x) :=
    hZ.sub hA
  rw [e]
  refine ⟨(hZA.sub hB).integrableOn, ?_⟩
  have i1 : Ioi (0 : ℝ) ∩ Icc (7 / 50) (27 / 100) = Icc (7 / 50) (27 / 100) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < 7 / 50 by norm_num).trans_le hx.1
  have i2 : Ioi (0 : ℝ) ∩ Icc (11 / 250) (7 / 100) = Icc (11 / 250) (7 / 100) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < 11 / 250 by norm_num).trans_le hx.1
  have i3 : Ioi (0 : ℝ) ∩ Icc (207 / 625) (181 / 500) = Icc (207 / 625) (181 / 500) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < 207 / 625 by norm_num).trans_le hx.1
  rw [integral_sub hZA.integrableOn hB.integrableOn,
    integral_sub hZ.integrableOn hA.integrableOn, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    setIntegral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Icc,
    setIntegral_indicator measurableSet_Icc, i1, i2, i3]

theorem schurLendWeight_of_middle {x : ℝ} (h1 : 7 / 50 ≤ x) (h2 : x ≤ 27 / 100) :
    schurLendWeight x = 33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500) := by
  unfold schurLendWeight
  rw [Set.indicator_of_mem (show x ∈ Icc (7 / 50 : ℝ) (27 / 100) from ⟨h1, h2⟩),
    Set.indicator_of_notMem (show x ∉ Icc (11 / 250 : ℝ) (7 / 100) from fun h => by linarith [h.2]),
    Set.indicator_of_notMem (show x ∉ Icc (207 / 625 : ℝ) (181 / 500) from fun h => by linarith [h.1])]
  ring

theorem schurLendWeight_of_hubA {x : ℝ} (h1 : 11 / 250 ≤ x) (h2 : x ≤ 7 / 100) :
    schurLendWeight x = -(9 / 25 * (13 / 100)) := by
  unfold schurLendWeight
  rw [Set.indicator_of_notMem (show x ∉ Icc (7 / 50 : ℝ) (27 / 100) from fun h => by linarith [h.1]),
    Set.indicator_of_mem (show x ∈ Icc (11 / 250 : ℝ) (7 / 100) from ⟨h1, h2⟩),
    Set.indicator_of_notMem (show x ∉ Icc (207 / 625 : ℝ) (181 / 500) from fun h => by linarith [h.1])]
  ring

theorem schurLendWeight_of_hubB {x : ℝ} (h1 : 207 / 625 ≤ x) (h2 : x ≤ 181 / 500) :
    schurLendWeight x = -(13 / 100) := by
  unfold schurLendWeight
  rw [Set.indicator_of_notMem (show x ∉ Icc (7 / 50 : ℝ) (27 / 100) from fun h => by linarith [h.2]),
    Set.indicator_of_notMem (show x ∉ Icc (11 / 250 : ℝ) (7 / 100) from fun h => by linarith [h.2]),
    Set.indicator_of_mem (show x ∈ Icc (207 / 625 : ℝ) (181 / 500) from ⟨h1, h2⟩)]
  ring

theorem schurLendWeight_of_off {x : ℝ}
    (h : x < 11 / 250 ∨ (7 / 100 < x ∧ x < 7 / 50) ∨ (27 / 100 < x ∧ x < 207 / 625)) :
    schurLendWeight x = 0 := by
  have hZ : x ∉ Icc (7 / 50 : ℝ) (27 / 100) := fun h' => by
    rcases h with h | h | h <;> linarith [h'.1, h'.2]
  have hA : x ∉ Icc (11 / 250 : ℝ) (7 / 100) := fun h' => by
    rcases h with h | h | h <;> linarith [h'.1, h'.2]
  have hB : x ∉ Icc (207 / 625 : ℝ) (181 / 500) := fun h' => by
    rcases h with h | h | h <;> linarith [h'.1, h'.2]
  unfold schurLendWeight
  rw [Set.indicator_of_notMem hZ, Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]
  ring

/-! ### The potential -/

/-- **The potential on `(0, 181/500]`.** The killing, the mixed surplus potential, `θ = 24/25`, the
prime potential `(49/125) 1_S`, the lending redistribution `(24/25) W`, and the plateau potential of
radius `7241/20000`, with the second-order expansions, exceed `347/20000`. -/
theorem lendFoldWindow_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 181 / 500) :
    347 / 20000 ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 181 / 500)) +
        (((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (181 / 500) x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (Real.log 2 - 181 / 500) (181 / 500) x) + 49 / 125 * lendStripWeight x + 24 / 25 * schurLendWeight x) +
        (archLevyAntideriv (7241 / 20000 - x) + archLevyAntideriv (7241 / 20000 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := lendFoldGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge_second (1 / 500) (59 / 100) (-29 / 30) (-21 / 100)
    (-16 / 7) hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr =>
      lendFoldGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge_second hx0 (by linarith)
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 181 / 500 by linarith)
  have hΩa := archLevyAntideriv_ge_second (show 0 < 7241 / 20000 - x by linarith) (by linarith)
  have hΩb := archLevyAntideriv_ge_second (show 0 < 7241 / 20000 + x by linarith) (by linarith)
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_le_11448
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hκ : Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi ≤ 241517 / 100000 := by
    linarith
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e1 : Real.log (x / 4) = Real.log x - 2 * Real.log 2 := by
    rw [Real.log_div hx0.ne' (by norm_num), l4]
  have e2 : Real.log ((x + 181 / 500) / 4) = Real.log (x + 181 / 500) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((7241 / 20000 - x) / 4) = Real.log (7241 / 20000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((7241 / 20000 + x) / 4) = Real.log (7241 / 20000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 181 / 500) - Real.log x) +
    (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x)) - κ - 1 / 40000 -
    (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 +
      (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (181 / 500) x with hUdef
  set U' := surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (Real.log 2 - 181 / 500) (181 / 500) x with hU'def
  have hkey : quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x * (V - 347 / 20000) +
      (quarticSurplusMain (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x +
        firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x -
        16 / 25 * (4 / 125 * (181 / 500) ^ 5)) = lendFoldNumerator κ x := by
    rw [hV]; unfold lendFoldNumerator quarticSurplusMain cubicSurplusMain lendFoldPoly quarticGauge
    ring
  -- below the strip the off-strip potential is `U`; on the strip it loses at most `97/10000`
  have hUU : x < Real.log 2 - 181 / 500 → U' = U := fun hS => by
    rw [hU'def, hUdef]; unfold surplusPotentialOff; rw [if_pos hS]
  have hstrip : Real.log 2 - 181 / 500 ≤ x →
      quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x * U ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x * ((1 - 24 / 25) * U + 24 / 25 * U') + 97 / 10000 := fun hpx => by
    have hloss := mul_surplusPotential_le_off_add (h := quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (a₀ := 1 / 500) (L := 16 / 25)
      (by linarith) hpx hxr (by norm_num) (continuous_quarticGauge _ _ _ _ _) (by norm_num) hh
      (by norm_num) (fun y hy0 hyr => by
        rw [quarticGauge_sub, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (lendFoldGauge_divDiff_le hx0.le hxr hy0.le hyr)
          (abs_nonneg _))
    have hd0 : 0 ≤ 181 / 500 - (Real.log 2 - 181 / 500) := by linarith
    have hd1 : 181 / 500 - (Real.log 2 - 181 / 500) ≤ 30853 / 1000000 := by linarith
    have hd : 24 / 25 * (16 / 25 * (181 / 500 - (Real.log 2 - 181 / 500)) *
        (1 / 2 + (181 / 500 - (Real.log 2 - 181 / 500)) / 4)) ≤ 97 / 10000 := by
      have hm := mul_le_mul hd1 (show 1 / 2 + (181 / 500 - (Real.log 2 - 181 / 500)) / 4 ≤
        1 / 2 + 30853 / 1000000 / 4 by linarith) (by linarith) (by norm_num)
      linarith only [hm]
    rw [hU'def, hUdef]
    linarith only [hloss, hd]
  clear_value V U U'
  set g := quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x with hg
  set N := lendFoldNumerator κ x with hNdef
  set I := lendStripWeight x with hIdef
  set W := schurLendWeight x with hWdef
  clear_value g N I W
  -- the seven regions of the window
  have hcase : g * U ≤ g * ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W) + N := by
    by_cases hS : x < Real.log 2 - 181 / 500
    · have hI : I = 0 := by
        rw [hIdef]; exact Set.indicator_of_notMem (fun hx => absurd hx.1 (not_le.mpr hS)) _
      rw [hUU hS, hI]
      rcases lt_or_ge x (11 / 250) with h0 | h0
      · -- below the origin hub
        have hW : W = 0 := by rw [hWdef]; exact schurLendWeight_of_off (Or.inl h0)
        have hN : 0 ≤ N := by rw [hNdef]; exact lendFoldNumerator_nonneg_origin hκ hx0 h0.le
        rw [hW]; linarith only [hN]
      rcases le_or_gt x (7 / 100) with h1 | h1
      · -- the origin hub pays `(24/25)(9/25)(13/100) h ≤ 173/100000`
        have hW : W = -(9 / 25 * (13 / 100)) := by rw [hWdef]; exact schurLendWeight_of_hubA h0 h1
        have hN : 173 / 100000 ≤ N := by rw [hNdef]; exact lendFoldNumerator_hubA hκ h0 h1
        obtain ⟨-, hg2⟩ := lendFoldGauge_hubA_bounds h0 h1
        rw [← hg] at hg2
        rw [hW]; linarith only [hN, hg2]
      rcases lt_or_ge x (7 / 50) with h2 | h2
      · have hW : W = 0 := by rw [hWdef]; exact schurLendWeight_of_off (Or.inr (Or.inl ⟨h1, h2⟩))
        have hN : 0 ≤ N := by rw [hNdef]; exact lendFoldNumerator_nonneg_lower hκ h1.le h2.le
        rw [hW]; linarith only [hN]
      rcases le_or_gt x (27 / 100) with h3 | h3
      · -- the middle borrows `(24/25)(s_A|H_A| + s_B|H_B|) h ≥ 38/100000`
        have hW : W = 33 / 1000 * (13 / 500) + 89 / 500 * (77 / 2500) := by
          rw [hWdef]; exact schurLendWeight_of_middle h2 h3
        have hN : -38 / 100000 ≤ N := by rw [hNdef]; exact lendFoldNumerator_middle hκ h2 h3
        obtain ⟨hg1, -⟩ := lendFoldGauge_middle_bounds h2 h3
        rw [← hg] at hg1
        rw [hW]; linarith only [hN, hg1]
      · have hW : W = 0 := by
          rw [hWdef]; exact schurLendWeight_of_off (Or.inr (Or.inr ⟨h3, by linarith⟩))
        have hN : 0 ≤ N := by rw [hNdef]; exact lendFoldNumerator_nonneg_upper hκ h3.le hxr
        rw [hW]; linarith only [hN]
    · -- on the strip the prime potential pays the loss and the strip hub
      have hpx : Real.log 2 - 181 / 500 ≤ x := not_lt.mp hS
      have hI : I = 1 := by
        rw [hIdef]
        exact Set.indicator_of_mem (show x ∈ Icc (Real.log 2 - 181 / 500) (181 / 500) from ⟨hpx, hxr⟩) _
      have hg1 : 79 / 2000 ≤ g := by rw [hg]; exact lendFoldGauge_strip_ge (by linarith) hxr
      have hs := hstrip hpx
      have hN : 0 ≤ N := by rw [hNdef]; exact lendFoldNumerator_nonneg_upper hκ (by linarith) hxr
      rw [hI]
      rcases lt_or_ge x (207 / 625) with h4 | h4
      · have hW : W = 0 := by
          rw [hWdef]; exact schurLendWeight_of_off (Or.inr (Or.inr ⟨by linarith, h4⟩))
        rw [hW]; linarith only [hs, hN, hg1]
      · have hW : W = -(13 / 100) := by rw [hWdef]; exact schurLendWeight_of_hubB h4 hxr
        rw [hW]; linarith only [hs, hN, hg1]
  have hVU : 347 / 20000 ≤ V + ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W) := by
    have h1 : g * (347 / 20000) ≤ g * (V + ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W)) := by
      have e : g * (V + ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W)) =
          g * (V - 347 / 20000) + g * ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W) +
            347 / 20000 * g := by ring
      rw [e]
      linarith only [hkey, hU, hcase]
    exact le_of_mul_le_mul_left h1 hh0
  have hW' : V + ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W) ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 181 / 500)) +
        ((1 - 24 / 25) * U + 24 / 25 * U' + 49 / 125 * I + 24 / 25 * W) +
      (archLevyAntideriv (7241 / 20000 - x) + archLevyAntideriv (7241 / 20000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV, hκdef]; linarith only [hΩx, hΩr, hΩa, hΩb]
  linarith only [hVU, hW']
/-! ### Odd-sector positivity on `[−181/500, 181/500]` -/

/-- The sharp micro-fold constant at `r = 181/500` pays `9/5` times the odd part with `θ = 24/25`. -/
theorem lendWindow_microFold_constant :
    (1 + 4 / 5) * (2 * (4902 / 10000)) ≤ 24 / 25 * (19 / 10 -
      ((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2 / (Real.log 2 - 181 / 500) -
      3 * (((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2) ^ 2) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hη0 : 0 ≤ ((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2 := by linarith
  have hη1 : ((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2 ≤ 15427 / 1000000 := by linarith
  have hp : 3311 / 10000 ≤ Real.log 2 - 181 / 500 := by linarith
  have hq : ((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2 / (Real.log 2 - 181 / 500) ≤ 47 / 1000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hsq : 3 * (((181 / 500 : ℝ) - (Real.log 2 - 181 / 500)) / 2) ^ 2 ≤ 72 / 100000 := by nlinarith
  linarith

/-- The pole constant of the plateau of radius `7241/20000`: `R³/6 · cosh²(R/2) ≤ 8174/1000000`. -/
theorem lendWindow_pole_constant :
    (7241 / 20000 : ℝ) ^ 3 / 6 * Real.cosh (7241 / 20000 / 2) ^ 2 ≤ 8174 / 1000000 := by
  have h1 := Real.cosh_le_exp_half_sq (7241 / 20000 / 2 : ℝ)
  have h2 : (7241 / 20000 / 2 : ℝ) ^ 2 / 2 ≤ 164 / 10000 := by norm_num
  have h3 : Real.exp ((7241 / 20000 / 2 : ℝ) ^ 2 / 2) ≤ Real.exp (164 / 10000) := Real.exp_le_exp.mpr h2
  have h4 : Real.exp (164 / 10000) ≤ 101654 / 100000 := by
    have := Real.exp_bound' (show (0 : ℝ) ≤ 164 / 10000 by norm_num)
      (show (164 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this ⊢
    linarith
  have h5 : Real.cosh (7241 / 20000 / 2) ≤ 101654 / 100000 := by linarith
  have h6 := Real.cosh_pos (7241 / 20000 / 2 : ℝ)
  have hc : Real.cosh (7241 / 20000 / 2) ^ 2 ≤ 1033354 / 1000000 := by nlinarith
  have := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ (7241 / 20000) ^ 3 / 6 by norm_num)
  linarith

/-- **Weil positivity of every odd test supported in `[−181/500, 181/500]`.** The sharp micro-fold pays
`9/5` times the odd part of the atom with `96%` of the strip surplus; the even part of the atom gives
the strip the potential `49/125`, which the strip lends, with the origin region, to the middle of the
window through two Schur rectangles: `Ẑ(F) ≥ (1/1000) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 181 / 500 with hrdef
  set R : ℝ := 7241 / 20000 with hRdef
  set δ : ℝ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef, hRdef, hrdef]; norm_num
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hPr : ∀ y, |y| ≤ r → P y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hδdef]; linarith)
  have hPe : ∀ y, P (-y) = P y := fun y => by
    simp only [hPdef, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hFr : ∀ x, F x ≠ 0 → |x| ≤ r := fun x hx => by
    by_contra h
    exact hx (hsupp x (not_le.mp h))
  have hFM : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => hPr x (hFr x hx)
  have hFB : ∀ x, R ≤ |x| → F x = 0 := fun x hx => hsupp x (by
    simp only [hrdef, hRdef] at hx ⊢; linarith)
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hPL : ∀ a b, |P a - P b| ≤ KM * |a - b| := fun a b => hKM b a
  have hR0 : 0 < R := by rw [hRdef]; norm_num
  have hR1 : 2 * R ≤ 1 := by rw [hRdef]; norm_num
  have hR3 : 2 * R < Real.log 3 := by have := log_three_bounds.1; rw [hRdef]; linarith
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  -- the sharp micro-fold pays `9/5` times the odd part with `θ = 24/25`
  have hθ : (1 + 4 / 5) * (2 * (4902 / 10000)) ≤ 24 / 25 * (19 / 10 -
      (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) - 3 * ((r - (Real.log 2 - r)) / 2) ^ 2) := by
    rw [hrdef]; exact lendWindow_microFold_constant
  -- representation with the prime `2`; the micro-fold pays the whole prime term
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_potentialMixPrimeSchur_le_archJump_sub_prime hPd.continuous
    hF.continuous hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (θ := 24 / 25) (t := 4 / 5) hFc
    (by rw [hrdef]; linarith) (by rw [hrdef]; linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hθ
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
    (continuous_quarticGauge _ _ _ _ _) (a₀ := 1 / 500) (by norm_num)
    (fun x hx0 hxr => lendFoldGauge_ge hx0 hxr) (L := 16 / 25)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (lendFoldGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
    (a₁ := 11 / 250) (a₂ := 7 / 100) (b₁ := 7 / 50) (b₂ := 27 / 100) (βA := 9 / 25)
    (sA := 33 / 1000) (c₁ := 7 / 50) (c₂ := 27 / 100) (d₁ := 207 / 625) (d₂ := 181 / 500) (βB := 1)
    (sB := 89 / 500) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [hrdef]; norm_num)
    (by norm_num) (fun x hx y hy => lendFold_pairWeightA_ge hx.1 hx.2 hy.1 hy.2) (by norm_num)
    (by norm_num) (by rw [hrdef]; linarith) (by norm_num) (by norm_num) (by rw [hrdef])
    (by norm_num) (fun x hx y hy => lendFold_pairWeightB_ge hx.1 hx.2 hy.1 hy.2)
  have hZ : fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 := by
    unfold fullZeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous hPL hdec8).neg
  set G : ℝ → ℝ := fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x with hGdef
  have hGi : Integrable G :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  set L : ℝ := Real.log 2 with hLdef
  set Λ₂ : ℝ := vonMangoldtAtom 2 with hΛdef
  set Pr : ℝ → ℝ := fun x => F x ^ 2 * P x * (P (x + L) + P (x - L)) with hPrdef
  have hPri : Integrable Pr :=
    ((((hF.continuous.pow 2).mul hPd.continuous).mul
      ((hPd.continuous.comp (continuous_id.add continuous_const)).add
        (hPd.continuous.comp (continuous_id.sub continuous_const))))).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  set G₁ : ℝ → ℝ := fun x => F x ^ 2 * P x * (-poleFreeWeilOperator P x + profilePrimeSum P x)
    with hG₁def
  have hG₁eq : ∀ x, G₁ x = G x + Λ₂ * Pr x := fun x => by
    simp only [hG₁def, hGdef, hPrdef]
    by_cases h : F x = 0
    · rw [h]; ring
    · have hx : |x| < R := by have := hFr x h; rw [hrdef] at this; rw [hRdef]; linarith
      rw [profilePrimeSum_eq_two hPB hR3 hx]
      ring
  have hG₁i : Integrable G₁ := by
    have : G₁ = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this]; exact hGi.add (hPri.const_mul Λ₂)
  have hG₁e : ∀ x, G₁ (-x) = G₁ x := fun x => by
    simp only [hG₁def, hodd, hPe, poleFreeWeilOperator_neg hPe, profilePrimeSum_neg hPe, neg_sq]
  have hG₁int := integral_eq_two_mul_Ioi_of_even hG₁i hG₁e
  have hGsplit : (∫ x, G x) = (∫ x, G₁ x) - Λ₂ * ∫ x, Pr x := by
    have : (fun x => G₁ x) = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this, integral_add hGi (hPri.const_mul Λ₂), MeasureTheory.integral_const_mul]
    ring
  have hprime : gaugeJumpProfile P F L - ∫ x, Pr x = -2 * ∫ x, F x * F (x + L) :=
    gaugeJumpProfile_sub_primePotential_eq hPd.continuous hF.continuous hFc hFM L
  have hprimeΛ : Λ₂ * gaugeJumpProfile P F L - Λ₂ * ∫ x, Pr x = -2 * (Λ₂ * ∫ x, F x * F (x + L)) := by
    rw [← mul_sub, hprime]; ring
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2e : ∀ x, (fun x => F x ^ 2) (-x) = F x ^ 2 := fun x => by simp only [hodd, neg_sq]
  have hF2int := integral_eq_two_mul_Ioi_of_even hF2 hF2e
  have hHi := integrableOn_sq_mul_antideriv_sub hF.continuous hodd hFB hFL hR1
    (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num)
  -- pointwise potential on the half line
  obtain ⟨hWi, hWint⟩ := integral_sq_mul_lendStripWeight hF2
  rw [← hLdef, ← hrdef] at hWint
  obtain ⟨hSi, hSint⟩ := integral_sq_mul_schurLendWeight hF2
  set c₀ : ℝ := 347 / 20000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * ((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x) + 49 / 125 * (F x ^ 2 * lendStripWeight x) + 24 / 25 * (F x ^ 2 * schurLendWeight x) + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : 347 / 20000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) +
          (((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x) +
            49 / 125 * lendStripWeight x + 24 / 25 * schurLendWeight x) +
          (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
            2 * archConstantReal) := lendFoldWindow_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      rw [hc₀]
      linarith
  have hW49 : IntegrableOn (fun x => 49 / 125 * (F x ^ 2 * lendStripWeight x)) (Ioi 0) :=
    hWi.const_mul (49 / 125)
  have hS24 : IntegrableOn (fun x => 24 / 25 * (F x ^ 2 * schurLendWeight x)) (Ioi 0) :=
    hSi.const_mul (24 / 25)
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x)) (Ioi 0) := hH2.add hIU
  have hH2UW : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x) +
      49 / 125 * (F x ^ 2 * lendStripWeight x)) (Ioi 0) := hH2U.add hW49
  have hH2UWS : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x) +
      49 / 125 * (F x ^ 2 * lendStripWeight x) + 24 / 25 * (F x ^ 2 * schurLendWeight x)) (Ioi 0) :=
    hH2UW.add hS24
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 24 / 25) * surplusPotential (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) r x + 24 / 25 * surplusPotentialOff (quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7)) (L - r) r x) +
      49 / 125 * (F x ^ 2 * lendStripWeight x) + 24 / 25 * (F x ^ 2 * schurLendWeight x) +
      G₁ x) (Ioi 0) := hH2UWS.add hG₁i.integrableOn
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2UWS hG₁i.integrableOn, integral_add hH2UW hS24, integral_add hH2U hW49,
    integral_add hH2 hIU, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 8174 / 500000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 8174 / 1000000 := by
      rw [hRdef]; exact lendWindow_pole_constant
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  rw [hc₀] at hmono
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ, hI0, hWint, hSint]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
