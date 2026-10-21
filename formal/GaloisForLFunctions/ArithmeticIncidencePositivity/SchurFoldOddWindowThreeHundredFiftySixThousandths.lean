import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurFoldWindowNumeratorBounds
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurAbsorbedGroundState

/-!
# Odd-sector Weil positivity on `[−356/1000, 356/1000]`: the strip borrows from its outer edge

Past `353/1000` the inner edge of the prime strip `S = [log 2 − r, r]` cannot pay its share of the
atom from its own potential: the strip pairs that pay the atom through the sharp micro-fold are
missing from its ground-state potential. A Schur step through the ground-state remainder
(`SchurAbsorbedGroundState`) moves potential to it from the outer part of the strip, where the
plateau potential is logarithmically large.

The rectangle is `Z = [337/1000, 343/1000]`, `H = [35/100, 356/1000]`, with `β = 40`. On `Z × H` the
surplus kernel is at least `128/5`, because `|x − y| ≤ 19/1000`, and the ground-state ratio
`q = h(y)/h(x)` is at least `31/40`. So every pair carries `kβq²/(k + βq) ≥ 21/2`
(`schurFold_pairWeight_ge`). The potential gains `(1 − θ) · (21/2) · |H|` on `Z` and pays
`(1 − θ) · 40 · |Z|` on `H`, `θ = 53/100`. In units of `h`, the numerator on `Z` needs
`2/1000 + 13/10000` to cover the strip loss `33/10000`, and on `H` it needs
`85/10000 − 52/10000 ≥ 33/10000` (`schurFoldWindow_potential_ge`).

**Theorem** (`fullZeroForm_ge_of_odd_support_le_threeHundredFiftySixThousandths`). Every odd
`F ∈ C²_c` vanishing outside `[−356/1000, 356/1000]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The Schur rectangle -/

/-- The gauge on the inner edge: `473/10000 ≤ h ≤ 507/10000` on `[337/1000, 343/1000]`. -/
theorem schurFoldGauge_innerEdge_bounds {x : ℝ} (h1 : 337 / 1000 ≤ x) (h2 : x ≤ 343 / 1000) :
    473 / 10000 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x ∧ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x ≤ 507 / 10000 := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  constructor <;> nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 337 / 1000) h1 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 337 / 1000) h1 4,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 4, mul_nonneg hm (by linarith : (0 : ℝ) ≤ x)]

/-- The gauge on the hub: `79/2000 ≤ h ≤ 434/10000` on `[35/100, 356/1000]`. -/
theorem schurFoldGauge_hub_bounds {y : ℝ} (h1 : 35 / 100 ≤ y) (h2 : y ≤ 356 / 1000) :
    79 / 2000 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y ∧ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y ≤ 434 / 10000 := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  constructor <;> nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 35 / 100) h1 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y) h2 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 35 / 100) h1 4,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y) h2 4, mul_nonneg hm (by linarith : (0 : ℝ) ≤ y)]

/-- **The surplus kernel on the rectangle.** For `x ∈ [337/1000, 343/1000]` and
`y ∈ [35/100, 356/1000]`, `k(x, y) ≥ 128/5`: `ω(y − x) ≥ 1/(2(y − x)) + 1/4 − (y − x)/48 − (y − x)²/32`
with `y − x ≤ 19/1000`, and `ω(x + y) ≤ 1/(2(x + y)) + 1/4 − (x + y)/48 − (x + y)²/32 + (x + y)³/250`
with `x + y ≥ 687/1000`. -/
theorem surplusKernel_ge_schurRectangle {x y : ℝ} (hx1 : 337 / 1000 ≤ x) (hx2 : x ≤ 343 / 1000)
    (hy1 : 35 / 100 ≤ y) (hy2 : y ≤ 356 / 1000) : 128 / 5 ≤ surplusKernel x y := by
  have hd0 : 0 < y - x := by linarith
  have hd1 : y - x ≤ 19 / 1000 := by linarith
  have hs0 : 687 / 1000 ≤ x + y := by linarith
  have hs1 : x + y ≤ 699 / 1000 := by linarith
  obtain ⟨a1, -⟩ := archLevyDensity_secondOrder_bounds hd0 (by linarith)
  obtain ⟨-, b2⟩ := archLevyDensity_secondOrder_bounds (show 0 < x + y by linarith) (by linarith)
  have hinv1 : 500 / 19 ≤ 1 / (2 * (y - x)) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hinv2 : 1 / (2 * (x + y)) ≤ 500 / 687 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsq1 : (y - x) ^ 2 ≤ (19 / 1000) ^ 2 := pow_le_pow_left₀ hd0.le hd1 2
  have hsq2 : (687 / 1000) ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (by norm_num) hs0 2
  have hcu : (x + y) ^ 3 ≤ (699 / 1000) ^ 3 := pow_le_pow_left₀ (by linarith) hs1 3
  unfold surplusKernel
  rw [abs_of_neg (by linarith : x - y < 0), neg_sub]
  linarith

/-- **The Schur weight of a pair of the rectangle.** For `x ∈ [337/1000, 343/1000]` and
`y ∈ [35/100, 356/1000]`, `kβq²/(k + βq) ≥ 21/2` with `β = 40`, `q = h(y)/h(x) ≥ 31/40`. -/
theorem schurFold_pairWeight_ge {x y : ℝ} (hx1 : 337 / 1000 ≤ x) (hx2 : x ≤ 343 / 1000)
    (hy1 : 35 / 100 ≤ y) (hy2 : y ≤ 356 / 1000) :
    21 / 2 ≤ surplusKernel x y * 40 * (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y / quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x) ^ 2 /
      (surplusKernel x y + 40 * (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y / quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x)) := by
  have hk := surplusKernel_ge_schurRectangle hx1 hx2 hy1 hy2
  obtain ⟨hx3, hx4⟩ := schurFoldGauge_innerEdge_bounds hx1 hx2
  obtain ⟨hy3, -⟩ := schurFoldGauge_hub_bounds hy1 hy2
  have hq : 31 / 40 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y / quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  set q := quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) y / quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x with hqdef
  set k := surplusKernel x y with hkdef
  clear_value q k
  rw [le_div_iff₀ (by nlinarith)]
  have e1 : 0 ≤ (k - 128 / 5) * (40 * q ^ 2 - 21 / 2) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hq)]

/-- The Schur redistribution of the potential: the gain `(21/2)|H|` on `Z = [337/1000, 343/1000]`
and the cost `40|Z|` on `H = [35/100, 356/1000]`. -/
def schurFoldWeight (x : ℝ) : ℝ :=
  21 / 2 * (6 / 1000) * (Icc (337 / 1000 : ℝ) (343 / 1000)).indicator (fun _ => (1 : ℝ)) x -
    40 * (6 / 1000) * (Icc (35 / 100 : ℝ) (356 / 1000)).indicator (fun _ => (1 : ℝ)) x

/-- The Schur weight integrates to the Schur part of the rectangle. -/
theorem integral_sq_mul_schurFoldWeight {F : ℝ → ℝ} (hF : Integrable fun x => F x ^ 2) :
    IntegrableOn (fun x => F x ^ 2 * schurFoldWeight x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), F x ^ 2 * schurFoldWeight x =
        21 / 2 * (6 / 1000) * (∫ x in Icc (337 / 1000 : ℝ) (343 / 1000), F x ^ 2) -
          40 * (6 / 1000) * ∫ y in Icc (35 / 100 : ℝ) (356 / 1000), F y ^ 2 := by
  have e : (fun x => F x ^ 2 * schurFoldWeight x) = fun x =>
      21 / 2 * (6 / 1000) * (Icc (337 / 1000 : ℝ) (343 / 1000)).indicator (fun x => F x ^ 2) x -
        40 * (6 / 1000) * (Icc (35 / 100 : ℝ) (356 / 1000)).indicator (fun x => F x ^ 2) x := by
    funext x
    unfold schurFoldWeight
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  have hZ := (hF.indicator (measurableSet_Icc (a := (337 / 1000 : ℝ)) (b := 343 / 1000))).const_mul
    (21 / 2 * (6 / 1000))
  have hH := (hF.indicator (measurableSet_Icc (a := (35 / 100 : ℝ)) (b := 356 / 1000))).const_mul
    (40 * (6 / 1000))
  rw [e]
  refine ⟨(hZ.sub hH).integrableOn, ?_⟩
  have i1 : Ioi (0 : ℝ) ∩ Icc (337 / 1000) (343 / 1000) = Icc (337 / 1000) (343 / 1000) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < 337 / 1000 by norm_num).trans_le hx.1
  have i2 : Ioi (0 : ℝ) ∩ Icc (35 / 100) (356 / 1000) = Icc (35 / 100) (356 / 1000) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < 35 / 100 by norm_num).trans_le hx.1
  rw [integral_sub hZ.integrableOn hH.integrableOn, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, setIntegral_indicator measurableSet_Icc,
    setIntegral_indicator measurableSet_Icc, i1, i2]

theorem schurFoldWeight_of_innerEdge {x : ℝ} (h1 : 337 / 1000 ≤ x) (h2 : x ≤ 343 / 1000) :
    schurFoldWeight x = 21 / 2 * (6 / 1000) := by
  unfold schurFoldWeight
  rw [Set.indicator_of_mem (show x ∈ Icc (337 / 1000 : ℝ) (343 / 1000) from ⟨h1, h2⟩),
    Set.indicator_of_notMem (show x ∉ Icc (35 / 100 : ℝ) (356 / 1000) from fun h => by
      linarith [h.1])]
  ring

theorem schurFoldWeight_of_middle {x : ℝ} (h1 : 343 / 1000 < x) (h2 : x < 35 / 100) :
    schurFoldWeight x = 0 := by
  unfold schurFoldWeight
  rw [Set.indicator_of_notMem (show x ∉ Icc (337 / 1000 : ℝ) (343 / 1000) from fun h => by
      linarith [h.2]),
    Set.indicator_of_notMem (show x ∉ Icc (35 / 100 : ℝ) (356 / 1000) from fun h => by
      linarith [h.1])]
  ring

theorem schurFoldWeight_of_hub {x : ℝ} (h1 : 35 / 100 ≤ x) (h2 : x ≤ 356 / 1000) :
    schurFoldWeight x = -(40 * (6 / 1000)) := by
  unfold schurFoldWeight
  rw [Set.indicator_of_notMem (show x ∉ Icc (337 / 1000 : ℝ) (343 / 1000) from fun h => by
      linarith [h.2]),
    Set.indicator_of_mem (show x ∈ Icc (35 / 100 : ℝ) (356 / 1000) from ⟨h1, h2⟩)]
  ring

theorem schurFoldWeight_nonneg_of_lt {x : ℝ} (h : x < 35 / 100) : 0 ≤ schurFoldWeight x := by
  unfold schurFoldWeight
  rw [Set.indicator_of_notMem (show x ∉ Icc (35 / 100 : ℝ) (356 / 1000) from fun h' => by
      linarith [h'.1])]
  have : 0 ≤ (Icc (337 / 1000 : ℝ) (343 / 1000)).indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  linarith

/-! ### The potential with the Schur step -/

/-- **The potential on `(0, 356/1000]`.** The killing, the mixed surplus potential
`(1 − θ)(U_h + W) + θ U_h^{off}`, `θ = 53/100`, `W` the Schur redistribution, and the plateau
potential of radius `7121/20000`, with the second-order expansions of the surplus kernel and of `Ω`,
exceed `331/20000`. -/
theorem schurFoldWindow_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 356 / 1000) :
    331 / 20000 ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 356 / 1000)) +
        (((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (356 / 1000) x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (Real.log 2 - 356 / 1000) (356 / 1000) x) + (1 - 53 / 100) * schurFoldWeight x) +
        (archLevyAntideriv (7121 / 20000 - x) + archLevyAntideriv (7121 / 20000 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := schurFoldGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge_second (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)
    hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr => schurFoldGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge_second hx0 (by linarith)
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 356 / 1000 by linarith)
  have hΩa := archLevyAntideriv_ge_second (show 0 < 7121 / 20000 - x by linarith) (by linarith)
  have hΩb := archLevyAntideriv_ge_second (show 0 < 7121 / 20000 + x by linarith) (by linarith)
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
  have e2 : Real.log ((x + 356 / 1000) / 4) = Real.log (x + 356 / 1000) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((7121 / 20000 - x) / 4) = Real.log (7121 / 20000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((7121 / 20000 + x) / 4) = Real.log (7121 / 20000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 356 / 1000) - Real.log x) +
    (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x)) - κ - 1 / 40000 -
    (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 +
      (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (356 / 1000) x with hUdef
  set U' := surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (Real.log 2 - 356 / 1000) (356 / 1000) x with hU'def
  have hkey : quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x * (V - 331 / 20000) +
      (quarticSurplusMain (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x +
        firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x -
        16 / 25 * (4 / 125 * (356 / 1000) ^ 5)) = schurFoldNumerator κ x := by
    rw [hV]; unfold schurFoldNumerator quarticSurplusMain cubicSurplusMain schurFoldPoly quarticGauge
    ring
  -- below the strip the off-strip potential is `U`; on the strip it loses at most `33/10000`
  have hUU : x < Real.log 2 - 356 / 1000 → U' = U := fun hS => by
    rw [hU'def, hUdef]; unfold surplusPotentialOff; rw [if_pos hS]
  have hstrip : Real.log 2 - 356 / 1000 ≤ x →
      quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x * U ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x * ((1 - 53 / 100) * U + 53 / 100 * U') + 33 / 10000 := fun hpx => by
    have hloss := mul_surplusPotential_le_off_add (h := quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (a₀ := 1 / 500) (L := 16 / 25)
      (by linarith) hpx hxr (by norm_num) (continuous_quarticGauge _ _ _ _ _) (by norm_num) hh
      (by norm_num) (fun y hy0 hyr => by
        rw [quarticGauge_sub, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (schurFoldGauge_divDiff_le hx0.le hxr hy0.le hyr)
          (abs_nonneg _))
    have hd0 : 0 ≤ 356 / 1000 - (Real.log 2 - 356 / 1000) := by linarith
    have hd1 : 356 / 1000 - (Real.log 2 - 356 / 1000) ≤ 18853 / 1000000 := by linarith
    have hd : 53 / 100 * (16 / 25 * (356 / 1000 - (Real.log 2 - 356 / 1000)) *
        (1 / 2 + (356 / 1000 - (Real.log 2 - 356 / 1000)) / 4)) ≤ 33 / 10000 := by
      have hm := mul_le_mul hd1 (show 1 / 2 + (356 / 1000 - (Real.log 2 - 356 / 1000)) / 4 ≤
        1 / 2 + 18853 / 1000000 / 4 by linarith) (by linarith) (by norm_num)
      linarith only [hm]
    rw [hU'def, hUdef]
    linarith only [hloss, hd]
  clear_value V U U'
  set g := quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x with hg
  set N := schurFoldNumerator κ x with hNdef
  set W := schurFoldWeight x with hWdef
  clear_value g N W
  -- the four regions: below the strip, the inner edge, the middle of the strip, the hub
  have hcase : g * U ≤ g * ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W) + N := by
    by_cases hS : x < Real.log 2 - 356 / 1000
    · -- below the strip: `U' = U`, `W ≥ 0`
      have hW0 : 0 ≤ W := by rw [hWdef]; exact schurFoldWeight_nonneg_of_lt (by linarith)
      have hN : 0 ≤ N := by
        rw [hNdef]
        rcases le_or_gt x (337 / 1000) with h | h
        · exact schurFoldNumerator_nonneg_inner hκ hx0 h
        · linarith [schurFoldNumerator_innerEdge hκ h.le (by linarith)]
      rw [hUU hS]
      linarith only [mul_nonneg hh0.le hW0, hN]
    have hpx : Real.log 2 - 356 / 1000 ≤ x := not_lt.mp hS
    have hs := hstrip hpx
    rcases le_or_gt x (343 / 1000) with hz | hz
    · -- the inner edge gains `(1 − θ)(21/2)|H| h ≥ 13/10000`
      have hW : W = 21 / 2 * (6 / 1000) := by
        rw [hWdef]; exact schurFoldWeight_of_innerEdge (by linarith) hz
      obtain ⟨hg1, -⟩ := schurFoldGauge_innerEdge_bounds (by linarith) hz
      rw [← hg] at hg1
      have hN : 2 / 1000 ≤ N := by rw [hNdef]; exact schurFoldNumerator_innerEdge hκ (by linarith) hz
      rw [hW]
      linarith only [hs, hN, hg1]
    rcases lt_or_ge x (35 / 100) with hm | hm
    · -- the middle of the strip
      have hW : W = 0 := by rw [hWdef]; exact schurFoldWeight_of_middle hz hm
      have hN : 33 / 10000 ≤ N := by rw [hNdef]; exact schurFoldNumerator_strip hκ hz.le hm.le
      rw [hW]
      linarith only [hs, hN]
    · -- the hub pays `(1 − θ) 40 |Z| h ≤ 52/10000`
      have hW : W = -(40 * (6 / 1000)) := by rw [hWdef]; exact schurFoldWeight_of_hub hm hxr
      obtain ⟨-, hg2⟩ := schurFoldGauge_hub_bounds hm hxr
      rw [← hg] at hg2
      have hN : 85 / 10000 ≤ N := by rw [hNdef]; exact schurFoldNumerator_hub hκ hm hxr
      rw [hW]
      linarith only [hs, hN, hg2]
  have hVU : 331 / 20000 ≤ V + ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W) := by
    have h1 : g * (331 / 20000) ≤
        g * (V + ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W)) := by
      have e : g * (V + ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W)) =
          g * (V - 331 / 20000) +
            g * ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W) +
            331 / 20000 * g := by ring
      rw [e]
      linarith only [hkey, hU, hcase]
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W) ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 356 / 1000)) +
        ((1 - 53 / 100) * U + 53 / 100 * U' + (1 - 53 / 100) * W) +
      (archLevyAntideriv (7121 / 20000 - x) + archLevyAntideriv (7121 / 20000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV, hκdef]; linarith only [hΩx, hΩr, hΩa, hΩb]
  linarith only [hVU, hW]
/-! ### Odd-sector positivity on `[−356/1000, 356/1000]` -/

/-- **Weil positivity of every odd test supported in `[−356/1000, 356/1000]`.** The sharp
micro-fold pays the atom with `53%` of the strip surplus; the rest stays in the ground-state
potential, where a Schur step moves potential from the outer part of the strip to its inner edge:
`Ẑ(F) ≥ (1/1000) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_threeHundredFiftySixThousandths {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 356 / 1000 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 356 / 1000 with hrdef
  set R : ℝ := 7121 / 20000 with hRdef
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
  -- the sharp micro-fold constant beats the atom with `θ = 53/100`
  have hθ : 2 * (4902 / 10000) ≤ 53 / 100 * (19 / 10 - (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) -
      3 * ((r - (Real.log 2 - r)) / 2) ^ 2) := by
    have hη0 : 0 ≤ (r - (Real.log 2 - r)) / 2 := by rw [hrdef]; linarith
    have hη1 : (r - (Real.log 2 - r)) / 2 ≤ 9427 / 1000000 := by rw [hrdef]; linarith
    have hp : 3371 / 10000 ≤ Real.log 2 - r := by rw [hrdef]; linarith
    have hq : (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) ≤ 28 / 1000 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hsq : 3 * ((r - (Real.log 2 - r)) / 2) ^ 2 ≤ 27 / 100000 := by nlinarith
    linarith
  -- representation with the prime `2`; the micro-fold pays the whole prime term
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_potentialMixSchur_le_archJump_sub_prime hPd.continuous
    hF.continuous hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (θ := 53 / 100) hFc
    (by rw [hrdef]; linarith) (by rw [hrdef]; linarith) (by norm_num) (by norm_num) hθ
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
    (continuous_quarticGauge _ _ _ _ _) (a₀ := 1 / 500) (by norm_num)
    (fun x hx0 hxr => schurFoldGauge_ge hx0 hxr) (L := 16 / 25)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (schurFoldGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
    (z₁ := 337 / 1000) (z₂ := 343 / 1000) (y₁ := 35 / 100) (y₂ := 356 / 1000) (β := 40)
    (s₀ := 21 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [hrdef])
    (by norm_num) (fun x hx y hy => schurFold_pairWeight_ge hx.1 hx.2 hy.1 hy.2)
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
  obtain ⟨hWi, hWint⟩ := integral_sq_mul_schurFoldWeight hF2
  set c₀ : ℝ := 331 / 20000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (L - r) r x) + (1 - 53 / 100) * (F x ^ 2 * schurFoldWeight x) + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : 331 / 20000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) +
          (((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (L - r) r x) +
            (1 - 53 / 100) * schurFoldWeight x) +
          (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
            2 * archConstantReal) := schurFoldWindow_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      rw [hc₀]
      linarith
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (L - r) r x) + (1 - 53 / 100) * (F x ^ 2 * schurFoldWeight x) +
      G₁ x) (Ioi 0) :=
    (((hHi.const_mul 2).add hIU).add (hWi.const_mul (1 - 53 / 100))).add hG₁i.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (L - r) r x)) (Ioi 0) := hH2.add hIU
  have hH2UW : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20)) (L - r) r x) + (1 - 53 / 100) * (F x ^ 2 * schurFoldWeight x))
      (Ioi 0) := hH2U.add (hWi.const_mul (1 - 53 / 100))
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2UW hG₁i.integrableOn, integral_add hH2U (hWi.const_mul (1 - 53 / 100)),
    integral_add hH2 hIU, integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 1032317 / 1000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 159 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (159 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (159 / 10000) ≤ 101603 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 159 / 10000 by norm_num)
        (show (159 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101603 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 7767 / 500000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 7767 / 1000000 := by
      have : R ^ 3 / 6 = (7121 / 20000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      have := mul_le_mul_of_nonneg_left hcosh (show (0 : ℝ) ≤ (7121 / 20000) ^ 3 / 6 by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  rw [hc₀] at hmono
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ, hI0, hWint]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
