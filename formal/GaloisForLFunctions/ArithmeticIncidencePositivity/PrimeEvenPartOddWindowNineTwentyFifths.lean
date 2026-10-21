import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomEvenPartPotential
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeEvenPartWindowNumeratorBounds

/-!
# Odd-sector Weil positivity on `[−9/25, 9/25]`: the prime atom pays the strip

On the strip `S = [log 2 − r, r]` of the first prime window the atom `Λ(2)/√2` is a cost only through
the odd part of `F` about `log 2 / 2`; its even part is a gain (`PrimeAtomEvenPartPotential`). With
`t = 1/2` the sharp micro-fold pays `3/2` times the odd part with the fraction `θ = 4/5` of the strip
surplus (`λ ≥ 1.858` at `r = 9/25`). The strip then carries the prime potential `(49/100)(1/2)`, which
in units of the gauge is `(49/200) h ≥ 0.0096`. This exceeds the strip loss
`θ L |S| (½ + |S|/4) ≤ 7/1000` of the mixed ground-state potential, so the numerator only has to be
nonnegative on the whole window (`primeEvenFoldWindow_potential_ge`). The inner-edge wall of the
windows `353/1000` and `356/1000` is gone. What remains is the archimedean middle of the window,
where the gauge of the window `356/1000`, dilated by `90/89`, still has slack.

**Theorem** (`fullZeroForm_ge_of_odd_support_le_nineTwentyFifths`). Every odd `F ∈ C²_c` vanishing
outside `[−9/25, 9/25]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The strip weight -/

/-- The indicator of the strip `[log 2 − 9/25, 9/25]`. -/
def primeStripWeight (x : ℝ) : ℝ :=
  (Icc (Real.log 2 - 9 / 25) (9 / 25)).indicator (fun _ => (1 : ℝ)) x

theorem primeStripWeight_of_lt {x : ℝ} (h : x < Real.log 2 - 9 / 25) : primeStripWeight x = 0 :=
  Set.indicator_of_notMem (fun hx => absurd hx.1 (not_le.mpr h)) _

theorem primeStripWeight_of_mem {x : ℝ} (h1 : Real.log 2 - 9 / 25 ≤ x) (h2 : x ≤ 9 / 25) :
    primeStripWeight x = 1 :=
  Set.indicator_of_mem (show x ∈ Icc (Real.log 2 - 9 / 25) (9 / 25) from ⟨h1, h2⟩) _

/-- The strip weight integrates to the strip mass. -/
theorem integral_sq_mul_primeStripWeight {F : ℝ → ℝ} (hF : Integrable fun x => F x ^ 2) :
    IntegrableOn (fun x => F x ^ 2 * primeStripWeight x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), F x ^ 2 * primeStripWeight x =
        ∫ x in (Real.log 2 - 9 / 25)..(9 / 25), F x ^ 2 := by
  have e : (fun x => F x ^ 2 * primeStripWeight x) =
      (Icc (Real.log 2 - 9 / 25) (9 / 25)).indicator (fun x => F x ^ 2) := by
    funext x
    unfold primeStripWeight
    simp only [Set.indicator_apply]
    split_ifs <;> ring
  have hi := hF.indicator (measurableSet_Icc (a := Real.log 2 - 9 / 25) (b := (9 / 25 : ℝ)))
  rw [e]
  refine ⟨hi.integrableOn, ?_⟩
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have i1 : Ioi (0 : ℝ) ∩ Icc (Real.log 2 - 9 / 25) (9 / 25) = Icc (Real.log 2 - 9 / 25) (9 / 25) :=
    Set.inter_eq_right.mpr fun x hx => (show (0 : ℝ) < Real.log 2 - 9 / 25 by linarith).trans_le hx.1
  rw [setIntegral_indicator measurableSet_Icc, i1, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

/-- The gauge on the strip: `h ≥ 79/2000` on `[3331/10000, 9/25]`. -/
theorem primeEvenFoldGauge_strip_ge {x : ℝ} (h1 : 3331 / 10000 ≤ x) (h2 : x ≤ 9 / 25) :
    79 / 2000 ≤ quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x := by
  unfold quarticGauge
  have hm := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
  nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 3331 / 10000) h1 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 3,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 3331 / 10000) h1 4,
    pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) h2 4, mul_nonneg hm (by linarith : (0 : ℝ) ≤ x)]

/-! ### The potential -/

/-- **The potential on `(0, 9/25]`.** The killing, the mixed surplus potential
`(1 − θ) U_h + θ U_h^{off}`, `θ = 4/5`, the prime potential `(49/200) 1_S`, and the plateau potential of
radius `7201/20000`, with the second-order expansions of the surplus kernel and of `Ω`, exceed
`171/10000`. -/
theorem primeEvenFoldWindow_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 9 / 25) :
    171 / 10000 ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 9 / 25)) +
        (((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (9 / 25) x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (Real.log 2 - 9 / 25) (9 / 25) x) + 49 / 200 * primeStripWeight x) +
        (archLevyAntideriv (7201 / 20000 - x) + archLevyAntideriv (7201 / 20000 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := primeEvenFoldGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge_second (1 / 500) (89 / 150) (-44 / 45) (-17 / 80)
    (-82 / 35) hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr =>
      primeEvenFoldGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge_second hx0 (by linarith)
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 9 / 25 by linarith)
  have hΩa := archLevyAntideriv_ge_second (show 0 < 7201 / 20000 - x by linarith) (by linarith)
  have hΩb := archLevyAntideriv_ge_second (show 0 < 7201 / 20000 + x by linarith) (by linarith)
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
  have e2 : Real.log ((x + 9 / 25) / 4) = Real.log (x + 9 / 25) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((7201 / 20000 - x) / 4) = Real.log (7201 / 20000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((7201 / 20000 + x) / 4) = Real.log (7201 / 20000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 9 / 25) - Real.log x) +
    (-(1 / 2) * Real.log (7201 / 20000 - x) - 1 / 2 * Real.log (7201 / 20000 + x)) - κ - 1 / 40000 -
    (x + 9 / 25) ^ 2 / 48 - 5 * (x + 9 / 25) ^ 3 / 192 +
      (2 * x ^ 2 + (7201 / 20000) ^ 2) / 48 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (9 / 25) x with hUdef
  set U' := surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (Real.log 2 - 9 / 25) (9 / 25) x with hU'def
  have hkey : quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x * (V - 171 / 10000) +
      (quarticSurplusMain (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) (9 / 25) x +
        firstOrderSurplus (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) (9 / 25) x -
        16 / 25 * (4 / 125 * (9 / 25) ^ 5)) = primeEvenFoldNumerator κ x := by
    rw [hV]; unfold primeEvenFoldNumerator quarticSurplusMain cubicSurplusMain primeEvenFoldPoly quarticGauge
    ring
  -- below the strip the off-strip potential is `U`; on the strip it loses at most `7/1000`
  have hUU : x < Real.log 2 - 9 / 25 → U' = U := fun hS => by
    rw [hU'def, hUdef]; unfold surplusPotentialOff; rw [if_pos hS]
  have hstrip : Real.log 2 - 9 / 25 ≤ x →
      quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x * U ≤ quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x * ((1 - 4 / 5) * U + 4 / 5 * U') + 7 / 1000 := fun hpx => by
    have hloss := mul_surplusPotential_le_off_add (h := quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (a₀ := 1 / 500) (L := 16 / 25)
      (by linarith) hpx hxr (by norm_num) (continuous_quarticGauge _ _ _ _ _) (by norm_num) hh
      (by norm_num) (fun y hy0 hyr => by
        rw [quarticGauge_sub, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (primeEvenFoldGauge_divDiff_le hx0.le hxr hy0.le hyr)
          (abs_nonneg _))
    have hd0 : 0 ≤ 9 / 25 - (Real.log 2 - 9 / 25) := by linarith
    have hd1 : 9 / 25 - (Real.log 2 - 9 / 25) ≤ 26853 / 1000000 := by linarith
    have hd : 4 / 5 * (16 / 25 * (9 / 25 - (Real.log 2 - 9 / 25)) *
        (1 / 2 + (9 / 25 - (Real.log 2 - 9 / 25)) / 4)) ≤ 7 / 1000 := by
      have hm := mul_le_mul hd1 (show 1 / 2 + (9 / 25 - (Real.log 2 - 9 / 25)) / 4 ≤
        1 / 2 + 26853 / 1000000 / 4 by linarith) (by linarith) (by norm_num)
      linarith only [hm]
    rw [hU'def, hUdef]
    linarith only [hloss, hd]
  clear_value V U U'
  set g := quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35) x with hg
  set N := primeEvenFoldNumerator κ x with hNdef
  set I := primeStripWeight x with hIdef
  clear_value g N I
  have hN : 0 ≤ N := by rw [hNdef]; exact primeEvenFoldNumerator_nonneg hκ hx0 hxr
  -- below the strip nothing changes; on the strip the prime potential pays the loss
  have hcase : g * U ≤ g * ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I) + N := by
    by_cases hS : x < Real.log 2 - 9 / 25
    · have hI : I = 0 := by rw [hIdef]; exact primeStripWeight_of_lt hS
      rw [hUU hS, hI]
      linarith only [hN]
    · have hpx : Real.log 2 - 9 / 25 ≤ x := not_lt.mp hS
      have hI : I = 1 := by rw [hIdef]; exact primeStripWeight_of_mem hpx hxr
      have hg1 : 79 / 2000 ≤ g := by rw [hg]; exact primeEvenFoldGauge_strip_ge (by linarith) hxr
      have hs := hstrip hpx
      rw [hI]
      linarith only [hs, hN, hg1]
  have hVU : 171 / 10000 ≤ V + ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I) := by
    have h1 : g * (171 / 10000) ≤ g * (V + ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I)) := by
      have e : g * (V + ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I)) =
          g * (V - 171 / 10000) + g * ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I) +
            171 / 10000 * g := by ring
      rw [e]
      linarith only [hkey, hU, hcase]
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I) ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 9 / 25)) +
        ((1 - 4 / 5) * U + 4 / 5 * U' + 49 / 200 * I) +
      (archLevyAntideriv (7201 / 20000 - x) + archLevyAntideriv (7201 / 20000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV, hκdef]; linarith only [hΩx, hΩr, hΩa, hΩb]
  linarith only [hVU, hW]
/-! ### Odd-sector positivity on `[−9/25, 9/25]` -/

/-- **Weil positivity of every odd test supported in `[−9/25, 9/25]`.** The sharp micro-fold pays
`3/2` times the odd part of the atom with `80%` of the strip surplus; the even part of the atom gives
the strip the potential `49/200`: `Ẑ(F) ≥ (1/1000) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_nineTwentyFifths {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 9 / 25 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 9 / 25 with hrdef
  set R : ℝ := 7201 / 20000 with hRdef
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
  -- the sharp micro-fold pays `3/2` times the odd part with `θ = 4/5`
  have hθ : (1 + 1 / 2) * (2 * (4902 / 10000)) ≤ 4 / 5 * (19 / 10 -
      (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) - 3 * ((r - (Real.log 2 - r)) / 2) ^ 2) := by
    have hη0 : 0 ≤ (r - (Real.log 2 - r)) / 2 := by rw [hrdef]; linarith
    have hη1 : (r - (Real.log 2 - r)) / 2 ≤ 13427 / 1000000 := by rw [hrdef]; linarith
    have hp : 3331 / 10000 ≤ Real.log 2 - r := by rw [hrdef]; linarith
    have hq : (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) ≤ 41 / 1000 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hsq : 3 * ((r - (Real.log 2 - r)) / 2) ^ 2 ≤ 55 / 100000 := by nlinarith
    linarith
  -- representation with the prime `2`; the micro-fold pays the whole prime term
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_potentialMixPrime_le_archJump_sub_prime hPd.continuous
    hF.continuous hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (θ := 4 / 5) (t := 1 / 2) hFc
    (by rw [hrdef]; linarith) (by rw [hrdef]; linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hθ
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
    (continuous_quarticGauge _ _ _ _ _) (a₀ := 1 / 500) (by norm_num)
    (fun x hx0 hxr => primeEvenFoldGauge_ge hx0 hxr) (L := 16 / 25)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (primeEvenFoldGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
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
  obtain ⟨hWi, hWint⟩ := integral_sq_mul_primeStripWeight hF2
  rw [← hLdef, ← hrdef] at hWint
  set c₀ : ℝ := 171 / 10000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * ((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) r x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (L - r) r x) + 49 / 200 * (F x ^ 2 * primeStripWeight x) + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : 171 / 10000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) +
          (((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) r x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (L - r) r x) +
            49 / 200 * primeStripWeight x) +
          (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
            2 * archConstantReal) := primeEvenFoldWindow_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      rw [hc₀]
      linarith
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) r x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (L - r) r x) + 49 / 200 * (F x ^ 2 * primeStripWeight x) +
      G₁ x) (Ioi 0) :=
    (((hHi.const_mul 2).add hIU).add (hWi.const_mul (49 / 200))).add hG₁i.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) r x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (L - r) r x)) (Ioi 0) := hH2.add hIU
  have hH2UW : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 4 / 5) * surplusPotential (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) r x + 4 / 5 * surplusPotentialOff (quarticGauge (1 / 500) (89 / 150) (-44 / 45) (-17 / 80) (-82 / 35)) (L - r) r x) + 49 / 200 * (F x ^ 2 * primeStripWeight x))
      (Ioi 0) := hH2U.add (hWi.const_mul (49 / 200))
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2UW hG₁i.integrableOn, integral_add hH2U (hWi.const_mul (49 / 200)),
    integral_add hH2 hIU, integral_const_mul, integral_const_mul, integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 1033151 / 1000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 163 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (163 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (163 / 10000) ≤ 101644 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 163 / 10000 by norm_num)
        (show (163 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101644 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 8038 / 500000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 8038 / 1000000 := by
      have : R ^ 3 / 6 = (7201 / 20000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      have := mul_le_mul_of_nonneg_left hcosh (show (0 : ℝ) ≤ (7201 / 20000) ^ 3 / 6 by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  rw [hc₀] at hmono
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ, hI0, hWint]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
