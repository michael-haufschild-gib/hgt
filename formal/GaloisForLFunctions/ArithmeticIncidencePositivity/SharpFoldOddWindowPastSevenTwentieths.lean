import GaloisForLFunctions.ArithmeticIncidencePositivity.AtomFreeOddWindowSevenTwentieths
import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpMicroFoldHarnack
import GaloisForLFunctions.ArithmeticIncidencePositivity.SecondOrderSurplusPotential

/-!
# Odd-sector Weil positivity on `[−353/1000, 353/1000]`: the sharp micro-fold shares the strip

Past `7/20` the binding constraint of the first prime window is the inner edge `p = log 2 − r` of
the strip `S = [p, r]`: the pairs of `S × S` that pay the atom are missing from the ground-state
potential there. The sharp micro-fold (`SharpMicroFoldHarnack`) needs only the fraction
`θ = 2Λ(2)/√2 / λ ≈ 0.53` of the strip surplus, `λ = 1.9 − η/p − 3η² ≈ 1.88`. The convex combination
of the full ground-state transform and the transform with the strip pairs kept exact
(`fourKilling_add_potentialMix_le_archJump_sub_prime`) leaves the potential
`(1 − θ) U_h + θ U_h^{off}`, whose loss on `S` is `θ L |S| (½ + |S|/4) ≤ 0.0023` per unit of gauge.

Two second-order sharpenings pay the rest (`SecondOrderSurplusPotential`): the surplus kernel to second
order, `k = k₀ + min(x, y)/24 + xy/8 + O((x + y)³)`, replaces the remainder `L·O(r³)` of the
first-order bound by `L (4/125) r⁵`; and `Ω(y) ≥ −½ log(y/4) + π/4 − y/4 + y²/96` adds
`(2x² + R²)/48` to the potential. The plateau collar is `R − r = 1/20000`.

With the gauge `1/500 + (3/5)y − y² − (3/10)y³ − (49/20)y⁴` the numerator is nonnegative on
`(0, 353/1000]` and exceeds `0.0023` on `[0.3401, 0.353] ⊇ S` (`sharpFoldNumerator_nonneg`,
`sharpFoldNumerator_strip`).

**Theorem** (`fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths`). Every odd
`F ∈ C²_c` vanishing outside `[−353/1000, 353/1000]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The prime window with the strip shared -/

section Mix

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The first prime window with the strip shared.** If the fraction `θ` of the strip surplus pays
the atom through the sharp micro-fold, `2Λ(2)/√2 ≤ θ λ`, the archimedean jump energy minus the prime
term dominates the killing plus the mixed ground-state potential `(1 − θ) U_h + θ U_h^{off}`. -/
theorem fourKilling_add_potentialMix_le_archJump_sub_prime {h : ℝ → ℝ} {r a₀ L θ : ℝ}
    (hFcs : HasCompactSupport F) (hr : Real.log 2 / 2 < r) (hr' : r ≤ Real.log 2 / 2 + 1 / 12)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθ : 2 * (4902 / 10000) ≤ θ * (19 / 10 - (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) -
      3 * ((r - (Real.log 2 - r)) / 2) ^ 2))
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hPcs : HasCompactSupport P) (hh : Continuous h) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
        θ * surplusPotentialOff h (Real.log 2 - r) r x)) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
            θ * surplusPotentialOff h (Real.log 2 - r) r x)) ≤
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
          2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hr0 : 0 < r := by linarith
  obtain ⟨hIA, hA⟩ := surplusEnergy_ge_potential hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL
  obtain ⟨hIB, hBs⟩ := surplusEnergy_ge_potentialOff_add_strip hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1
    (p := Real.log 2 - r) (by linarith) (by linarith) hrB hPr hFr hh ha₀ hhpos hhL
  have hfold := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0
    hB1 hr0 hrB hPr hFr hPcs
  have hsupp : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  -- the sharp micro-fold pays the atom with the fraction `θ` of the strip
  set p := Real.log 2 - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = Real.log 2 := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hms := sharpMicroFold_strip_ge hFc hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hFc hFL hp0 hpr.le (by linarith)
  have hshift := integral_mul_shift_le_reflectedOdd hFc hFcs hFo (r := r) (L := Real.log 2)
    (by linarith) (by rw [← hpdef]; exact hpr.le) hsupp
  rw [← hpdef] at hshift
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hdom : 2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) ≤ θ * (2 * stripSurplus F p r) := by
    have k1 := mul_le_mul_of_nonneg_left hshift hΛ0
    have k2 := mul_le_mul_of_nonneg_right hθ hα0
    have k3 := mul_le_mul_of_nonneg_right hΛ1 hα0
    have k4 := mul_le_mul_of_nonneg_left hms hθ0
    rw [hT] at k4
    nlinarith
  -- the mixed potential
  have h1 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x)) (Ioi 0) :=
    hIA.const_mul (1 - θ)
  have h2 : IntegrableOn (fun x => θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) :=
    hIB.const_mul θ
  have h3 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x) +
      θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) := h1.add h2
  have hmix : IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) (Ioi 0) :=
    h3.congr_fun (fun x _ => by ring) measurableSet_Ioi
  refine ⟨hmix, ?_⟩
  have hsplit : (∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) =
      (1 - θ) * (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) +
        θ * ∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
  rw [hsplit]
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have k5 := mul_le_mul_of_nonneg_left hA hθ1'
  have k6 := mul_le_mul_of_nonneg_left hBs hθ0
  nlinarith

end Mix

/-! ### The gauge and the numerator -/

theorem sharpFoldGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 353 / 1000) :
    1 / 500 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by
  unfold quarticGauge
  have h : 0 ≤ 3 / 5 - x - 3 / 10 * x ^ 2 - 49 / 20 * x ^ 3 := by
    nlinarith [pow_le_pow_left₀ hx0 hxr 3]
  nlinarith [mul_nonneg hx0 h]

theorem sharpFoldGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 353 / 1000) (hv0 : 0 ≤ v)
    (hvr : v ≤ 353 / 1000) :
    |3 / 5 + -1 * (u + v) + -3 / 10 * (u ^ 2 + u * v + v ^ 2) +
      -49 / 20 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ 13 / 20 := by
  have h1 := mul_nonneg hu0 hv0
  have h2 : u ^ 3 ≤ (353 / 1000) ^ 3 := pow_le_pow_left₀ hu0 hur 3
  have h3 : v ^ 3 ≤ (353 / 1000) ^ 3 := pow_le_pow_left₀ hv0 hvr 3
  have h4 : u ^ 2 * v ≤ (353 / 1000) ^ 3 := by
    nlinarith [mul_le_mul (pow_le_pow_left₀ hu0 hur 2) hvr hv0 (by positivity)]
  have h5 : u * v ^ 2 ≤ (353 / 1000) ^ 3 := by
    nlinarith [mul_le_mul hur (pow_le_pow_left₀ hv0 hvr 2) (by positivity) (by norm_num)]
  have h6 : 0 ≤ u ^ 2 * v := by positivity
  have h7 : 0 ≤ u * v ^ 2 := by positivity
  have h8 : 0 ≤ u ^ 3 := by positivity
  have h9 : 0 ≤ v ^ 3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- The polynomial part of the principal surplus of the gauge on `[0, 353/1000]`. -/
def sharpFoldPoly (x : ℝ) : ℝ :=
  3 / 5 * x + -1 * (3 / 2 * x ^ 2 - 353 / 1000 * x) +
    -3 / 10 * (11 / 6 * x ^ 3 - (353 / 1000) ^ 2 * x / 2) +
    -49 / 20 * (25 / 12 * x ^ 4 - 353 / 1000 * x ^ 3 - (353 / 1000) ^ 3 * x / 3)

/-- The numerator of the potential on `[−353/1000, 353/1000]` (`κ` stands for `log 2 + γ + log π`). -/
def sharpFoldNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 353 / 1000) - Real.log x) +
    quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
      (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) - κ - 1 / 40000 -
        (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) +
    sharpFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5)

/-- **Tangent form of the numerator** on `[p, q] ⊆ [7/100, 353/1000]`. -/
theorem sharpFoldNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 353 / 1000) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
        353 / 1000 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
          (-(1 / 2) * (La + (7061 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7061 / 20000 + x) / b - 1) -
            241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
            5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) +
        sharpFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5) ≤
      sharpFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 353 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 353 / 1000) - Real.log x ≤ Lv + (1 + 353 / 1000 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 353 / 1000) / x = 1 + 353 / 1000 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 353 / 1000 / x by positivity) hv
    linarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 353 / 1000 / x) / v - 1) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 353 / 1000) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
      353 / 1000 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 353 / 1000 / x) / v - 1) := by
    have e : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 353 / 1000 / x) / v - 1) =
        (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
          353 / 1000 / v * (1 / (500 * x) - x - 49 / 20 * x ^ 3) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 353 / 1000 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (7061 / 20000 - x) / a - 1) ≤ -(1 / 2) * Real.log (7061 / 20000 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 7061 / 20000 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (7061 / 20000 + x) / b - 1) ≤ -(1 / 2) * Real.log (7061 / 20000 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 7061 / 20000 + x by linarith) hb
    linarith
  have hp2 : (x + 353 / 1000) ^ 2 ≤ (q + 353 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 353 / 1000) ^ 3 ≤ (q + 353 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := sharpFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * (La + (7061 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7061 / 20000 + x) / b - 1) -
          241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
          5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) - κ - 1 / 40000 -
          (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold sharpFoldNumerator
  linarith

/-- **Monotone form of the numerator** on `[p, q] ⊆ [7/100, 353/1000]`. -/
theorem sharpFoldNumerator_ge_monotone {κ x p q Lℓ Llam : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 353 / 1000)
    (hLℓ : Real.log (p + 353 / 1000) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * Lℓ +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
          (Llam - 241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
            5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) +
        sharpFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5) ≤
      sharpFoldNumerator κ x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 353 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 353 / 1000) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) =
        -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7061 / 20000 : ℝ) ^ 2 - x ^ 2 = (7061 / 20000 - x) * (7061 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((7061 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7061 / 20000) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 353 / 1000) ^ 2 ≤ (q + 353 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 353 / 1000) ^ 3 ≤ (q + 353 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := sharpFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (Llam - 241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
          5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) - κ - 1 / 40000 -
          (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold sharpFoldNumerator
  nlinarith

theorem sharpFoldNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 1 1 0 3 0 0 1
  have eb := log_smooth_div 0 0 0 1 4 0 0 0
  norm_num at ea eb
  have hv : Real.log (5) ≤ 1.609438 := by linarith [l5.2]
  have ha : Real.log (15/56) ≤ -1.317301 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/16) ≤ -0.826678 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 13/100) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 0 0 0 0 0 0
  have ea := log_smooth_div 0 0 1 0 0 1 0 1
  have eb := log_smooth_div 0 0 2 0 1 3 0 0
  norm_num at ev ea eb
  have hv : Real.log (4) ≤ 1.386295 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/21) ≤ -1.435084 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/54) ≤ -0.770107 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 1/10) (q := 13/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/200)),
    sq_nonneg (x - 23/200), mul_nonneg (sq_nonneg (x - 23/200)) (sq_nonneg (x - 23/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/100 ≤ x)
    (h2 : x ≤ 4/25) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 3 0 0 3 0 0 0
  have ea := log_smooth_div 0 0 1 0 3 1 0 0
  have eb := log_smooth_div 0 0 0 2 2 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (27/8) ≤ 1.216396 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/24) ≤ -1.568615 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/100) ≤ -0.713349 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 13/100) (q := 4/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/200)),
    sq_nonneg (x - 29/200), mul_nonneg (sq_nonneg (x - 29/200)) (sq_nonneg (x - 29/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 4/25 ≤ x)
    (h2 : x ≤ 9/50) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 5 0 0 0 0 0 2 1
  have eb := log_smooth_div 1 0 0 1 0 3 0 0
  norm_num at ea eb
  have hv : Real.log (3) ≤ 1.098613 := by linarith [l3.2]
  have ha : Real.log (32/175) ≤ -1.699049 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (14/27) ≤ -0.656779 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 4/25) (q := 9/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/100)),
    sq_nonneg (x - 17/100), mul_nonneg (sq_nonneg (x - 17/100)) (sq_nonneg (x - 17/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/50 ≤ x)
    (h2 : x ≤ 1/5) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 0 0 1 0 0 1 0
  have ea := log_smooth_div 3 0 0 0 0 0 0 2
  have eb := log_smooth_div 0 3 0 0 1 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (14/5) ≤ 1.029620 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (8/49) ≤ -1.812378 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/50) ≤ -0.616186 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 9/50) (q := 1/5) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 19/100)),
    sq_nonneg (x - 19/100), mul_nonneg (sq_nonneg (x - 19/100)) (sq_nonneg (x - 19/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/5 ≤ x)
    (h2 : x ≤ 11/50) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 0 0 0 0 1 0 0
  have ea := log_smooth_div 0 0 0 0 0 0 0 1
  have eb := log_smooth_div 0 0 1 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (8/3) ≤ 0.980830 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/7) ≤ -1.945910 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/9) ≤ -0.587786 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 1/5) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 21/100)),
    sq_nonneg (x - 21/100), mul_nonneg (sq_nonneg (x - 21/100)) (sq_nonneg (x - 21/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 6/25) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 0 1 0 0 0
  have ea := log_smooth_div 0 0 0 2 4 0 2 0
  have eb := log_smooth_div 3 2 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (5/2) ≤ 0.916291 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (49/400) ≤ -2.099644 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (72/125) ≤ -0.551647 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 11/50) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/100)),
    sq_nonneg (x - 23/100), mul_nonneg (sq_nonneg (x - 23/100)) (sq_nonneg (x - 23/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 13/50) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 1 0 0 0 0 1 0
  have ea := log_smooth_div 1 2 0 0 0 0 2 1
  have eb := log_smooth_div 0 1 0 0 0 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (12/5) ≤ 0.875469 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (18/175) ≤ -2.274414 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/5) ≤ -0.510825 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 6/25) (q := 13/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 1/4)),
    sq_nonneg (x - 1/4), mul_nonneg (sq_nonneg (x - 1/4)) (sq_nonneg (x - 1/4)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/50 ≤ x)
    (h2 : x ≤ 7/25) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 0 0 0 0 0 0 1
  have ea := log_smooth_div 0 0 0 0 2 1 0 0
  have eb := log_smooth_div 0 0 1 0 3 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (16/7) ≤ 0.826679 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/12) ≤ -2.484906 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/8) ≤ -0.470003 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 13/50) (q := 7/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 27/100)),
    sq_nonneg (x - 27/100), mul_nonneg (sq_nonneg (x - 27/100)) (sq_nonneg (x - 27/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/25 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 0 2 0 1 3 0 3 0
  have eb := log_smooth_div 4 0 0 0 0 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (63/1000) ≤ -2.764620 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/25) ≤ -0.446287 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 7/25) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/100)),
    sq_nonneg (x - 29/100), mul_nonneg (sq_nonneg (x - 29/100)) (sq_nonneg (x - 29/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 0 0 0 0 1 1 0
  have ea := log_smooth_div 0 2 0 0 3 0 2 0
  have eb := log_smooth_div 0 1 0 1 5 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (32/15) ≤ 0.757686 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (9/200) ≤ -3.101092 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (21/32) ≤ -0.421213 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 3/10) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 123/400)),
    sq_nonneg (x - 123/400), mul_nonneg (sq_nonneg (x - 123/400)) (sq_nonneg (x - 123/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 2 0 2 1 0 0
  have ea := log_smooth_div 0 0 0 0 1 1 1 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (25/12) ≤ 0.733970 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/30) ≤ -3.401197 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_thirteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 333/1000) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 2 0 0 0 0 1 1
  have ea := log_smooth_div 0 1 0 0 0 0 3 0
  have eb := log_smooth_div 0 3 0 0 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (72/35) ≤ 0.721319 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/125) ≤ -3.729701 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/40) ≤ -0.393042 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 13/40) (q := 333/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 329/1000)),
    sq_nonneg (x - 329/1000), mul_nonneg (sq_nonneg (x - 329/1000)) (sq_nonneg (x - 329/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_nonneg_fourteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 333/1000 ≤ x)
    (h2 : x ≤ 169/500) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 0 0 1 4 0 2 0
  have eb := log_smooth_div 3 1 0 0 0 0 1 1
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/400) ≤ -4.045554 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (24/35) ≤ -0.377294 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (sharpFoldNumerator_ge_tangent (p := 333/1000) (q := 169/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 671/2000)),
    sq_nonneg (x - 671/2000), mul_nonneg (sq_nonneg (x - 671/2000)) (sq_nonneg (x - 671/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem sharpFoldNumerator_edge {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 169/500 ≤ x)
    (h2 : x ≤ 3401/10000) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (169/500 + 353 / 1000) - Real.log (169/500) ≤ 715337 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (169/500 + 353 / 1000) / (169/500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2282937 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (169/500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (169/500) ^ 2 by norm_num)
      (show (0 : ℝ) < 21/2000 by norm_num)
    have e := log_smooth_div 0 1 0 1 4 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 169/500) (q := 3401/10000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 33905/100000)),
    sq_nonneg (x - 33905/100000)]

theorem sharpFoldNumerator_stripA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3401/10000 ≤ x)
    (h2 : x ≤ 341/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (3401/10000 + 353 / 1000) - Real.log (3401/10000) ≤ 712113 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (3401/10000 + 353 / 1000) / (3401/10000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2356582 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (3401/10000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (3401/10000) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/1000 by norm_num)
    have e := log_smooth_div 0 2 0 0 3 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 3401/10000) (q := 341/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 34055/100000)),
    sq_nonneg (x - 34055/100000)]

theorem sharpFoldNumerator_stripB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 341/1000 ≤ x)
    (h2 : x ≤ 342/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (341/1000 + 353 / 1000) - Real.log (341/1000) ≤ 710743 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (341/1000 + 353 / 1000) / (341/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2391945 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (341/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (341/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 21/2500 by norm_num)
    have e := log_smooth_div 0 1 0 1 2 0 4 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 341/1000) (q := 342/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3415/10000)),
    sq_nonneg (x - 3415/10000)]

theorem sharpFoldNumerator_stripC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 342/1000 ≤ x)
    (h2 : x ≤ 3435/10000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (342/1000 + 353 / 1000) - Real.log (342/1000) ≤ 709230 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (342/1000 + 353 / 1000) / (342/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2434547 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (342/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (342/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 24/3125 by norm_num)
    have e := log_smooth_div 3 1 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 342/1000) (q := 3435/10000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 34275/100000)),
    sq_nonneg (x - 34275/100000)]

theorem sharpFoldNumerator_stripD {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3435/10000 ≤ x)
    (h2 : x ≤ 345/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (3435/10000 + 353 / 1000) - Real.log (3435/10000) ≤ 706976 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (3435/10000 + 353 / 1000) / (3435/10000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2506413 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (3435/10000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (3435/10000) ^ 2 by norm_num)
      (show (0 : ℝ) < 1/150 by norm_num)
    have e := log_smooth_div 0 0 0 0 1 1 2 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 3435/10000) (q := 345/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 34425/100000)),
    sq_nonneg (x - 34425/100000)]

theorem sharpFoldNumerator_stripE {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 345/1000 ≤ x)
    (h2 : x ≤ 348/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (345/1000 + 353 / 1000) - Real.log (345/1000) ≤ 704742 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (345/1000 + 353 / 1000) / (345/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2590773 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (345/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (345/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/1600 by norm_num)
    have e := log_smooth_div 0 2 0 0 6 0 2 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 345/1000) (q := 348/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3465/10000)),
    sq_nonneg (x - 3465/10000)]

theorem sharpFoldNumerator_stripF {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 348/1000 ≤ x)
    (h2 : x ≤ 351/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (348/1000 + 353 / 1000) - Real.log (348/1000) ≤ 700332 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (348/1000 + 353 / 1000) / (348/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2821738 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (348/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (348/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 7/2000 by norm_num)
    have e := log_smooth_div 0 0 0 1 4 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 348/1000) (q := 351/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3495/10000)),
    sq_nonneg (x - 3495/10000)]

theorem sharpFoldNumerator_stripG {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 351/1000 ≤ x)
    (h2 : x ≤ 353/1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (351/1000 + 353 / 1000) - Real.log (351/1000) ≤ 695997 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (351/1000 + 353 / 1000) / (351/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3270409 / 1000000 ≤ -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - (351/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (351/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/6250 by norm_num)
    have e := log_smooth_div 0 2 0 0 1 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := sharpFoldNumerator_ge_monotone (p := 351/1000) (q := 353/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 352/1000)),
    sq_nonneg (x - 352/1000)]
/-- The numerator near the origin, `0 < x ≤ 11/250`. -/
theorem sharpFoldNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hxr : x ≤ 353 / 1000 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 353 / 1000) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 353 / 1000) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1041107 / 1000000 ≤
      -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) =
        -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7061 / 20000 : ℝ) ^ 2 - x ^ 2 = (7061 / 20000 - x) * (7061 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7061 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7061 / 20000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((7061 / 20000 : ℝ) ^ 2) = 2 * Real.log (7061 / 20000) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 7061 / 20000 by norm_num) (show (0 : ℝ) < 7 / 20 by norm_num)
    have e7 := log_smooth_div 0 0 0 1 2 0 1 0
    norm_num at e7 ht
    rw [e7] at ht
    linarith
  have hc : 0 ≤ 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 := by nlinarith [pow_le_pow_left₀ h1.le h2 4]
  have hp2 : (x + 353 / 1000) ^ 2 ≤ (11 / 250 + 353 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 353 / 1000) ^ 3 ≤ (11 / 250 + 353 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := sharpFoldGauge_ge h1.le hxr
  have hA : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 353 / 1000) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (1041107 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 353 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) - κ - 1 / 40000 -
          (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) + quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (1041107 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 353 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) +
      sharpFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5) := by
    unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x,
      mul_nonneg (mul_nonneg h1.le h1.le) (sub_nonneg.2 h2), pow_nonneg h1.le 3, pow_nonneg h1.le 4,
      pow_nonneg h1.le 5, pow_nonneg h1.le 6, pow_nonneg h1.le 7]
  unfold sharpFoldNumerator
  linarith

/-- The numerator on a collar `[p, q] ⊆ [11/250, 7/100]`: `ℓ` between its endpoint values. -/
theorem sharpFoldNumerator_ge_collar {κ x p q Llo Lhi Llam : ℝ} (hp : 11 / 250 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 100)
    (hlo : Llo ≤ Real.log (x + 353 / 1000) - Real.log x)
    (hhi : Real.log (x + 353 / 1000) - Real.log x ≤ Lhi)
    (hlam : Llam ≤ -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x))
    (hκ : κ ≤ 241517 / 100000) :
    1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi +
        quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
          5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) +
        sharpFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5) ≤
      sharpFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 353 / 1000 := by linarith
  have hp2 : (x + 353 / 1000) ^ 2 ≤ (q + 353 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 353 / 1000) ^ 3 ≤ (q + 353 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := sharpFoldGauge_ge hx0.le hxr
  have hw : 0 ≤ x ^ 2 + 49 / 20 * x ^ 4 := by positivity
  have hA : 1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 353 / 1000) - Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hhi hw]
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 353 / 1000) ^ 2 / 48 -
          5 * (q + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x *
        (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) - κ - 1 / 40000 -
          (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 - 41 / 2500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold sharpFoldNumerator
  linarith

/-- The window ratio `log((x + 353/1000)/x)` on a collar, from both endpoints. -/
theorem sharpFoldWindowRatio_bounds {x p q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    Real.log (q + 353 / 1000) - Real.log q ≤ Real.log (x + 353 / 1000) - Real.log x ∧
      Real.log (x + 353 / 1000) - Real.log x ≤ Real.log (p + 353 / 1000) - Real.log p := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  rw [← Real.log_div (by linarith) hx0.ne', ← Real.log_div (by linarith) hq0.ne',
    ← Real.log_div (by linarith) hp.ne']
  constructor
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hq0 hx0]; nlinarith)
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hx0 hp]; nlinarith)

theorem sharpFoldNumerator_nonneg_collarA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 11 / 250 ≤ x) (h2 : x ≤ 57 / 1000) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := sharpFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1972738 / 1000000 ≤ Real.log (x + 353 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (57 / 1000 + 353 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 353 / 1000) - Real.log x ≤ 2199751 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (11 / 250 + 353 / 1000) / (11 / 250) by norm_num)
      (show (0 : ℝ) < 9 by norm_num)
    have e9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num at ht ⊢
    linarith
  have hlam : 1048846 / 1000000 ≤
      -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) =
        -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7061 / 20000 : ℝ) ^ 2 - x ^ 2 = (7061 / 20000 - x) * (7061 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7061 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7061 / 20000) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (sharpFoldNumerator_ge_collar (p := 11 / 250) (q := 57 / 1000) le_rfl h1 h2
    (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 5 / 100)),
    sq_nonneg (x - 5 / 100)]

theorem sharpFoldNumerator_nonneg_collarB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 57 / 1000 ≤ x) (h2 : x ≤ 7 / 100) : 0 ≤ sharpFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := sharpFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1798851 / 1000000 ≤ Real.log (x + 353 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (7 / 100 + 353 / 1000) / (7 / 100) by norm_num)
      (show (0 : ℝ) < 6 by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 353 / 1000) - Real.log x ≤ 1973480 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (57 / 1000 + 353 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1054317 / 1000000 ≤
      -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x) =
        -(1 / 2) * Real.log ((7061 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7061 / 20000 : ℝ) ^ 2 - x ^ 2 = (7061 / 20000 - x) * (7061 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7061 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7061 / 20000) ^ 2 - (57 / 1000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7061 / 20000) ^ 2 - (57 / 1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (sharpFoldNumerator_ge_collar (p := 57 / 1000) (q := 7 / 100) (by norm_num) h1
    h2 le_rfl hlo hhi hlam hκ)
  unfold quarticGauge sharpFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 635 / 10000)),
    sq_nonneg (x - 635 / 10000)]

/-- **The numerator exceeds the strip loss on `[0.3401, 0.353]`.** -/
theorem sharpFoldNumerator_strip {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3401 / 10000 ≤ x)
    (h2 : x ≤ 353 / 1000) : 23 / 10000 ≤ sharpFoldNumerator κ x := by
  rcases le_or_gt x (341 / 1000) with ha | ha
  · exact sharpFoldNumerator_stripA hκ h1 ha
  rcases le_or_gt x (342 / 1000) with hb | hb
  · exact sharpFoldNumerator_stripB hκ ha.le hb
  rcases le_or_gt x (3435 / 10000) with hc | hc
  · exact sharpFoldNumerator_stripC hκ hb.le hc
  rcases le_or_gt x (345 / 1000) with hd | hd
  · exact sharpFoldNumerator_stripD hκ hc.le hd
  rcases le_or_gt x (348 / 1000) with he | he
  · exact sharpFoldNumerator_stripE hκ hd.le he
  rcases le_or_gt x (351 / 1000) with hf | hf
  · exact sharpFoldNumerator_stripF hκ he.le hf
  · exact sharpFoldNumerator_stripG hκ hf.le h2

/-- **The numerator is nonnegative on `(0, 353/1000]`.** -/
theorem sharpFoldNumerator_nonneg {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (hx0 : 0 < x)
    (hxr : x ≤ 353 / 1000) : 0 ≤ sharpFoldNumerator κ x := by
  rcases le_or_gt x (11 / 250) with h | h
  · exact sharpFoldNumerator_nonneg_origin hκ hx0 h
  rcases le_or_gt x (57 / 1000) with h' | h'
  · exact sharpFoldNumerator_nonneg_collarA hκ h.le h'
  rcases le_or_gt x (7 / 100) with h0 | h0
  · exact sharpFoldNumerator_nonneg_collarB hκ h'.le h0
  rcases le_or_gt x (1 / 10) with h1 | h1
  · exact sharpFoldNumerator_nonneg_one hκ h0.le h1
  rcases le_or_gt x (13 / 100) with h2 | h2
  · exact sharpFoldNumerator_nonneg_two hκ h1.le h2
  rcases le_or_gt x (4 / 25) with h3 | h3
  · exact sharpFoldNumerator_nonneg_three hκ h2.le h3
  rcases le_or_gt x (9 / 50) with h4 | h4
  · exact sharpFoldNumerator_nonneg_four hκ h3.le h4
  rcases le_or_gt x (1 / 5) with h5 | h5
  · exact sharpFoldNumerator_nonneg_five hκ h4.le h5
  rcases le_or_gt x (11 / 50) with h6 | h6
  · exact sharpFoldNumerator_nonneg_six hκ h5.le h6
  rcases le_or_gt x (6 / 25) with h7 | h7
  · exact sharpFoldNumerator_nonneg_seven hκ h6.le h7
  rcases le_or_gt x (13 / 50) with h8 | h8
  · exact sharpFoldNumerator_nonneg_eight hκ h7.le h8
  rcases le_or_gt x (7 / 25) with h9 | h9
  · exact sharpFoldNumerator_nonneg_nine hκ h8.le h9
  rcases le_or_gt x (3 / 10) with h10 | h10
  · exact sharpFoldNumerator_nonneg_ten hκ h9.le h10
  rcases le_or_gt x (63 / 200) with h11 | h11
  · exact sharpFoldNumerator_nonneg_eleven hκ h10.le h11
  rcases le_or_gt x (13 / 40) with h12 | h12
  · exact sharpFoldNumerator_nonneg_twelve hκ h11.le h12
  rcases le_or_gt x (333 / 1000) with h13 | h13
  · exact sharpFoldNumerator_nonneg_thirteen hκ h12.le h13
  rcases le_or_gt x (169 / 500) with h14 | h14
  · exact sharpFoldNumerator_nonneg_fourteen hκ h13.le h14
  rcases le_or_gt x (3401 / 10000) with h15 | h15
  · exact sharpFoldNumerator_edge hκ h14.le h15
  · linarith [sharpFoldNumerator_strip hκ h15.le hxr]

/-! ### The mixed potential -/

/-- **The potential on `(0, 353/1000]`.** The killing, the mixed surplus potential
`(1 − θ) U_h + θ U_h^{off}`, `θ = 53/100`, and the plateau potential of radius `7061/20000`, with the
second-order expansions of the surplus kernel and of `Ω`, exceed `41/2500`. -/
theorem sharpFoldWindow_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 353 / 1000) :
    41 / 2500 ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 353 / 1000)) + ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (353 / 1000) x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (Real.log 2 - 353 / 1000) (353 / 1000) x) +
        (archLevyAntideriv (7061 / 20000 - x) + archLevyAntideriv (7061 / 20000 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := sharpFoldGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge_second (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)
    hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr => sharpFoldGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge_second hx0 (by linarith)
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 353 / 1000 by linarith)
  have hΩa := archLevyAntideriv_ge_second (show 0 < 7061 / 20000 - x by linarith) (by linarith)
  have hΩb := archLevyAntideriv_ge_second (show 0 < 7061 / 20000 + x by linarith) (by linarith)
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
  have e2 : Real.log ((x + 353 / 1000) / 4) = Real.log (x + 353 / 1000) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((7061 / 20000 - x) / 4) = Real.log (7061 / 20000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((7061 / 20000 + x) / 4) = Real.log (7061 / 20000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 353 / 1000) - Real.log x) +
    (-(1 / 2) * Real.log (7061 / 20000 - x) - 1 / 2 * Real.log (7061 / 20000 + x)) - κ - 1 / 40000 -
    (x + 353 / 1000) ^ 2 / 48 - 5 * (x + 353 / 1000) ^ 3 / 192 +
      (2 * x ^ 2 + (7061 / 20000) ^ 2) / 48 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (353 / 1000) x with hUdef
  set U' := surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (Real.log 2 - 353 / 1000) (353 / 1000) x with hU'def
  have hkey : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V - 41 / 2500) +
      (quarticSurplusMain (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x + firstOrderSurplus (3 / 5) (-1) (-3 / 10) (-49 / 20) (353 / 1000) x - 13 / 20 * (4 / 125 * (353 / 1000) ^ 5)) =
        sharpFoldNumerator κ x := by
    rw [hV]; unfold sharpFoldNumerator quarticSurplusMain cubicSurplusMain sharpFoldPoly quarticGauge
    ring
  -- off the strip the mixed potential is `U`; on the strip it loses at most `23/10000`
  have hoff : (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * U ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * ((1 - 53 / 100) * U + 53 / 100 * U') + 23 / 10000 ∧
        23 / 10000 ≤ sharpFoldNumerator κ x) ∨
      ((1 - 53 / 100) * U + 53 / 100 * U' = U ∧ 0 ≤ sharpFoldNumerator κ x) := by
    by_cases hS : x < Real.log 2 - 353 / 1000
    · right
      refine ⟨?_, sharpFoldNumerator_nonneg hκ hx0 hxr⟩
      have : U' = U := by rw [hU'def, hUdef]; unfold surplusPotentialOff; rw [if_pos hS]
      rw [this]; ring
    · left
      have hpx : Real.log 2 - 353 / 1000 ≤ x := not_lt.mp hS
      have hloss := mul_surplusPotential_le_off_add (h := quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (a₀ := 1 / 500) (L := 13 / 20)
        (by linarith) hpx hxr (by norm_num) (continuous_quarticGauge _ _ _ _ _) (by norm_num) hh
        (by norm_num) (fun y hy0 hyr => by
          rw [quarticGauge_sub, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (sharpFoldGauge_divDiff_le hx0.le hxr hy0.le hyr)
            (abs_nonneg _))
      refine ⟨?_, sharpFoldNumerator_strip hκ (by linarith) hxr⟩
      have hd0 : 0 ≤ 353 / 1000 - (Real.log 2 - 353 / 1000) := by linarith
      have hd1 : 353 / 1000 - (Real.log 2 - 353 / 1000) ≤ 12853 / 1000000 := by linarith
      have hd : 53 / 100 * (13 / 20 * (353 / 1000 - (Real.log 2 - 353 / 1000)) *
          (1 / 2 + (353 / 1000 - (Real.log 2 - 353 / 1000)) / 4)) ≤ 23 / 10000 := by
        have hm := mul_le_mul hd1 (show 1 / 2 + (353 / 1000 - (Real.log 2 - 353 / 1000)) / 4 ≤
          1 / 2 + 12853 / 1000000 / 4 by linarith) (by linarith) (by norm_num)
        linarith only [hm]
      rw [hU'def, hUdef]
      linarith only [hloss, hd]
  clear_value V U U'
  have hVU : 41 / 2500 ≤ V + ((1 - 53 / 100) * U + 53 / 100 * U') := by
    have h1 : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (41 / 2500) ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V + ((1 - 53 / 100) * U + 53 / 100 * U')) := by
      have e : quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V + ((1 - 53 / 100) * U + 53 / 100 * U')) =
          quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * (V - 41 / 2500) + quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x * ((1 - 53 / 100) * U + 53 / 100 * U') +
            41 / 2500 * quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20) x := by ring
      rw [e]
      rcases hoff with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith only [hkey, hU, h1, h2]
      · rw [h1]; linarith only [hkey, hU, h2]
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + ((1 - 53 / 100) * U + 53 / 100 * U') ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 353 / 1000)) +
        ((1 - 53 / 100) * U + 53 / 100 * U') +
      (archLevyAntideriv (7061 / 20000 - x) + archLevyAntideriv (7061 / 20000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV, hκdef]; linarith only [hΩx, hΩr, hΩa, hΩb]
  linarith only [hVU, hW]

/-! ### Odd-sector positivity on `[−353/1000, 353/1000]` -/

/-- **Weil positivity of every odd test supported in `[−353/1000, 353/1000]`.** The sharp
micro-fold pays the atom with `53%` of the strip surplus; the rest stays in the ground-state
potential: `Ẑ(F) ≥ (1/1000) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 353 / 1000 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 353 / 1000 with hrdef
  set R : ℝ := 7061 / 20000 with hRdef
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
    have hη1 : (r - (Real.log 2 - r)) / 2 ≤ 643 / 100000 := by rw [hrdef]; linarith
    have hp : 3401 / 10000 ≤ Real.log 2 - r := by rw [hrdef]; linarith
    have hq : (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) ≤ 19 / 1000 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hsq : 3 * ((r - (Real.log 2 - r)) / 2) ^ 2 ≤ 13 / 100000 := by nlinarith
    linarith
  -- representation with the prime `2`; the micro-fold pays the whole prime term
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_potentialMix_le_archJump_sub_prime hPd.continuous
    hF.continuous hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (θ := 53 / 100) hFc
    (by rw [hrdef]; linarith) (by rw [hrdef]; linarith) (by norm_num) (by norm_num) hθ
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs
    (continuous_quarticGauge _ _ _ _ _) (a₀ := 1 / 500) (by norm_num)
    (fun x hx0 hxr => sharpFoldGauge_ge hx0 hxr) (L := 13 / 20)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (sharpFoldGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
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
  set c₀ : ℝ := 41 / 2500 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (L - r) r x) + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : 41 / 2500 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) +
          ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (L - r) r x) +
          (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) - 2 * windowEdgeFunction 0 -
            2 * archConstantReal) := sharpFoldWindow_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      rw [hc₀]
      linarith
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (L - r) r x) + G₁ x) (Ioi 0) :=
    ((hHi.const_mul 2).add hIU).add hG₁i.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * ((1 - 53 / 100) * surplusPotential (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) r x + 53 / 100 * surplusPotentialOff (quarticGauge (1 / 500) (3 / 5) (-1) (-3 / 10) (-49 / 20)) (L - r) r x)) (Ioi 0) := hH2.add hIU
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2U hG₁i.integrableOn, integral_add hH2 hIU, integral_const_mul,
    integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 1031708 / 1000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 156 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (156 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (156 / 10000) ≤ 101573 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 156 / 10000 by norm_num)
        (show (156 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101573 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 757 / 50000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 757 / 100000 := by
      have : R ^ 3 / 6 = (7061 / 20000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      have := mul_le_mul_of_nonneg_left hcosh (show (0 : ℝ) ≤ (7061 / 20000) ^ 3 / 6 by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  rw [hc₀] at hmono
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ, hI0]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
