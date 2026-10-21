import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedPairHankelSelectivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldBoundaryQuarticGaugeWeilPositivity

/-!
# The shifted pair has no positive window: even tests at every radius

The completed product `Λ(s − a) Λ(s + a)` shares the Euler product, the functional equation and the
Dirichlet structure of an `L`-function with `ζ`, but its zeros `ρ ± a` lie off the line. On a test
supported in `[−r, r]`, `2r < log 2`, its zero form is (`shiftedPairZeroForm_eq`)

    Ẑ_a(F) = 2 Ẑ(F) + 4 ∫_0^∞ (cosh(at) − 1)(2cosh(t/2) − ω(t)) A_F(t) dt.

For a nonnegative bump `H` on `(0, ∞)` put `G_a(y) = e^{−ay} H(y)` and take the **even** extension
`F_a = G_a + G_a(−·)`. Its autocorrelation is `2A_{G_a} + G_a ∗ G_a` (`autoCorr_add_reflect`), and
`G_a ∗ G_a = e^{−at} H ∗ H`. Hence (`shiftedPairZeroForm_evenShiftTest`)

    Ẑ_a(F_a) = 2Ẑ(F_a) + 8 ∫ (cosh(at) − 1)(2cosh(t/2) − ω) A_{G_a} − 2 ∫ (1 − e^{−at})² f (H ∗ H),

`f = ω − 2cosh(t/2)`. Below the plastic threshold the middle term is `≤ 0` (the screw weight is
negative and `A_{G_a} ≥ 0`), the first is `O(a² e^{−a y₀})`, and the last tends to
`−2 ∫ f (H ∗ H) < 0`: on even tests the shifted pair converts the negative off-diagonal coupling of
`Ẑ` between `H` and its reflection into its diagonal. So, unlike the odd case, no indefiniteness of the
Hankel form is needed and the bump can be taken arbitrarily close to the origin
(`exists_even_shiftedPairZeroForm_neg`): **for every radius `r > 0` and every large shift `a` some even
test supported in `[−r, r]` has negative `ζ(s − a) ζ(s + a)` zero form.** Window positivity of `ζ` at
any aperture, in particular on `[−7/25, 7/25]` (`foldBoundary_window_selective`), is not a consequence
of the structure `ζ(s − a) ζ(s + a)` shares with `ζ`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The even extension of a half-line profile -/

/-- For `G` supported in `(0, ∞)` and `t > 0`, the autocorrelation of the even extension
`G + G(−·)` is `2 A_G(t) + (G ∗ G)(t)`. -/
theorem autoCorr_add_reflect {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (hG0 : ∀ x, x ≤ 0 → G x = 0) {t : ℝ} (ht : 0 < t) :
    autoCorr (fun x => G x + G (-x)) t = 2 * autoCorr G t + selfConv G t := by
  have hint : ∀ g h : ℝ → ℝ, Continuous g → Continuous h → HasCompactSupport g →
      Integrable fun x => g x * h x := fun g h hg hh hgc =>
    (hg.mul hh).integrable_of_hasCompactSupport hgc.mul_right
  have hc1 : Continuous fun x => G (x + t) := hG.comp (continuous_id.add continuous_const)
  have hc2 : Continuous fun x => G (-x - t) := hG.comp (continuous_neg.sub continuous_const)
  have hc3 : Continuous fun x => G (-x) := hG.comp continuous_neg
  have hGc' := hGc.comp_homeomorph (Homeomorph.neg ℝ)
  have i1 := hint (fun x => G x) (fun x => G (x + t)) hG hc1 hGc
  have i2 := hint (fun x => G x) (fun x => G (-x - t)) hG hc2 hGc
  have i3 := hint (fun x => G (-x)) (fun x => G (x + t)) hc3 hc1 hGc'
  have i4 := hint (fun x => G (-x)) (fun x => G (-x - t)) hc3 hc2 hGc'
  have h0 : ∀ x, G x * G (-x - t) = 0 := fun x => by
    by_cases hx : x ≤ 0
    · rw [hG0 x hx, zero_mul]
    · rw [hG0 (-x - t) (by linarith), mul_zero]
  have h4 : (∫ x, G (-x) * G (-x - t)) = autoCorr G t := by
    have e1 : (∫ x, G (-x) * G (-x - t)) = ∫ x, G x * G (x - t) :=
      integral_neg_eq_self (fun y => G y * G (y - t)) volume
    rw [e1, ← integral_add_right_eq_self (fun x => G x * G (x - t)) t]
    unfold autoCorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
    ring
  have h3 : (∫ x, G (-x) * G (x + t)) = selfConv G t := by
    have e1 : (∫ x, G (-x) * G (x + t)) = ∫ x, G x * G (-x + t) := by
      rw [← integral_neg_eq_self (fun y => G y * G (-y + t)) volume]
      simp only [neg_neg]
    rw [e1]
    unfold selfConv
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show -x + t = t - x by ring]
  unfold autoCorr
  have e : (fun x => (G x + G (-x)) * (G (x + t) + G (-(x + t)))) =
      fun x => G x * G (x + t) + G x * G (-x - t) + G (-x) * G (x + t) + G (-x) * G (-x - t) := by
    funext x; rw [show -(x + t) = -x - t by ring]; ring
  have i12 : Integrable fun x => G x * G (x + t) + G x * G (-x - t) := i1.add i2
  have i123 : Integrable fun x => G x * G (x + t) + G x * G (-x - t) + G (-x) * G (x + t) :=
    i12.add i3
  rw [e, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, h4, h3]
  simp only [h0, integral_zero]
  unfold autoCorr
  ring

/-! ### The even shift test -/

/-- The bump `H = φ_{ε/2, ε/4}`, supported in `(ε/4, 3ε/4)`. -/
def evenBump (ε y : ℝ) : ℝ := bumpAt (ε / 2) (ε / 4) y

/-- The reweighted bump `G_a(y) = e^{−ay} H(y)`. -/
def evenReweighted (ε a y : ℝ) : ℝ := Real.exp (-a * y) * evenBump ε y

/-- The even shift test `F_a(x) = G_a(x) + G_a(−x)`. -/
def evenShiftTest (ε a x : ℝ) : ℝ := evenReweighted ε a x + evenReweighted ε a (-x)

section EvenShift

variable {ε : ℝ} (hε : 0 < ε)

include hε in
theorem evenBump_eq_zero_of_le {y : ℝ} (hy : y ≤ ε / 4) : evenBump ε y = 0 :=
  bumpAt_eq_zero (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)

include hε in
theorem evenBump_eq_zero_of_ge {y : ℝ} (hy : 3 * ε / 4 ≤ y) : evenBump ε y = 0 :=
  bumpAt_eq_zero (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)

theorem evenBump_nonneg (y : ℝ) : 0 ≤ evenBump ε y := bumpAt_nonneg _ _ _

theorem evenBump_le_one (y : ℝ) : evenBump ε y ≤ 1 := plateauGauge_le_one _ _ _

theorem contDiff_evenBump : ContDiff ℝ 2 (evenBump ε) := contDiff_bumpAt _ _

include hε in
theorem hasCompactSupport_evenBump : HasCompactSupport (evenBump ε) :=
  hasCompactSupport_bumpAt (by linarith)

theorem contDiff_evenReweighted (a : ℝ) : ContDiff ℝ 2 (evenReweighted ε a) :=
  (by fun_prop : ContDiff ℝ 2 fun y : ℝ => Real.exp (-a * y)).mul contDiff_evenBump

include hε in
theorem hasCompactSupport_evenReweighted (a : ℝ) : HasCompactSupport (evenReweighted ε a) :=
  (hasCompactSupport_evenBump hε).mul_left

include hε in
theorem evenReweighted_eq_zero_of_le (a : ℝ) {y : ℝ} (hy : y ≤ ε / 4) :
    evenReweighted ε a y = 0 := by
  rw [evenReweighted, evenBump_eq_zero_of_le hε hy, mul_zero]

include hε in
theorem evenReweighted_eq_zero_of_abs (a : ℝ) {x : ℝ} (hx : 3 * ε / 4 < |x|) :
    evenReweighted ε a x = 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [evenReweighted, evenBump_eq_zero_of_ge hε hx.le, mul_zero]
  · exact evenReweighted_eq_zero_of_le hε a (by linarith)

theorem evenReweighted_nonneg (a y : ℝ) : 0 ≤ evenReweighted ε a y :=
  mul_nonneg (Real.exp_pos _).le (evenBump_nonneg y)

include hε in
theorem evenShiftTest_eq_zero (a : ℝ) {x : ℝ} (hx : 3 * ε / 4 < |x|) :
    evenShiftTest ε a x = 0 := by
  rw [evenShiftTest, evenReweighted_eq_zero_of_abs hε a hx,
    evenReweighted_eq_zero_of_abs hε a (by rwa [abs_neg]), add_zero]

theorem evenShiftTest_neg (a x : ℝ) : evenShiftTest ε a (-x) = evenShiftTest ε a x := by
  rw [evenShiftTest, evenShiftTest, neg_neg]; ring

theorem contDiff_evenShiftTest (a : ℝ) : ContDiff ℝ 2 (evenShiftTest ε a) :=
  (contDiff_evenReweighted a).add ((contDiff_evenReweighted a).comp contDiff_neg)

include hε in
theorem hasCompactSupport_evenShiftTest (a : ℝ) : HasCompactSupport (evenShiftTest ε a) :=
  HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun x hx =>
    evenShiftTest_eq_zero hε a (by
      have := lt_abs_of_notMem_Icc hx
      linarith)

include hε in
theorem abs_evenReweighted_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ) :
    |evenReweighted ε a y| ≤ Real.exp (-a * (ε / 4)) := by
  by_cases hy : y ≤ ε / 4
  · rw [evenReweighted_eq_zero_of_le hε a hy, abs_zero]; positivity
  · rw [evenReweighted, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (evenBump_nonneg y)]
    have he : Real.exp (-a * y) ≤ Real.exp (-a * (ε / 4)) :=
      Real.exp_le_exp.mpr (by nlinarith [not_le.mp hy])
    calc Real.exp (-a * y) * evenBump ε y ≤ Real.exp (-a * (ε / 4)) * 1 :=
          mul_le_mul he (evenBump_le_one y) (evenBump_nonneg y) (Real.exp_pos _).le
      _ = _ := mul_one _

include hε in
theorem abs_evenShiftTest_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |evenShiftTest ε a x| ≤ Real.exp (-a * (ε / 4)) := by
  rw [evenShiftTest]
  rcases le_or_gt 0 x with h | h
  · rw [evenReweighted_eq_zero_of_le hε a (show -x ≤ ε / 4 by linarith), add_zero]
    exact abs_evenReweighted_le hε ha x
  · rw [evenReweighted_eq_zero_of_le hε a (show x ≤ ε / 4 by linarith), zero_add]
    exact abs_evenReweighted_le hε ha (-x)

include hε in
theorem integral_sq_evenShiftTest_le {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, evenShiftTest ε a x ^ 2) ≤ 2 * ε * Real.exp (-a * (ε / 2)) := by
  have hcs : HasCompactSupport fun x => evenShiftTest ε a x ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun x hx => by
      rw [evenShiftTest_eq_zero hε a (by linarith [lt_abs_of_notMem_Icc hx]), zero_pow two_ne_zero]
  have hint : Integrable fun x => evenShiftTest ε a x ^ 2 :=
    ((contDiff_evenShiftTest a).continuous.pow 2).integrable_of_hasCompactSupport hcs
  have hsq : Real.exp (-a * (ε / 4)) ^ 2 = Real.exp (-a * (ε / 2)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc (∫ x, evenShiftTest ε a x ^ 2) ≤ ∫ x, (Icc (-ε) ε).indicator
        (fun _ => Real.exp (-a * (ε / 4)) ^ 2) x := by
        refine integral_mono hint ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (by simp))) fun x => ?_
        by_cases hx : x ∈ Icc (-ε) ε
        · rw [Set.indicator_of_mem hx, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_evenShiftTest_le hε ha x) 2
        · rw [Set.indicator_of_notMem hx, evenShiftTest_eq_zero hε a (by
            linarith [lt_abs_of_notMem_Icc hx])]
          norm_num
    _ = 2 * ε * Real.exp (-a * (ε / 2)) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc, max_eq_left (by linarith), hsq]
        ring

include hε in
theorem lipschitz_evenShiftTest {a L : ℝ} (ha : 0 ≤ a)
    (hL : ∀ x y, |evenBump ε y - evenBump ε x| ≤ L * |y - x|) (u v : ℝ) :
    |evenShiftTest ε a u - evenShiftTest ε a v| ≤
      2 * Real.exp (-a * (ε / 4)) * (L + a * 1) * |u - v| := by
  have hG : ∀ u v, |evenReweighted ε a u - evenReweighted ε a v| ≤
      Real.exp (-a * (ε / 4)) * (L + a * 1) * |u - v| := fun u v =>
    lipschitz_exp_mul ha (fun y hy => evenBump_eq_zero_of_le hε hy.le) (fun u v => hL v u)
      (fun y => by rw [abs_of_nonneg (evenBump_nonneg y)]; exact evenBump_le_one y) u v
  have h1 := hG u v
  have h2 := hG (-u) (-v)
  rw [show -u - -v = -(u - v) by ring, abs_neg] at h2
  rw [evenShiftTest, evenShiftTest,
    show evenReweighted ε a u + evenReweighted ε a (-u) -
        (evenReweighted ε a v + evenReweighted ε a (-v)) =
      (evenReweighted ε a u - evenReweighted ε a v) +
        (evenReweighted ε a (-u) - evenReweighted ε a (-v)) by ring]
  have h3 := abs_add_le (evenReweighted ε a u - evenReweighted ε a v)
    (evenReweighted ε a (-u) - evenReweighted ε a (-v))
  linarith

/-! ### The comparison identity and its three terms -/

include hε in
/-- **The comparison identity for `F_a = G_a + G̃_a`.** The cross term between `G_a` and its
reflection enters with the sign opposite to the odd case:
`Ẑ_a(F_a) = 2Ẑ(F_a) + 8∫(cosh(at) − 1)κ A_{G_a} − 2∫(1 − e^{−at})² f (H ∗ H)`. -/
theorem shiftedPairZeroForm_evenShiftTest (hε1 : ε ≤ 1 / 10) (a : ℝ) :
    shiftedPairZeroForm a (evenShiftTest ε a) = 2 * fullZeroForm (evenShiftTest ε a) +
      8 * (∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
        (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t) -
      2 * ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t *
        selfConv (evenBump ε) t := by
  have hlog : 2 * (3 * ε / 4) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨hIF, hEF⟩ := shiftedPairZeroForm_eq (contDiff_evenShiftTest a)
    (hasCompactSupport_evenShiftTest hε a) (fun x hx => evenShiftTest_eq_zero hε a hx)
    (by linarith) hlog a
  obtain ⟨hIG, -⟩ := shiftedPairZeroForm_eq (contDiff_evenReweighted a)
    (hasCompactSupport_evenReweighted hε a) (fun x hx => evenReweighted_eq_zero_of_abs hε a hx)
    (by linarith) hlog a
  have hptw : ∀ t ∈ Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenShiftTest ε a) t =
        2 * ((Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
          autoCorr (evenReweighted ε a) t) -
        1 / 2 * ((1 - Real.exp (-a * t)) ^ 2 * screwWeight t * selfConv (evenBump ε) t) := by
    intro t ht
    have hA : autoCorr (evenShiftTest ε a) t =
        2 * autoCorr (evenReweighted ε a) t + selfConv (evenReweighted ε a) t :=
      autoCorr_add_reflect (contDiff_evenReweighted a).continuous
        (hasCompactSupport_evenReweighted hε a)
        (fun x hx => evenReweighted_eq_zero_of_le hε a (by linarith)) ht
    have hS : selfConv (evenReweighted ε a) t = Real.exp (-a * t) * selfConv (evenBump ε) t :=
      selfConv_exp_mul (evenBump ε) a t
    have hce := cosh_sub_one_mul_exp_neg (a * t)
    rw [← neg_mul] at hce
    rw [hA, hS, screwWeight]
    linear_combination
      ((2 * Real.cosh (t / 2) - archLevyDensity t) * selfConv (evenBump ε) t) * hce
  have hIF' : Integrable (fun t => (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenShiftTest ε a) t)
      (volume.restrict (Ioi 0)) := hIF
  have hIG' : Integrable (fun t => 2 * ((Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t))
      (volume.restrict (Ioi 0)) := hIG.const_mul 2
  have hdiff : Integrable (fun t => 2 * ((Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t) -
        (Real.cosh (a * t) - 1) * (2 * Real.cosh (t / 2) - archLevyDensity t) *
          autoCorr (evenShiftTest ε a) t) (volume.restrict (Ioi 0)) := hIG'.sub hIF'
  have hIW : Integrable (fun t => 1 / 2 *
      ((1 - Real.exp (-a * t)) ^ 2 * screwWeight t * selfConv (evenBump ε) t))
      (volume.restrict (Ioi 0)) :=
    hdiff.congr ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
      dsimp only; rw [hptw t ht]; ring)
  rw [hEF, setIntegral_congr_fun measurableSet_Ioi hptw, integral_sub hIG' hIW,
    integral_const_mul, integral_const_mul]
  ring

include hε in
/-- **The same-side term is nonpositive** below the plastic threshold: the screw weight is
negative there and `A_{G_a} ≥ 0`. -/
theorem integral_sameSide_evenReweighted_nonpos (hε1 : ε ≤ 1 / 10) (a : ℝ) :
    (∫ t in Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
        (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t) ≤ 0 := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t ≤ 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hc : 0 ≤ Real.cosh (a * t) - 1 := by linarith [Real.one_le_cosh (a * t)]
    have hA : 0 ≤ autoCorr (evenReweighted ε a) t :=
      integral_nonneg fun x => mul_nonneg (evenReweighted_nonneg a x) (evenReweighted_nonneg a _)
    by_cases ht1 : t ≤ 0.28
    · have hk : 2 * Real.cosh (t / 2) - archLevyDensity t ≤ 0 := by
        linarith [two_mul_cosh_le_archLevyDensity_of_le_plastic ht0 ht1]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc hk) hA
    · have hA0 : autoCorr (evenReweighted ε a) t = 0 := by
        unfold autoCorr
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.zero_apply]
        by_cases hx : x ≤ ε / 4
        · rw [evenReweighted_eq_zero_of_le hε a hx, zero_mul]
        · rw [evenReweighted_eq_zero_of_abs hε a (x := x + t) (by
            rw [abs_of_pos (by linarith)]; linarith [not_le.mp ht1, not_le.mp hx]), mul_zero]
      rw [hA0, mul_zero]
  have hneg : 0 ≤ ∫ t in Ioi (0 : ℝ), -((Real.cosh (a * t) - 1) *
      (2 * Real.cosh (t / 2) - archLevyDensity t) * autoCorr (evenReweighted ε a) t) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => by linarith [hpt t ht]
  rw [integral_neg] at hneg
  linarith

include hε in
/-- **The Hankel term is bounded below** by `(3/2)(1 − e^{−aε/2})² m²`, `m = ∫ φ_{0, ε/4}`: on the
support `(ε/2, 3ε/2)` of `H ∗ H` the screw weight exceeds `3/2`. -/
theorem integral_hankel_evenBump_ge (hε1 : ε ≤ 1 / 10) {a : ℝ} (ha : 0 ≤ a) :
    3 / 2 * (1 - Real.exp (-a * (ε / 2))) ^ 2 * (∫ x, bumpAt 0 (ε / 4) x) ^ 2 ≤
      ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t *
        selfConv (evenBump ε) t := by
  have hw : (0 : ℝ) < ε / 4 := by linarith
  have hg : Measurable fun t => (1 - Real.exp (-a * t)) ^ 2 * screwWeight t :=
    ((by fun_prop : Continuous fun t : ℝ => (1 - Real.exp (-a * t)) ^ 2).measurable).mul
      measurable_screwWeight
  have hsupp : ∀ t, |t - (ε / 2 + ε / 2)| < 2 * (ε / 4) → ε / 2 < t ∧ t < 3 * ε / 2 := fun t ht => by
    rw [abs_lt] at ht; constructor <;> linarith
  have hL : ∀ t, |t - (ε / 2 + ε / 2)| < 2 * (ε / 4) →
      3 / 2 * (1 - Real.exp (-a * (ε / 2))) ^ 2 ≤ (1 - Real.exp (-a * t)) ^ 2 * screwWeight t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hsupp t ht
    have ht0 : 0 < t := by linarith
    have hf : 3 / 2 ≤ screwWeight t := by
      have h := weilJumpDensity_ge_poly ht0 (by linarith)
      have hinv : 10 / 3 ≤ 1 / (2 * t) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have ht4 : t ^ 4 ≤ 1 := by nlinarith [pow_le_one₀ ht0.le (show t ≤ 1 by linarith) (n := 4)]
      have ht5 : t ^ 5 ≤ 1 := pow_le_one₀ ht0.le (by linarith)
      unfold screwWeight
      unfold weilJumpDensity at h
      nlinarith
    have he : Real.exp (-a * t) ≤ Real.exp (-a * (ε / 2)) := Real.exp_le_exp.mpr (by nlinarith)
    have he1 : Real.exp (-a * (ε / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hsq : (1 - Real.exp (-a * (ε / 2))) ^ 2 ≤ (1 - Real.exp (-a * t)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsq0 : 0 ≤ (1 - Real.exp (-a * (ε / 2))) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul hsq hf (by norm_num) (sq_nonneg _)]
  have hU : ∀ t, |t - (ε / 2 + ε / 2)| < 2 * (ε / 4) →
      (1 - Real.exp (-a * t)) ^ 2 * screwWeight t ≤ 3 / ε := by
    intro t ht
    obtain ⟨h1, h2⟩ := hsupp t ht
    have ht0 : 0 < t := by linarith
    have hω := archLevyDensity_le_of_le_one ht0 (by linarith)
    have hc := (Real.cosh_pos (t / 2)).le
    have he0 := Real.exp_pos (-a * t)
    have he1 : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hsq : (1 - Real.exp (-a * t)) ^ 2 ≤ 1 := by nlinarith
    have hsw : screwWeight t ≤ 3 / ε := by
      unfold screwWeight
      have : 3 / 2 / t ≤ 3 / ε := by
        rw [div_div, div_le_div_iff₀ (by positivity) hε]; nlinarith
      linarith
    have hsw0 : 0 ≤ screwWeight t := by
      unfold screwWeight
      linarith [two_mul_cosh_le_archLevyDensity_of_le_plastic ht0 (by linarith)]
    nlinarith [mul_le_mul hsq hsw hsw0 zero_le_one, sq_nonneg (1 - Real.exp (-a * t))]
  obtain ⟨hI, hlow, -⟩ := integral_mul_bumpConv_bounds hw (y := ε / 2) (y' := ε / 2) hg hL hU
  have hconv : ∀ t, selfConv (evenBump ε) t = bumpConv (bumpAt (ε / 2) (ε / 4))
      (bumpAt (ε / 2) (ε / 4)) t := fun t => rfl
  have hzero : ∀ t ∉ Ioi (0 : ℝ), (1 - Real.exp (-a * t)) ^ 2 * screwWeight t *
      selfConv (evenBump ε) t = 0 := by
    intro t ht
    have ht0 : t ≤ 0 := not_lt.mp ht
    rw [hconv, bumpConv_eq_zero hw (by rw [abs_of_neg (by linarith)]; linarith), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp_rw [hconv]
  exact hlow

end EvenShift

/-! ### Selectivity at every radius -/

/-- **The shifted pair has no positive window.** For every radius `r > 0` and every large shift `a`
some even `F ∈ C²_c` supported in `[−r, r]` has negative `ζ(s − a) ζ(s + a)` zero form. -/
theorem exists_even_shiftedPairZeroForm_neg {r : ℝ} (hr : 0 < r) :
    ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = F x) ∧ (∀ x, r < |x| → F x = 0) ∧ shiftedPairZeroForm a F < 0 := by
  set ε := min r (1 / 10) with hεdef
  have hε : 0 < ε := lt_min hr (by norm_num)
  have hε1 : ε ≤ 1 / 10 := min_le_right _ _
  have hεr : ε ≤ r := min_le_left _ _
  have hlog : 2 * (3 * ε / 4) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨C, hC⟩ := exists_fullZeroForm_le_lipschitz (r := 3 * ε / 4) (by linarith) hlog
  obtain ⟨L, -, hL⟩ := exists_lipschitz_bound_of_compactSupport
    ((contDiff_evenBump (ε := ε)).of_le (by norm_num)) (hasCompactSupport_evenBump hε)
  set m := ∫ x, bumpAt 0 (ε / 4) x with hmdef
  have hm : 0 < m ^ 2 := by
    have : ε / 4 ≤ m := le_integral_bumpAt (by linarith)
    have : 0 < m := by linarith
    positivity
  have hβ : (0 : ℝ) < ε / 2 := by linarith
  -- the error terms decay
  have htend := (((tendsto_pow_mul_exp_neg_mul hβ 2).const_mul 8).add
    ((tendsto_pow_mul_exp_neg_mul hβ 1).const_mul (16 * L))).add
    ((tendsto_pow_mul_exp_neg_mul hβ 0).const_mul (8 * L ^ 2 + 4 * ε * max C 0))
  simp only [mul_zero, add_zero, pow_one, pow_zero, one_mul] at htend
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds
    (show (0 : ℝ) < m ^ 2 / 4 by positivity)))
  have hexp := (tendsto_pow_mul_exp_neg_mul hβ 0)
  simp only [pow_zero, one_mul] at hexp
  obtain ⟨a₂, ha₂⟩ := eventually_atTop.mp (hexp.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨max (max a₁ a₂) 0, fun a ha => ⟨evenShiftTest ε a, contDiff_evenShiftTest a,
    hasCompactSupport_evenShiftTest hε a, evenShiftTest_neg a,
    fun x hx => evenShiftTest_eq_zero hε a (by linarith), ?_⟩⟩
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) ha
  have ha1 : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha2 : a₂ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  -- the three terms
  have hZ := hC _ (contDiff_evenShiftTest a) (hasCompactSupport_evenShiftTest hε a)
    (fun x hx => evenShiftTest_eq_zero hε a hx) _ (lipschitz_evenShiftTest hε ha0 hL)
  have hI0 : 0 ≤ ∫ x, evenShiftTest ε a x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hCI : C * (∫ x, evenShiftTest ε a x ^ 2) ≤
      max C 0 * (2 * ε * Real.exp (-a * (ε / 2))) :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hI0).trans
      (mul_le_mul_of_nonneg_left (integral_sq_evenShiftTest_le hε ha0) (le_max_right C 0))
  have hK : (2 * Real.exp (-a * (ε / 4)) * (L + a * 1)) ^ 2 =
      4 * Real.exp (-a * (ε / 2)) * (L + a) ^ 2 := by
    have : Real.exp (-a * (ε / 4)) ^ 2 = Real.exp (-a * (ε / 2)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, mul_pow, this]; ring
  have hS := integral_sameSide_evenReweighted_nonpos hε hε1 a
  have hH := integral_hankel_evenBump_ge hε hε1 ha0
  have he := ha₂ a ha2
  have hsq : 1 / 4 ≤ (1 - Real.exp (-a * (ε / 2))) ^ 2 := by
    have h0 := Real.exp_pos (-a * (ε / 2))
    nlinarith
  have hsmall := ha₁ a ha1
  rw [shiftedPairZeroForm_evenShiftTest hε hε1]
  nlinarith [hZ, hCI, hK, hS, hH, hsq, hsmall, mul_le_mul_of_nonneg_left hsq hm.le]

/-- **ζ against `ζ(s − a) ζ(s + a)` at the fold boundary.** Every test supported in `[−7/25, 7/25]`
has `Ẑ(F) ≥ (1/500)∫F²` for `ζ`, while for every radius `r > 0` and every large shift `a` some even
test supported in `[−r, r]` has negative zero form for `ζ(s − a) ζ(s + a)`. -/
theorem foldBoundary_window_selective :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, 7 / 25 < |x| → F x = 0) →
        1 / 500 * ∫ x, F x ^ 2 ≤ fullZeroForm F) ∧
      ∀ r : ℝ, 0 < r → ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧
        HasCompactSupport F ∧ (∀ x, F (-x) = F x) ∧ (∀ x, r < |x| → F x = 0) ∧
          shiftedPairZeroForm a F < 0 :=
  ⟨fun _ hF hFc hsupp => fullZeroForm_ge_of_support_le_foldBoundary hF hFc hsupp,
    fun _ hr => exists_even_shiftedPairZeroForm_neg hr⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory
