import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity
import GaloisForLFunctions.HTGeometry.LogNodeExponentialTail
import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination

/-!
# Prime-blind positivity on the cone of separated narrow bumps

For a configuration `f = Σ_j a_j φ(· − x_j)` (`bumpSum`) write `R(y) = ∫ f(u) f(u − y) du`
(`autocorr`).  This file proves the tools for nonnegative combinations `g = Σ_k c_k R_k` of such
autocorrelations that vanish at every `log n`, `n ≥ 2`, the cancellation being allowed across the
tests:

* `abs_autocorr_le`: `|R(y)| ≤ ‖f‖²`;
* `abs_autocorr_sub_le`: if the bump has `L²` modulus `‖φ − φ(· − h)‖ ≤ (κ|h|/δ)‖φ‖` for
  `|h| ≤ δ` and the centres are `s`-separated with `s > 3δ`, then
  `|R(y) − R(y′)| ≤ (κ/δ)|y − y′| ‖f‖²` for `|y − y′| ≤ δ`;
* `integral_autocorr_mul_exp`: the pole is the exponential moment
  `(∫ f e^{u/2})(∫ f e^{−u/2}) = ∫ R(y) e^{y/2} dy`;
* `abs_integral_near_le`: `|∫_{−Y}^{Y} R(y) e^{y/2} dy| ≤ 2δ e^{Y/2} (2 + 2(Y + δ)/s) ‖f‖²`;
* `abs_integral_left_le`: `|∫_{−T}^{−Y} R(y) e^{y/2} dy| ≤ 2 e^{−Y/2} ‖f‖²`.
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23

noncomputable section

namespace RHTower.SeparatedBump

open WeilLevyPole

variable {N : ℕ}

/-- The autocorrelation `R(y) = ∫ f(u) f(u − y) du` of a configuration. -/
def autocorr (φ : ℝ → ℝ) (a x : Fin N → ℝ) (y : ℝ) : ℝ :=
  ∫ u, bumpSum φ a x u * bumpSum φ a x (u - y)

theorem integrable_bumpSum_sq {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) :
    Integrable fun u => bumpSum φ a x u ^ (2 : ℕ) := by
  have hf := (contDiff_bumpSum hφ a x).continuous
  have hfc := hasCompactSupport_bumpSum hφs a x
  have hc : HasCompactSupport ((fun t : ℝ => t ^ (2 : ℕ)) ∘ bumpSum φ a x) :=
    hfc.comp_left (by norm_num)
  exact (hf.pow 2).integrable_of_hasCompactSupport hc

/-- `|R(y)| ≤ ‖f‖²`. -/
theorem abs_autocorr_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (y : ℝ) :
    |autocorr φ a x y| ≤ ∫ u, bumpSum φ a x u ^ 2 := by
  have hf := (contDiff_bumpSum hφ a x).continuous
  have hsq := integrable_bumpSum_sq hφ hφs a x
  have h := GaloisForLFunctions.HTGeometry.abs_integral_mul_le_sqrt (μ := volume)
    (f := bumpSum φ a x) (g := fun u => bumpSum φ a x (u - y)) hf.aestronglyMeasurable
    (hf.comp (continuous_id.sub continuous_const)).aestronglyMeasurable hsq (hsq.comp_sub_right y)
  have htr : ∫ u, bumpSum φ a x (u - y) ^ (2 : ℕ) = ∫ u, bumpSum φ a x u ^ (2 : ℕ) :=
    integral_sub_right_eq_self (fun u => bumpSum φ a x u ^ (2 : ℕ)) y
  rw [htr, Real.sqrt_mul_self (integral_nonneg fun u => sq_nonneg _)] at h
  exact h

/-- The difference of two translates of a configuration is the configuration of the bump
difference `φ − φ(· − h)`. -/
theorem bumpSum_sub_translate (φ : ℝ → ℝ) (a x : Fin N → ℝ) (h v : ℝ) :
    bumpSum φ a x v - bumpSum φ a x (v - h) = bumpSum (fun u => φ u - φ (u - h)) a x v := by
  unfold bumpSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show v - h - x j = v - x j - h by ring]
  ring

/-- **Lipschitz bound for the autocorrelation.** -/
theorem abs_autocorr_sub_le {φ : ℝ → ℝ} {δ s κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 3 * δ < s) (hκ : 0 ≤ κ)
    (hreg : ∀ h, |h| ≤ δ → ∫ u, (φ u - φ (u - h)) ^ 2 ≤ (κ * h / δ) ^ 2 * ∫ u, φ u ^ 2)
    {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) {y y' : ℝ}
    (hyy : |y - y'| ≤ δ) :
    |autocorr φ a x y - autocorr φ a x y'| ≤ κ / δ * |y - y'| * ∫ u, bumpSum φ a x u ^ 2 := by
  set f := bumpSum φ a x with hfdef
  set h := y' - y with hh
  have hf := (contDiff_bumpSum hφ a x).continuous
  have hsq := integrable_bumpSum_sq hφ hφs a x
  have hcont_tr : ∀ c : ℝ, Continuous fun u => f (u - c) :=
    fun c => hf.comp (continuous_id.sub continuous_const)
  -- the bump difference
  set φh : ℝ → ℝ := fun u => φ u - φ (u - h) with hφh
  have hhδ : |h| ≤ δ := by rw [hh, abs_sub_comm]; exact hyy
  have hφh_cd : ContDiff ℝ 2 φh := hφ.sub (hφ.comp (contDiff_id.sub contDiff_const))
  have hφh_s : ∀ u, 3 * δ / 2 < |u| → φh u = 0 := by
    intro u hu
    have h1 : φ u = 0 := hφs u (by linarith)
    have h2 : φ (u - h) = 0 := hφs _ (by
      have := abs_sub_abs_le_abs_sub u h
      linarith)
    simp only [hφh, h1, h2, sub_zero]
  have hdiff_sq : ∫ v, (f v - f (v - h)) ^ (2 : ℕ) ≤ (κ * h / δ) ^ 2 * ∫ u, f u ^ 2 := by
    have e : (fun v => (f v - f (v - h)) ^ (2 : ℕ)) = fun v => bumpSum φh a x v ^ 2 := by
      funext v; rw [hfdef, bumpSum_sub_translate]
    rw [e, integral_bumpSum_sq hφh_cd hφh_s hδs hsep,
      integral_bumpSum_sq hφ hφs (by linarith) hsep]
    have hA : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    calc (∑ j, a j ^ 2) * ∫ u, φh u ^ 2 ≤ (∑ j, a j ^ 2) * ((κ * h / δ) ^ 2 * ∫ u, φ u ^ 2) :=
          mul_le_mul_of_nonneg_left (hreg h hhδ) hA
      _ = (κ * h / δ) ^ 2 * ((∑ j, a j ^ 2) * ∫ u, φ u ^ 2) := by ring
  -- the difference of autocorrelations as one integral
  have hint1 : Integrable fun u => f u * f (u - y) :=
    (hf.mul (hcont_tr y)).integrable_of_hasCompactSupport
      ((hasCompactSupport_bumpSum hφs a x).mul_right)
  have hint2 : Integrable fun u => f u * f (u - y') :=
    (hf.mul (hcont_tr y')).integrable_of_hasCompactSupport
      ((hasCompactSupport_bumpSum hφs a x).mul_right)
  have e1 : autocorr φ a x y - autocorr φ a x y' =
      ∫ v, f (v + y) * (f v - f (v - h)) := by
    unfold autocorr
    rw [← integral_sub hint1 hint2]
    have := integral_add_right_eq_self (μ := volume)
      (fun u => f u * f (u - y) - f u * f (u - y')) y
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [show v + y - y = v by ring, show v + y - y' = v - h by rw [hh]; ring]
    ring
  rw [e1]
  have hsq_tr : Integrable fun v => f (v + y) ^ (2 : ℕ) := by
    have := hsq.comp_sub_right (-y)
    simpa [sub_neg_eq_add] using this
  have hdiff_int : Integrable fun v => (f v - f (v - h)) ^ (2 : ℕ) := by
    have e : (fun v => (f v - f (v - h)) ^ (2 : ℕ)) = fun v => bumpSum φh a x v ^ (2 : ℕ) := by
      funext v; rw [hfdef, bumpSum_sub_translate]
    rw [e]
    exact integrable_bumpSum_sq hφh_cd hφh_s a x
  have hCS := GaloisForLFunctions.HTGeometry.abs_integral_mul_le_sqrt (μ := volume)
    (f := fun v => f (v + y)) (g := fun v => f v - f (v - h))
    (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    (hf.sub (hcont_tr h)).aestronglyMeasurable hsq_tr hdiff_int
  have htr : ∫ v, f (v + y) ^ (2 : ℕ) = ∫ v, f v ^ (2 : ℕ) :=
    integral_add_right_eq_self (fun v => f v ^ (2 : ℕ)) y
  rw [htr] at hCS
  have hE : 0 ≤ ∫ v, f v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hbound : (∫ v, f v ^ (2 : ℕ)) * ∫ v, (f v - f (v - h)) ^ (2 : ℕ) ≤
      (κ / δ * |y - y'| * ∫ u, f u ^ 2) ^ 2 := by
    have habs : |h| = |y - y'| := by rw [hh, abs_sub_comm]
    calc (∫ v, f v ^ (2 : ℕ)) * ∫ v, (f v - f (v - h)) ^ (2 : ℕ)
        ≤ (∫ v, f v ^ (2 : ℕ)) * ((κ * h / δ) ^ 2 * ∫ u, f u ^ 2) :=
          mul_le_mul_of_nonneg_left hdiff_sq hE
      _ = (κ / δ * |h| * ∫ u, f u ^ 2) ^ 2 := by
          rw [show (κ * h / δ) ^ 2 = (κ / δ * |h|) ^ 2 by rw [mul_pow, sq_abs]; ring]
          ring
      _ = (κ / δ * |y - y'| * ∫ u, f u ^ 2) ^ 2 := by rw [habs]
  have hnn : 0 ≤ κ / δ * |y - y'| * ∫ u, f u ^ 2 := by positivity
  calc |∫ v, f (v + y) * (f v - f (v - h))|
      ≤ Real.sqrt ((∫ v, f v ^ (2 : ℕ)) * ∫ v, (f v - f (v - h)) ^ (2 : ℕ)) := hCS
    _ ≤ Real.sqrt ((κ / δ * |y - y'| * ∫ u, f u ^ 2) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = κ / δ * |y - y'| * ∫ u, f u ^ 2 := Real.sqrt_sq hnn

/-! ## Regularity of the autocorrelation -/

theorem autocorr_eq_re_weilTest (φ : ℝ → ℝ) (a x : Fin N → ℝ) (y : ℝ) :
    autocorr φ a x y =
      (EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ)) y).re := by
  rw [weilTest_ofReal_apply, integral_complex_ofReal, Complex.ofReal_re]
  rfl

theorem continuous_autocorr {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) : Continuous (autocorr φ a x) := by
  have hF : ContDiff ℝ 2 fun u => (bumpSum φ a x u : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_bumpSum hφ a x)
  have hFc : HasCompactSupport fun u => (bumpSum φ a x u : ℂ) :=
    (hasCompactSupport_bumpSum hφs a x).comp_left Complex.ofReal_zero
  have hW := (EF.weilTest_contDiff hF hF.continuous hFc).continuous
  have e : autocorr φ a x = fun y =>
      (EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ)) y).re :=
    funext fun y => autocorr_eq_re_weilTest φ a x y
  rw [e]
  exact Complex.continuous_re.comp hW

theorem hasCompactSupport_autocorr {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (a x : Fin N → ℝ) : HasCompactSupport (autocorr φ a x) := by
  have hFc : HasCompactSupport fun u => (bumpSum φ a x u : ℂ) :=
    (hasCompactSupport_bumpSum hφs a x).comp_left Complex.ofReal_zero
  have hW := EF.weilTest_hasCompactSupport hFc hFc
  have e : autocorr φ a x = Complex.re ∘ (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
      (fun u => (bumpSum φ a x u : ℂ))) :=
    funext fun y => autocorr_eq_re_weilTest φ a x y
  rw [e]
  exact hW.comp_left Complex.zero_re

/-! ## The pole as an exponential moment of the autocorrelation -/

/-- **The pole is the exponential moment of the autocorrelation.** -/
theorem integral_autocorr_mul_exp {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) :
    ∫ y, autocorr φ a x y * Real.exp (y / 2) =
      (∫ u, bumpSum φ a x u * Real.exp (u / 2)) * ∫ u, bumpSum φ a x u * Real.exp (-u / 2) := by
  set f := bumpSum φ a x with hfdef
  set A : ℝ := (∑ j, |x j|) + δ / 2 with hA
  have hf : Continuous f := (contDiff_bumpSum hφ a x).continuous
  have hfz : ∀ u, A < |u| → f u = 0 := fun u hu => bumpSum_eq_zero hφs a x hu
  set F : ℝ → ℝ → ℝ := fun y u => f u * f (u - y) * Real.exp (y / 2) with hFdef
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hFdef, Function.uncurry]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro ((isCompact_Icc (a := -(2 * A)) (b := 2 * A)).prod
      (isCompact_Icc (a := -A) (b := A))) fun p hp => ?_
    simp only [hFdef, Function.uncurry]
    by_cases h2 : A < |p.2|
    · rw [hfz _ h2]; ring
    · by_cases h1 : A < |p.2 - p.1|
      · rw [hfz _ h1]; ring
      · exfalso
        apply hp
        rw [not_lt, abs_le] at h1 h2
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hinner : ∀ u, ∫ y, F y u = f u * Real.exp (u / 2) * ∫ v, f v * Real.exp (-v / 2) := by
    intro u
    have h := integral_sub_left_eq_self (fun v => f u * f v * Real.exp ((u - v) / 2)) volume u
    simp only [sub_sub_cancel] at h
    rw [show (fun y => F y u) = fun y => f u * f (u - y) * Real.exp (y / 2) from rfl, h,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [show (u - v) / 2 = u / 2 + -v / 2 by ring, Real.exp_add]
    ring
  calc ∫ y, autocorr φ a x y * Real.exp (y / 2)
      = ∫ y, ∫ u, F y u := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [autocorr, hFdef]
        rw [← integral_mul_const]
    _ = ∫ u, ∫ y, F y u := integral_integral_swap hFi
    _ = ∫ u, f u * Real.exp (u / 2) * ∫ v, f v * Real.exp (-v / 2) :=
        integral_congr_ae (Eventually.of_forall hinner)
    _ = (∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
        rw [integral_mul_const]

/-! ## The near part -/

theorem intervalIntegral_window_le {Y d δ : ℝ} (hY : 0 ≤ Y) (hδ : 0 < δ) :
    ∫ y in -Y..Y, (if |y - d| ≤ δ then (1 : ℝ) else 0) ≤
      2 * δ * (if |d| ≤ Y + δ then 1 else 0) := by
  have heq : (fun y => if |y - d| ≤ δ then (1 : ℝ) else 0) =
      (Icc (d - δ) (d + δ)).indicator 1 := by
    funext y
    simp only [Set.indicator, Set.mem_Icc, Pi.one_apply, abs_le]
    congr 1
    exact propext ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
      fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  split_ifs with hd
  · rw [mul_one, heq, intervalIntegral.integral_of_le (by linarith)]
    have hint : Integrable ((Icc (d - δ) (d + δ)).indicator (1 : ℝ → ℝ)) :=
      (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const)
    calc ∫ y in Ioc (-Y) Y, (Icc (d - δ) (d + δ)).indicator 1 y
        ≤ ∫ y, (Icc (d - δ) (d + δ)).indicator (1 : ℝ → ℝ) y :=
          setIntegral_le_integral hint (Eventually.of_forall fun y => by
            simp only [Set.indicator]; split_ifs <;> norm_num)
      _ = 2 * δ := by
          rw [integral_indicator_one measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith)]
          ring
  · rw [mul_zero]
    have hz : ∀ y ∈ Set.uIcc (-Y) Y, (if |y - d| ≤ δ then (1 : ℝ) else 0) = 0 := by
      intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      rw [if_neg]
      intro h
      apply hd
      have h1 : |y| ≤ Y := abs_le.mpr ⟨hy.1, hy.2⟩
      have h2 := abs_sub_abs_le_abs_sub d y
      rw [abs_sub_comm] at h
      linarith
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]

theorem window_eq_indicator (d δ : ℝ) :
    (fun y => if |y - d| ≤ δ then (1 : ℝ) else 0) = (Icc (d - δ) (d + δ)).indicator 1 := by
  funext y
  simp only [Set.indicator, Set.mem_Icc, Pi.one_apply, abs_le]
  congr 1
  exact propext ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

theorem intervalIntegrable_window (d δ a b : ℝ) :
    IntervalIntegrable (fun y => if |y - d| ≤ δ then (1 : ℝ) else 0) volume a b := by
  rw [window_eq_indicator]
  exact ((integrable_indicator_iff measurableSet_Icc).mpr integrableOn_const).intervalIntegrable

/-- The number of centres within `M` of a given one is at most `2 + 2M/s`. -/
theorem card_near_le {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) {x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) (i : Fin N) :
    ((Finset.univ.filter fun j => |x i - x j| ≤ M).card : ℝ) ≤ 2 + 2 * M / s := by
  have h := card_le_one_add_div_of_separated (Finset.univ.filter fun j => |x i - x j| ≤ M) x
    hs (by positivity : (0 : ℝ) ≤ 2 * M + s) (fun j _ k _ hjk => hsep j k hjk)
    fun j hj k hk _ => by
      rw [Finset.mem_filter] at hj hk
      have := abs_sub_le (x j) (x i) (x k)
      rw [abs_sub_comm (x j) (x i)] at this
      linarith [hj.2, hk.2]
  calc ((Finset.univ.filter fun j => |x i - x j| ≤ M).card : ℝ) ≤ 1 + (2 * M + s) / s := h
    _ = 2 + 2 * M / s := by field_simp; ring

/-- **The near part of the pole.** -/
theorem abs_integral_near_le {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : δ < s) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) {Y : ℝ} (hY : 0 ≤ Y) :
    |∫ y in -Y..Y, autocorr φ a x y * Real.exp (y / 2)| ≤
      2 * δ * Real.exp (Y / 2) * (2 + 2 * (Y + δ) / s) * ∫ u, bumpSum φ a x u ^ 2 := by
  have hs : 0 < s := hδ.trans hδs
  set W : ℝ := ∫ u, φ u ^ 2 with hW
  have hW0 : 0 ≤ W := integral_nonneg fun u => sq_nonneg _
  set ind : Fin N → Fin N → ℝ → ℝ :=
    fun i j y => if |y - (x i - x j)| ≤ δ then (1 : ℝ) else 0 with hind
  set B : ℝ → ℝ := fun y => Real.exp (Y / 2) * (W * ∑ i, ∑ j, |a i| * |a j| * ind i j y) with hB
  have hYY : -Y ≤ Y := by linarith
  have hcont : Continuous fun y => autocorr φ a x y * Real.exp (y / 2) :=
    (continuous_autocorr hφ hφs a x).mul (by fun_prop)
  have hBint : IntervalIntegrable B volume (-Y) Y := by
    refine (IntervalIntegrable.const_mul ?_ _)
    refine (IntervalIntegrable.const_mul ?_ _)
    refine IntervalIntegrable.sum (Finset.univ) fun i _ => ?_
    refine IntervalIntegrable.sum (Finset.univ) fun j _ => ?_
    exact (intervalIntegrable_window _ δ _ _).const_mul _
  have hpt : ∀ y ∈ Icc (-Y) Y, |autocorr φ a x y * Real.exp (y / 2)| ≤ B y := by
    intro y hy
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := abs_integral_bumpSum_mul_bumpSum_sub_le hφ hφs a x y
    have h2 : Real.exp (y / 2) ≤ Real.exp (Y / 2) := Real.exp_le_exp.mpr (by linarith [hy.2])
    have h0 : 0 ≤ W * ∑ i, ∑ j, |a i| * |a j| * ind i j y := by
      refine mul_nonneg hW0 (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
      refine mul_nonneg (by positivity) ?_
      simp only [hind]; split_ifs <;> norm_num
    calc |autocorr φ a x y| * Real.exp (y / 2)
        ≤ (W * ∑ i, ∑ j, |a i| * |a j| * ind i j y) * Real.exp (Y / 2) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le h0
      _ = B y := by simp only [hB]; ring
  -- integrate the majorant
  have hBval : ∫ y in -Y..Y, B y = Real.exp (Y / 2) * (W * ∑ i, ∑ j, |a i| * |a j| *
      ∫ y in -Y..Y, ind i j y) := by
    simp only [hB]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ => IntervalIntegrable.sum _ fun j _ =>
        (intervalIntegrable_window _ δ _ _).const_mul _]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (intervalIntegrable_window _ δ _ _).const_mul _]
    exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
  -- the Schur bound
  set K : Fin N → Fin N → ℝ := fun i j => if |x i - x j| ≤ Y + δ then 1 else 0 with hK
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => by simp only [hK]; split_ifs <;> norm_num
  have hKs : ∀ i j, K i j = K j i := fun i j => by simp only [hK]; rw [abs_sub_comm]
  have hKrow : ∀ i, ∑ j, K i j ≤ 2 + 2 * (Y + δ) / s := fun i => by
    have := card_near_le hs (by linarith : 0 ≤ Y + δ) hsep i
    simp only [hK]
    rw [Finset.sum_boole]
    exact this
  have hschur := sum_abs_mul_le_of_rowSum hK0 hKs hKrow a
  have hwin : ∀ i j, ∫ y in -Y..Y, ind i j y ≤ 2 * δ * K i j := fun i j =>
    intervalIntegral_window_le hY hδ
  have hsum : ∑ i, ∑ j, |a i| * |a j| * ∫ y in -Y..Y, ind i j y ≤
      2 * δ * ((2 + 2 * (Y + δ) / s) * ∑ i, a i ^ 2) := by
    calc ∑ i, ∑ j, |a i| * |a j| * ∫ y in -Y..Y, ind i j y
        ≤ ∑ i, ∑ j, |a i| * |a j| * (2 * δ * K i j) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hwin i j) (by positivity)
      _ = 2 * δ * ∑ i, ∑ j, |a i| * |a j| * K i j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 2 * δ * ((2 + 2 * (Y + δ) / s) * ∑ i, a i ^ 2) :=
          mul_le_mul_of_nonneg_left hschur (by positivity)
  have hE : ∫ u, bumpSum φ a x u ^ 2 = (∑ j, a j ^ 2) * W := integral_bumpSum_sq hφ hφs hδs hsep
  calc |∫ y in -Y..Y, autocorr φ a x y * Real.exp (y / 2)|
      ≤ ∫ y in -Y..Y, |autocorr φ a x y * Real.exp (y / 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hYY
    _ ≤ ∫ y in -Y..Y, B y :=
        intervalIntegral.integral_mono_on hYY (hcont.abs.intervalIntegrable _ _) hBint hpt
    _ = Real.exp (Y / 2) * (W * ∑ i, ∑ j, |a i| * |a j| * ∫ y in -Y..Y, ind i j y) := hBval
    _ ≤ Real.exp (Y / 2) * (W * (2 * δ * ((2 + 2 * (Y + δ) / s) * ∑ i, a i ^ 2))) := by
        gcongr
    _ = 2 * δ * Real.exp (Y / 2) * (2 + 2 * (Y + δ) / s) * ∫ u, bumpSum φ a x u ^ 2 := by
        rw [hE]; ring

/-- **The left tail of the pole.** -/
theorem abs_integral_left_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) {Y T : ℝ} (hYT : Y ≤ T) :
    |∫ y in -T..-Y, autocorr φ a x y * Real.exp (y / 2)| ≤
      2 * Real.exp (-Y / 2) * ∫ u, bumpSum φ a x u ^ 2 := by
  set E : ℝ := ∫ u, bumpSum φ a x u ^ 2 with hE
  have hE0 : 0 ≤ E := integral_nonneg fun u => sq_nonneg _
  have hTY : -T ≤ -Y := by linarith
  have hcont : Continuous fun y => autocorr φ a x y * Real.exp (y / 2) :=
    (continuous_autocorr hφ hφs a x).mul (by fun_prop)
  have hpt : ∀ y ∈ Icc (-T) (-Y), |autocorr φ a x y * Real.exp (y / 2)| ≤
      E * Real.exp (y / 2) := fun y _ => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_autocorr_le hφ hφs a x y) (Real.exp_pos _).le
  have hexp : ∫ y in -T..-Y, Real.exp (y / 2) = 2 * (Real.exp (-Y / 2) - Real.exp (-T / 2)) := by
    have := intervalIntegral.integral_comp_div (a := -T) (b := -Y) Real.exp
      (by norm_num : (2 : ℝ) ≠ 0)
    rw [this, integral_exp, smul_eq_mul]
    ring_nf
  calc |∫ y in -T..-Y, autocorr φ a x y * Real.exp (y / 2)|
      ≤ ∫ y in -T..-Y, |autocorr φ a x y * Real.exp (y / 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hTY
    _ ≤ ∫ y in -T..-Y, E * Real.exp (y / 2) :=
        intervalIntegral.integral_mono_on hTY (hcont.abs.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun y : ℝ => E * Real.exp (y / 2)).intervalIntegrable _ _) hpt
    _ = E * (2 * (Real.exp (-Y / 2) - Real.exp (-T / 2))) := by
        rw [intervalIntegral.integral_const_mul, hexp]
    _ ≤ 2 * Real.exp (-Y / 2) * E := by
        have := Real.exp_pos (-T / 2)
        nlinarith

/-! ## One test: the Lévy gain against the signed pole -/

/-- **Signed Lévy bound.**  `W_∞(f ⋆ f̃) ≥ (A(0) + e^{−s/2} log((s−δ)/δ))‖f‖² + 2∫R(y)e^{y/2}dy`. -/
theorem le_weilArchRe_add_pole {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 2 * δ < s) {a x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    (EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ)) *
        (∫ u, bumpSum φ a x u ^ 2) + 2 * ∫ y, autocorr φ a x y * Real.exp (y / 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  rw [weilArchRe_eq_levy_pole (contDiff_bumpSum hφ a x) (hasCompactSupport_bumpSum hφs a x),
    integral_prod_cosh_eq (hasCompactSupport_bumpSum hφs a x)
      (contDiff_bumpSum hφ a x).continuous, ← integral_autocorr_mul_exp hφ hφs a x]
  have hlev := levy_ge (a := a) hφ hφs hδ hδs hsep
  have hint := integral_archLevyDensity_ge hδ hδs
  have hE : 0 ≤ ∫ u, bumpSum φ a x u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h1 : Real.exp (-s / 2) * Real.log ((s - δ) / δ) * ∫ u, bumpSum φ a x u ^ 2 ≤
      2 * (∫ u, bumpSum φ a x u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t := by
    have := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ 2 * ∫ u, bumpSum φ a x u ^ 2)
    nlinarith
  nlinarith

/-! ## The cone -/

section Cone

variable {K : ℕ} {M : Fin K → ℕ}

/-- A nonnegative combination of autocorrelations of configurations. -/
def coneAutocorr (φ : ℝ → ℝ) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ) (y : ℝ) : ℝ :=
  ∑ k, c k * autocorr φ (a k) (x k) y

/-- The total mass `Σ c_k ‖f_k‖²`. -/
def coneMass (φ : ℝ → ℝ) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ) : ℝ :=
  ∑ k, c k * ∫ u, bumpSum φ (a k) (x k) u ^ 2

theorem integral_eq_intervalIntegral_of_vanish {h : ℝ → ℝ} {R T₁ T₂ : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < |y| → h y = 0) (hT₁ : R < T₁) (hT₂ : R < T₂) :
    ∫ y, h y = ∫ y in -T₁..T₂, h y := by
  rw [intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro y hy
  refine hR y ?_
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
  rcases hy with h1 | h1
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

end Cone

end RHTower.SeparatedBump

end
