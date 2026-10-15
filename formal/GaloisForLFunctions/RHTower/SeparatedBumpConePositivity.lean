import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity
import GaloisForLFunctions.HTGeometry.LogNodeExponentialTail
import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination

/-!
# Prime-blind positivity on the cone of separated narrow bumps

For a configuration `f = Σ_j a_j φ(· − x_j)` (`bumpSum`) write `R(y) = ∫ f(u) f(u − y) du`
(`autocorr`).

**Theorem** (`exists_cone_primeBlind_nonneg`).  For every separation `s > 0` and regularity
`κ ≥ 0` there is `δ₀ > 0` such that for `0 < δ < δ₀` the following holds.  Let `φ` be a `C²` bump
supported in `[−δ/2, δ/2]` with `‖φ − φ(· − h)‖² ≤ (κ h/δ)² ‖φ‖²` for `|h| ≤ δ`, and let
`g = Σ_k c_k R_k` (`c_k ≥ 0`) be a combination of autocorrelations of configurations with
`s`-separated centres and arbitrary amplitudes, vanishing at every `log n`, `n ≥ 2`.  The blindness
is only required for the combination, so cancellation across the tests is allowed.  Then
`Σ_k c_k W_∞(f_k ⋆ f̃_k) ≥ 0`.

Proof.
* *Lévy gain against the signed pole* (`le_weilArchRe_add_pole`):
  `W_∞(f ⋆ f̃) ≥ (A(0) + e^{−s/2} log((s−δ)/δ))‖f‖² + 2∫ R(y) e^{y/2} dy`, the pole being the
  exponential moment of the autocorrelation (`integral_autocorr_mul_exp`).
* *Near lags* `|y| ≤ log N₀` (`abs_integral_near_le`): only pairs at distance `≤ log N₀ + δ`
  contribute, each on a window of length `2δ`, so the part is `≤ 2δ √N₀ (2 + 2(log N₀ + δ)/s)‖f‖²`.
  Left tail: `≤ 2‖f‖²/√N₀` (`abs_integral_left_le`).
* *Far lags* `y ≥ log N₀`: `g` vanishes at every `log n` and is `(κ/δ)Σc_k‖f_k‖²`-Lipschitz on
  scale `δ` (`abs_coneAutocorr_sub_le`), so the exponential tail is
  `≤ √2 (κ/δ) Σc_k‖f_k‖² / √(N₀ − 1)`
  (`GaloisForLFunctions.HTGeometry.abs_intervalIntegral_mul_exp_half_le`).
* With `N₀ ≈ (η/δ)²`, `η = s e^{−s/2}/64`, every loss is `≤ (3/8) e^{−s/2} log(1/δ) + O_{s,κ}(1)`
  while the Lévy gain is `e^{−s/2} log(1/δ) + O_s(1)` (`cone_coefficient_nonneg`).
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
    simp only [hFdef]
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
      (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
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
  exact ((integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const measure_Icc_lt_top.ne)).intervalIntegrable

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
  have hind_int : ∀ i j, Integrable (ind i j) := fun i j => by
    simp only [hind]
    rw [window_eq_indicator]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const measure_Icc_lt_top.ne)
  have hrow_int : ∀ i, Integrable fun y => ∑ j, |a i| * |a j| * ind i j y := fun i =>
    integrable_finsetSum _ fun j _ => (hind_int i j).const_mul _
  have hsum_int : Integrable fun y => ∑ i, ∑ j, |a i| * |a j| * ind i j y :=
    integrable_finsetSum _ fun i _ => hrow_int i
  have hBint : IntervalIntegrable B volume (-Y) Y :=
    ((hsum_int.const_mul W).const_mul (Real.exp (Y / 2))).intervalIntegrable
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
    have hs1 : ∫ y in -Y..Y, ∑ i, ∑ j, |a i| * |a j| * ind i j y =
        ∑ i, ∫ y in -Y..Y, ∑ j, |a i| * |a j| * ind i j y :=
      intervalIntegral.integral_finsetSum fun i _ => (hrow_int i).intervalIntegrable
    have hs2 : ∀ i, ∫ y in -Y..Y, ∑ j, |a i| * |a j| * ind i j y =
        ∑ j, |a i| * |a j| * ∫ y in -Y..Y, ind i j y := fun i => by
      rw [intervalIntegral.integral_finsetSum fun j _ =>
        ((hind_int i j).const_mul _).intervalIntegrable]
      exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    simp only [hB]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hs1]
    congr 2
    exact Finset.sum_congr rfl fun i _ => hs2 i
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

theorem continuous_coneAutocorr {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ) :
    Continuous (coneAutocorr φ c a x) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_autocorr hφ hφs _ _)

theorem exists_coneAutocorr_vanish {φ : ℝ → ℝ} {δ : ℝ} (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < |y| → coneAutocorr φ c a x y = 0 := by
  have h := fun k => (hasCompactSupport_autocorr hφs (a k) (x k)).exists_pos_le_norm
  choose R hR0 hR using h
  refine ⟨∑ k, R k, Finset.sum_nonneg fun k _ => (hR0 k).le, fun y hy => ?_⟩
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : R k ≤ ∑ k, R k :=
    Finset.single_le_sum (f := R) (fun k _ => (hR0 k).le) (Finset.mem_univ k)
  rw [hR k y (by rw [Real.norm_eq_abs]; linarith), mul_zero]

theorem integrable_autocorr_mul_exp {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) {N : ℕ} (a x : Fin N → ℝ) :
    Integrable fun y => autocorr φ a x y * Real.exp (y / 2) :=
  ((continuous_autocorr hφ hφs a x).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_autocorr hφs a x).mul_right

/-- The pole of the combination is the combination of the poles. -/
theorem integral_coneAutocorr_mul_exp {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ) :
    ∫ y, coneAutocorr φ c a x y * Real.exp (y / 2) =
      ∑ k, c k * ∫ y, autocorr φ (a k) (x k) y * Real.exp (y / 2) := by
  have e : (fun y => coneAutocorr φ c a x y * Real.exp (y / 2)) =
      fun y => ∑ k, c k * (autocorr φ (a k) (x k) y * Real.exp (y / 2)) := by
    funext y; simp only [coneAutocorr, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, integral_finsetSum _ fun k _ => (integrable_autocorr_mul_exp hφ hφs _ _).const_mul _]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

theorem intervalIntegral_coneAutocorr_mul_exp {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ)
    (α β : ℝ) :
    ∫ y in α..β, coneAutocorr φ c a x y * Real.exp (y / 2) =
      ∑ k, c k * ∫ y in α..β, autocorr φ (a k) (x k) y * Real.exp (y / 2) := by
  have e : (fun y => coneAutocorr φ c a x y * Real.exp (y / 2)) =
      fun y => ∑ k, c k * (autocorr φ (a k) (x k) y * Real.exp (y / 2)) := by
    funext y; simp only [coneAutocorr, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, intervalIntegral.integral_finsetSum fun k _ =>
    ((integrable_autocorr_mul_exp hφ hφs _ _).const_mul _).intervalIntegrable]
  exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _

theorem abs_sum_mul_le {c v w : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) (hvw : ∀ k, |v k| ≤ w k) :
    |∑ k, c k * v k| ≤ ∑ k, c k * w k :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
    rw [abs_mul, abs_of_nonneg (hc k)]
    exact mul_le_mul_of_nonneg_left (hvw k) (hc k))

/-- **Lipschitz bound for the combination.** -/
theorem abs_coneAutocorr_sub_le {φ : ℝ → ℝ} {δ s κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 3 * δ < s) (hκ : 0 ≤ κ)
    (hreg : ∀ h, |h| ≤ δ → ∫ u, (φ u - φ (u - h)) ^ 2 ≤ (κ * h / δ) ^ 2 * ∫ u, φ u ^ 2)
    {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) {a x : (k : Fin K) → Fin (M k) → ℝ}
    (hsep : ∀ k i j, i ≠ j → s ≤ |x k i - x k j|) {y y' : ℝ} (hyy : |y - y'| ≤ δ) :
    |coneAutocorr φ c a x y - coneAutocorr φ c a x y'| ≤
      κ / δ * |y - y'| * coneMass φ c a x := by
  have e : coneAutocorr φ c a x y - coneAutocorr φ c a x y' =
      ∑ k, c k * (autocorr φ (a k) (x k) y - autocorr φ (a k) (x k) y') := by
    simp only [coneAutocorr, ← Finset.sum_sub_distrib, mul_sub]
  rw [e]
  calc |∑ k, c k * (autocorr φ (a k) (x k) y - autocorr φ (a k) (x k) y')|
      ≤ ∑ k, c k * (κ / δ * |y - y'| * ∫ u, bumpSum φ (a k) (x k) u ^ 2) :=
        abs_sum_mul_le hc fun k => abs_autocorr_sub_le hφ hφs hδ hδs hκ hreg (hsep k) hyy
    _ = κ / δ * |y - y'| * coneMass φ c a x := by
        simp only [coneMass, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem log_succ_sub_log_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) / n by positivity)
  rw [show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at this
  exact this

/-- **The pole of a blind combination.** -/
theorem abs_integral_coneAutocorr_le {φ : ℝ → ℝ} {δ s κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδs : 3 * δ < s) (hκ : 0 ≤ κ)
    (hreg : ∀ h, |h| ≤ δ → ∫ u, (φ u - φ (u - h)) ^ 2 ≤ (κ * h / δ) ^ 2 * ∫ u, φ u ^ 2)
    {c : Fin K → ℝ} (hc : ∀ k, 0 ≤ c k) {a x : (k : Fin K) → Fin (M k) → ℝ}
    (hsep : ∀ k i j, i ≠ j → s ≤ |x k i - x k j|) {N₀ : ℕ} (hN₀ : 2 ≤ N₀)
    (hN₀δ : 1 / (N₀ : ℝ) ≤ δ)
    (hblind : ∀ n : ℕ, 2 ≤ n → coneAutocorr φ c a x (Real.log n) = 0) :
    |∫ y, coneAutocorr φ c a x y * Real.exp (y / 2)| ≤
      (2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s)) *
        coneMass φ c a x + Real.sqrt 2 * (κ / δ * coneMass φ c a x) / Real.sqrt ((N₀ : ℝ) - 1) := by
  set g := coneAutocorr φ c a x with hg
  set C₀ := coneMass φ c a x with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hc k) (integral_nonneg fun u => sq_nonneg _)
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  set Y := Real.log N₀ with hY
  have hY0 : 0 ≤ Y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₀))
  have hgc : Continuous g := continuous_coneAutocorr hφ hφs c a x
  have hge : Continuous fun y => g y * Real.exp (y / 2) := hgc.mul (by fun_prop)
  obtain ⟨R, hR0, hR⟩ := exists_coneAutocorr_vanish hφs c a x
  set K₁ : ℕ := ⌈Real.exp (R + 1)⌉₊ with hK₁
  set T₂ : ℝ := Real.log ((N₀ + K₁ : ℕ) : ℝ) with hT₂
  set T₁ : ℝ := R + 1 + Y with hT₁
  have hT₂R : R < T₂ := by
    have h1 : Real.exp (R + 1) ≤ ((N₀ + K₁ : ℕ) : ℝ) := by
      calc Real.exp (R + 1) ≤ K₁ := Nat.le_ceil _
        _ ≤ ((N₀ + K₁ : ℕ) : ℝ) := by push_cast; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith
  have hT₂Y : Y ≤ T₂ :=
    Real.log_le_log hN0 (by push_cast; linarith [(Nat.cast_nonneg K₁ : (0 : ℝ) ≤ K₁)])
  have hfull : ∫ y, g y * Real.exp (y / 2) = ∫ y in -T₁..T₂, g y * Real.exp (y / 2) :=
    integral_eq_intervalIntegral_of_vanish hR0 (fun y hy => by
      show coneAutocorr φ c a x y * Real.exp (y / 2) = 0
      rw [hR y hy, zero_mul])
      (by linarith) hT₂R
  have hii : ∀ α β : ℝ, IntervalIntegrable (fun y => g y * Real.exp (y / 2)) volume α β :=
    fun α β => hge.intervalIntegrable α β
  have hsplit : ∫ y in -T₁..T₂, g y * Real.exp (y / 2) =
      (∫ y in -T₁..-Y, g y * Real.exp (y / 2)) + (∫ y in -Y..Y, g y * Real.exp (y / 2)) +
        ∫ y in Y..T₂, g y * Real.exp (y / 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  -- the left tail
  have hexpm : Real.exp (-Y / 2) = 1 / Real.sqrt N₀ := by
    rw [show -Y / 2 = -(Y / 2) by ring, Real.exp_neg, Real.exp_half, hY, Real.exp_log hN0,
      one_div]
  have hexpp : Real.exp (Y / 2) = Real.sqrt N₀ := by
    rw [Real.exp_half, hY, Real.exp_log hN0]
  have hleft : |∫ y in -T₁..-Y, g y * Real.exp (y / 2)| ≤ 2 / Real.sqrt N₀ * C₀ := by
    rw [hg, intervalIntegral_coneAutocorr_mul_exp hφ hφs]
    calc |∑ k, c k * ∫ y in -T₁..-Y, autocorr φ (a k) (x k) y * Real.exp (y / 2)|
        ≤ ∑ k, c k * (2 * Real.exp (-Y / 2) * ∫ u, bumpSum φ (a k) (x k) u ^ 2) :=
          abs_sum_mul_le hc fun k => abs_integral_left_le hφ hφs _ _ (by linarith)
      _ = 2 / Real.sqrt N₀ * C₀ := by
          rw [hexpm, hC₀]; simp only [coneMass, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hnear : |∫ y in -Y..Y, g y * Real.exp (y / 2)| ≤
      2 * δ * Real.sqrt N₀ * (2 + 2 * (Y + δ) / s) * C₀ := by
    rw [hg, intervalIntegral_coneAutocorr_mul_exp hφ hφs]
    calc |∑ k, c k * ∫ y in -Y..Y, autocorr φ (a k) (x k) y * Real.exp (y / 2)|
        ≤ ∑ k, c k * (2 * δ * Real.exp (Y / 2) * (2 + 2 * (Y + δ) / s) *
            ∫ u, bumpSum φ (a k) (x k) u ^ 2) :=
          abs_sum_mul_le hc fun k => abs_integral_near_le hφ hφs hδ (by linarith) (hsep k) hY0
      _ = 2 * δ * Real.sqrt N₀ * (2 + 2 * (Y + δ) / s) * C₀ := by
          rw [hexpp, hC₀]; simp only [coneMass, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  -- the far part
  have hfar : |∫ y in Y..T₂, g y * Real.exp (y / 2)| ≤
      Real.sqrt 2 * (κ / δ * C₀) / Real.sqrt ((N₀ : ℝ) - 1) := by
    refine GaloisForLFunctions.HTGeometry.abs_intervalIntegral_mul_exp_half_le
      (by positivity) hgc hN₀ (fun n hn y hy => ?_) K₁
    have hn1 : 1 ≤ n := by omega
    have hz : g (Real.log n) = 0 := hblind n (by omega)
    have hyl : 0 ≤ y - Real.log n := by linarith [hy.1]
    have hyδ : |y - Real.log n| ≤ δ := by
      rw [abs_of_nonneg hyl]
      have h1 := log_succ_sub_log_le hn1
      have h2 : (1 : ℝ) / n ≤ 1 / N₀ := one_div_le_one_div_of_le hN0 (by exact_mod_cast hn)
      linarith [hy.2]
    have := abs_coneAutocorr_sub_le (a := a) hφ hφs hδ hδs hκ hreg hc hsep hyδ
    rw [show coneAutocorr φ c a x (Real.log n) = 0 from hz, sub_zero, abs_of_nonneg hyl] at this
    calc |g y| ≤ κ / δ * (y - Real.log n) * C₀ := this
      _ = κ / δ * C₀ * (y - Real.log n) := by ring
  rw [hfull, hsplit]
  calc |(∫ y in -T₁..-Y, g y * Real.exp (y / 2)) + (∫ y in -Y..Y, g y * Real.exp (y / 2)) +
        ∫ y in Y..T₂, g y * Real.exp (y / 2)|
      ≤ |∫ y in -T₁..-Y, g y * Real.exp (y / 2)| + |∫ y in -Y..Y, g y * Real.exp (y / 2)| +
        |∫ y in Y..T₂, g y * Real.exp (y / 2)| := abs_add_three _ _ _
    _ ≤ 2 / Real.sqrt N₀ * C₀ + 2 * δ * Real.sqrt N₀ * (2 + 2 * (Y + δ) / s) * C₀ +
        Real.sqrt 2 * (κ / δ * C₀) / Real.sqrt ((N₀ : ℝ) - 1) := by gcongr
    _ = (2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s)) * C₀ +
        Real.sqrt 2 * (κ / δ * C₀) / Real.sqrt ((N₀ : ℝ) - 1) := by rw [hY]; ring

/-- The constant of the cone margin. -/
def coneMarginConst (s κ : ℝ) : ℝ :=
  2 + 12 * (s * Real.exp (-s / 2) / 64) + 12 * (s * Real.exp (-s / 2) / 64) / s *
    (2 * Real.log 2 + 1) + 4 * κ / (s * Real.exp (-s / 2) / 64) - EF.gammaBracket 0 -
    Real.exp (-s / 2) * Real.log (s / 2)

/-- **The cone coefficient is nonnegative** for `N₀ ≈ (η/δ)²`, `η = s e^{−s/2}/64`. -/
theorem cone_coefficient_nonneg {s κ δ : ℝ} {N₀ : ℕ} (hs : 0 < s) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (hδη : δ ≤ s * Real.exp (-s / 2) / 64 / 2) (hδs : δ ≤ s / 2) (hδ1 : δ ≤ 1)
    (hN1 : (s * Real.exp (-s / 2) / 64 / δ) ^ 2 ≤ N₀)
    (hN2 : (N₀ : ℝ) ≤ (s * Real.exp (-s / 2) / 64 / δ) ^ 2 + 1)
    (hL : coneMarginConst s κ ≤ 5 / 8 * Real.exp (-s / 2) * Real.log (1 / δ)) :
    0 ≤ EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ) -
      2 * ((2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s)) +
        Real.sqrt 2 * (κ / δ) / Real.sqrt ((N₀ : ℝ) - 1)) := by
  set c₀ := Real.exp (-s / 2) with hc₀
  have hc₀0 : 0 < c₀ := Real.exp_pos _
  set η := s * c₀ / 64 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    have h := Real.add_one_le_exp (s / 2)
    have he : c₀ * Real.exp (s / 2) = 1 := by
      rw [hc₀, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]
    have h2 := mul_le_mul_of_nonneg_left h hc₀0.le
    have : s * c₀ ≤ 2 := by nlinarith
    rw [hη]; linarith
  set q := η / δ with hq
  have hqη : δ * q = η := by rw [hq]; field_simp
  have hq2 : 2 ≤ q := by rw [hq, le_div_iff₀ hδ]; linarith
  set L := Real.log (1 / δ) with hLdef
  have hq4 : (4 : ℝ) ≤ q ^ 2 := by nlinarith
  have hN0 : (0 : ℝ) < N₀ := by linarith
  -- square roots
  have hsq_ge : q ≤ Real.sqrt N₀ := by
    rw [show q = Real.sqrt (q ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hN1
  have hsq_le : Real.sqrt N₀ ≤ q + 1 := by
    rw [show q + 1 = Real.sqrt ((q + 1) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqm : q ≤ Real.sqrt 2 * Real.sqrt ((N₀ : ℝ) - 1) := by
    rw [← Real.sqrt_mul (by norm_num),
      show q = Real.sqrt (q ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hqpos : 0 < q := by linarith
  have hsqmpos : 0 < Real.sqrt ((N₀ : ℝ) - 1) := by
    have : 0 < Real.sqrt 2 * Real.sqrt ((N₀ : ℝ) - 1) := lt_of_lt_of_le hqpos hsqm
    exact pos_of_mul_pos_right this hs2pos.le
  -- the logarithm of N₀
  have hlogN : Real.log N₀ ≤ 2 * Real.log 2 + 2 * L := by
    have h1 : (N₀ : ℝ) ≤ (2 / δ) ^ 2 := by
      have hq1 : q ≤ 1 / δ := by rw [hq]; exact div_le_div_of_nonneg_right hη1 hδ.le
      have : (2 / δ) ^ 2 = 4 * (1 / δ) ^ 2 := by ring
      have hq1sq : q ^ 2 ≤ (1 / δ) ^ 2 := pow_le_pow_left₀ hqpos.le hq1 2
      nlinarith
    have h2 := Real.log_le_log hN0 h1
    rw [Real.log_pow, show (2 : ℝ) / δ = 2 * (1 / δ) by ring,
      Real.log_mul (by norm_num) (by positivity)] at h2
    push_cast at h2
    linarith
  have hlogN0 : 0 ≤ Real.log N₀ := Real.log_nonneg (by linarith)
  -- the three losses
  have hT1 : 2 / Real.sqrt N₀ ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le hqpos hsq_ge)]; linarith
  have hX : 2 + 2 * (Real.log N₀ + δ) / s ≤ 2 + 2 * (2 * Real.log 2 + 2 * L + 1) / s := by
    gcongr
  have hT2 : 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s) ≤
      3 * η * (2 + 2 * (2 * Real.log 2 + 2 * L + 1) / s) := by
    have h1 : 2 * δ * Real.sqrt N₀ ≤ 3 * η := by
      have := mul_le_mul_of_nonneg_left hsq_le hδ.le
      linarith
    have hX0 : 0 ≤ 2 + 2 * (Real.log N₀ + δ) / s := by positivity
    calc 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s)
        ≤ 3 * η * (2 + 2 * (Real.log N₀ + δ) / s) := mul_le_mul_of_nonneg_right h1 hX0
      _ ≤ 3 * η * (2 + 2 * (2 * Real.log 2 + 2 * L + 1) / s) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
  have hT3 : Real.sqrt 2 * (κ / δ) / Real.sqrt ((N₀ : ℝ) - 1) ≤ 2 * κ / η := by
    rw [div_le_div_iff₀ hsqmpos hη0]
    have h1 : Real.sqrt 2 * (κ / δ) * η = Real.sqrt 2 * κ * q := by
      rw [← hqη]; field_simp
    rw [h1]
    have h2 : Real.sqrt 2 * κ * q ≤ Real.sqrt 2 * κ * (Real.sqrt 2 * Real.sqrt ((N₀ : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hsqm (by positivity)
    have e : Real.sqrt 2 * κ * (Real.sqrt 2 * Real.sqrt ((N₀ : ℝ) - 1)) =
        2 * κ * Real.sqrt ((N₀ : ℝ) - 1) := by
      rw [show Real.sqrt 2 * κ * (Real.sqrt 2 * Real.sqrt ((N₀ : ℝ) - 1)) =
        (Real.sqrt 2 * Real.sqrt 2) * κ * Real.sqrt ((N₀ : ℝ) - 1) by ring, hs2]
    linarith
  -- the gain
  have hgain : Real.log (s / 2) + L ≤ Real.log ((s - δ) / δ) := by
    have h1 : s / 2 * (1 / δ) ≤ (s - δ) / δ := by
      rw [div_eq_mul_one_div (s - δ)]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (by positivity)] at h2
  have hgain' : c₀ * (Real.log (s / 2) + L) ≤ c₀ * Real.log ((s - δ) / δ) :=
    mul_le_mul_of_nonneg_left hgain hc₀0.le
  have hηs : 24 * η / s = 3 / 8 * c₀ := by rw [hη]; field_simp; ring
  have hkey : 3 * η * (2 + 2 * (2 * Real.log 2 + 2 * L + 1) / s) =
      6 * η + 6 * η / s * (2 * Real.log 2 + 1) + 12 * η / s * L := by
    field_simp; ring
  have hηs' : 12 * η / s * L = 3 / 16 * c₀ * L := by
    rw [show 12 * η / s = (24 * η / s) / 2 by ring, hηs]; ring
  unfold coneMarginConst at hL
  rw [← hc₀, ← hη] at hL
  have hκη : 4 * κ / η = 2 * (2 * κ / η) := by ring
  have hT2' : 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s) ≤
      6 * η + 6 * η / s * (2 * Real.log 2 + 1) + 3 / 16 * c₀ * L := by
    rw [← hηs', ← hkey]; exact hT2
  have hsum : 2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ * (2 + 2 * (Real.log N₀ + δ) / s) +
      Real.sqrt 2 * (κ / δ) / Real.sqrt ((N₀ : ℝ) - 1) ≤
      1 + (6 * η + 6 * η / s * (2 * Real.log 2 + 1) + 3 / 16 * c₀ * L) + 2 * κ / η :=
    add_le_add (add_le_add hT1 hT2') hT3
  have hg2 : c₀ * Real.log (s / 2) + c₀ * L ≤ c₀ * Real.log ((s - δ) / δ) := by
    rw [← mul_add]; exact hgain'
  have e1 : 12 * η / s * (2 * Real.log 2 + 1) = 2 * (6 * η / s * (2 * Real.log 2 + 1)) := by
    ring
  have e2 : 5 / 8 * c₀ * L = c₀ * L - 2 * (3 / 16 * c₀ * L) := by ring
  linarith [hsum, hg2, hL, e1, e2, hκη]

/-- **Prime-blind positivity on the cone of separated narrow bumps.**  For every separation
`s > 0` and regularity `κ ≥ 0` there is `δ₀ > 0` with the following property.  Let `0 < δ < δ₀`,
let `φ` be a `C²` bump supported in `[−δ/2, δ/2]` with `L²` modulus
`‖φ − φ(· − h)‖² ≤ (κ h/δ)² ‖φ‖²` for `|h| ≤ δ`, and let `f_k = Σ_j a_{kj} φ(· − x_{kj})` be any
finite family of configurations with `s`-separated centres and any amplitudes.  If the
combination `Σ_k c_k f_k ⋆ f̃_k` with `c_k ≥ 0` vanishes at every `log n`, `n ≥ 2` (cancellation
across the tests allowed), then `Σ_k c_k W_∞(f_k ⋆ f̃_k) ≥ 0`. -/
theorem exists_cone_primeBlind_nonneg {s κ : ℝ} (hs : 0 < s) (hκ : 0 ≤ κ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ u, δ / 2 < |u| → φ u = 0) →
      (∀ h, |h| ≤ δ → ∫ u, (φ u - φ (u - h)) ^ 2 ≤ (κ * h / δ) ^ 2 * ∫ u, φ u ^ 2) →
      ∀ (K : ℕ) (M : Fin K → ℕ) (c : Fin K → ℝ) (a x : (k : Fin K) → Fin (M k) → ℝ),
      (∀ k, 0 ≤ c k) → (∀ k i j, i ≠ j → s ≤ |x k i - x k j|) →
      (∀ n : ℕ, 2 ≤ n → coneAutocorr φ c a x (Real.log n) = 0) →
      0 ≤ ∑ k, c k * WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ (a k) (x k) u : ℂ))
        (fun u => (bumpSum φ (a k) (x k) u : ℂ))) := by
  set c₀ := Real.exp (-s / 2) with hc₀
  have hc₀0 : 0 < c₀ := Real.exp_pos _
  set η := s * c₀ / 64 with hη
  have hη0 : 0 < η := by positivity
  set C₂ := coneMarginConst s κ with hC₂
  set X : ℝ := 8 / 5 * Real.exp (s / 2) * |C₂| with hX
  refine ⟨min (min (min (s / 4) (η / 2)) (min (η ^ 2) 1)) (Real.exp (-X)), by positivity,
    fun δ hδ hδlt φ hφ hφs hreg K M c a x hc hsep hblind => ?_⟩
  have hd1 : δ < s / 4 := lt_of_lt_of_le hδlt
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hd2 : δ < η / 2 := lt_of_lt_of_le hδlt
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hd3 : δ < η ^ 2 := lt_of_lt_of_le hδlt
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd4 : δ < 1 := lt_of_lt_of_le hδlt
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hd5 : δ < Real.exp (-X) := lt_of_lt_of_le hδlt (min_le_right _ _)
  -- the cut-off index
  set N₀ : ℕ := ⌈(η / δ) ^ 2⌉₊ with hN₀
  have hN1 : (η / δ) ^ 2 ≤ N₀ := Nat.le_ceil _
  have hN2 : (N₀ : ℝ) ≤ (η / δ) ^ 2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hq2 : 2 ≤ η / δ := by rw [le_div_iff₀ hδ]; linarith
  have hN₀2 : 2 ≤ N₀ := by
    have : (2 : ℝ) ≤ N₀ := by nlinarith
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have h1N : 1 / (N₀ : ℝ) ≤ δ := by
    rw [div_le_iff₀ hN0]
    have h1 : (η / δ) ^ 2 * δ = η ^ 2 / δ := by field_simp
    have h2 : 1 ≤ η ^ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    nlinarith
  have hL : C₂ ≤ 5 / 8 * c₀ * Real.log (1 / δ) := by
    have h1 : X < Real.log (1 / δ) := by
      rw [one_div, Real.log_inv, lt_neg]
      have := Real.log_lt_log hδ hd5
      rwa [Real.log_exp] at this
    have he : c₀ * Real.exp (s / 2) = 1 := by
      rw [hc₀, ← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]
    have h2 : 5 / 8 * c₀ * X = |C₂| := by rw [hX]; linear_combination |C₂| * he
    have h3 := le_abs_self C₂
    nlinarith
  have hcoef := cone_coefficient_nonneg (N₀ := N₀) hs hκ hδ hd2.le (by linarith) hd4.le hN1 hN2
    hL
  -- the per-test Lévy bounds and the pole of the combination
  have hk : ∀ k, (EF.gammaBracket 0 + c₀ * Real.log ((s - δ) / δ)) *
      (∫ u, bumpSum φ (a k) (x k) u ^ 2) +
        2 * ∫ y, autocorr φ (a k) (x k) y * Real.exp (y / 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ (a k) (x k) u : ℂ))
        (fun u => (bumpSum φ (a k) (x k) u : ℂ))) :=
    fun k => le_weilArchRe_add_pole hφ hφs hδ (by linarith) (hsep k)
  have hP := abs_integral_coneAutocorr_le hφ hφs hδ (by linarith) hκ hreg hc hsep hN₀2 h1N hblind
  set G := EF.gammaBracket 0 + c₀ * Real.log ((s - δ) / δ) with hG
  set C₀ := coneMass φ c a x with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hc k) (integral_nonneg fun u => sq_nonneg _)
  have hlower : G * C₀ + 2 * ∫ y, coneAutocorr φ c a x y * Real.exp (y / 2) ≤
      ∑ k, c k * WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ (a k) (x k) u : ℂ))
        (fun u => (bumpSum φ (a k) (x k) u : ℂ))) := by
    rw [integral_coneAutocorr_mul_exp hφ hφs, hC₀]
    unfold coneMass
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    calc G * (c k * ∫ u, bumpSum φ (a k) (x k) u ^ 2) +
          2 * (c k * ∫ y, autocorr φ (a k) (x k) y * Real.exp (y / 2))
        = c k * (G * (∫ u, bumpSum φ (a k) (x k) u ^ 2) +
            2 * ∫ y, autocorr φ (a k) (x k) y * Real.exp (y / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk k) (hc k)
  have hab := neg_abs_le (∫ y, coneAutocorr φ c a x y * Real.exp (y / 2))
  have hid : G * C₀ - 2 * ((2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ *
      (2 + 2 * (Real.log N₀ + δ) / s)) * C₀ +
        Real.sqrt 2 * (κ / δ * C₀) / Real.sqrt ((N₀ : ℝ) - 1)) =
      C₀ * (G - 2 * ((2 / Real.sqrt N₀ + 2 * δ * Real.sqrt N₀ *
        (2 + 2 * (Real.log N₀ + δ) / s)) + Real.sqrt 2 * (κ / δ) / Real.sqrt ((N₀ : ℝ) - 1))) := by
    ring
  have hfin := mul_nonneg hC₀0 hcoef
  rw [← hid] at hfin
  linarith

end Cone

end RHTower.SeparatedBump

end
