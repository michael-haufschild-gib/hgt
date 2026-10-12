import GaloisForLFunctions.RHTower.EvenWeilRHCriterion

/-!
# The spectral dictionary: heat windows reproduce even Weil Rayleigh quotients

For a smooth even pole-free source `u` of half-width `A` with `A² < 4K`, the sharp-witness
polynomials `P_n` satisfy `Re H_{K/n}(P_n, P_n) → Re Σ F_u(z_q)²` and
`∫ heatTest(K/n, P_n)² → ∫ u²`. So the hyperplane Rayleigh quotients of the heat sections at window
`K` approach those of the even Weil form at half-width `2√K` from above.

This file proves the `L²` input: the heat smoothing `u_a` converges to `u` in `L²` as `a → 0`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly hasDerivAt_gaussPolyFun continuous_gaussPolyFun
  sq_integral_abs_gaussPolyFun_mul_exp_half_le)

namespace RHTower

noncomputable section

/-- The unit Gaussian density `(2π)^{-1/2} e^{-σ²/2}`. -/
def unitGauss (σ : ℝ) : ℝ := (2 * π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(σ ^ 2 / 2))

theorem unitGauss_nonneg (σ : ℝ) : 0 ≤ unitGauss σ := by unfold unitGauss; positivity

theorem integrable_unitGauss : Integrable unitGauss := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul ((2 * π) ^ (-(1 / 2 : ℝ)))
  refine h.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only [unitGauss]; ring_nf

theorem integral_unitGauss : ∫ σ, unitGauss σ = 1 := by
  have h := integral_gaussian (1 / 2)
  have e : (fun σ : ℝ => unitGauss σ) =
      fun σ => (2 * π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2) * σ ^ 2) := by
    funext σ; simp only [unitGauss]; ring_nf
  rw [e, integral_const_mul, h, show π / (1 / 2) = 2 * π by ring, Real.sqrt_eq_rpow,
    ← Real.rpow_add (by positivity)]
  norm_num

/-- `u_a(x) = ∫ u(x - √a σ) φ(σ) dσ` with `φ` the unit Gaussian. -/
theorem heatSmooth_eq_average {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) (x : ℝ) :
    heatSmooth a u x = ∫ σ, u (x - Real.sqrt a * σ) * unitGauss σ := by
  have hs := Real.sqrt_pos.2 ha
  have e0 : ∫ t, u t * gaussHeatKernel a (x - t) =
      ∫ t, (fun s => u (x - s) * gaussHeatKernel a s) (x - t) := by
    congr 1; funext t; simp only [sub_sub_cancel]
  rw [heatSmooth, e0, integral_sub_left_eq_self (fun s => u (x - s) * gaussHeatKernel a s) volume x]
  have h := Measure.integral_comp_mul_left (fun t => u (x - t) * gaussHeatKernel a t) (Real.sqrt a)
  rw [abs_inv, abs_of_pos hs, smul_eq_mul] at h
  have e : ∫ t, u (x - t) * gaussHeatKernel a t =
      Real.sqrt a * ∫ σ, u (x - Real.sqrt a * σ) * gaussHeatKernel a (Real.sqrt a * σ) := by
    rw [h]; field_simp
  rw [e, ← integral_const_mul]
  congr 1
  funext σ
  have hk : Real.sqrt a * gaussHeatKernel a (Real.sqrt a * σ) = unitGauss σ := by
    unfold gaussHeatKernel unitGauss
    rw [mul_pow, Real.sq_sqrt ha.le, Real.mul_rpow (by positivity) ha.le, Real.sqrt_eq_rpow]
    have : a ^ (1 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← Real.rpow_add ha]; norm_num
    rw [show a * σ ^ 2 / (2 * a) = σ ^ 2 / 2 by field_simp]
    linear_combination (2 * π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(σ ^ 2 / 2)) * this
  rw [← hk]; ring

/-- `u_a(x) → u(x)` as `a → 0⁺` along any sequence. -/
theorem tendsto_heatSmooth_apply {u : ℝ → ℝ} (hu : Continuous u) {B : ℝ} (hB : ∀ t, |u t| ≤ B)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => heatSmooth (a n) u x) atTop (𝓝 (u x)) := by
  simp_rw [heatSmooth_eq_average (ha _)]
  have hlim : u x = ∫ σ, u (x - Real.sqrt 0 * σ) * unitGauss σ := by
    simp only [Real.sqrt_zero, zero_mul, sub_zero]
    rw [integral_const_mul, integral_unitGauss, mul_one]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun σ => B * unitGauss σ) (fun n => ?_)
    (integrable_unitGauss.const_mul B) (fun n => Filter.Eventually.of_forall fun σ => ?_)
    (Filter.Eventually.of_forall fun σ => ?_)
  · exact ((hu.comp (continuous_const.sub (continuous_const.mul continuous_id))).mul
      (Real.continuous_exp.comp (by fun_prop) |>.const_mul _ |>.congr fun σ => rfl)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (unitGauss_nonneg σ)]
    exact mul_le_mul_of_nonneg_right (hB _) (unitGauss_nonneg σ)
  · have hs : Tendsto (fun n => Real.sqrt (a n)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp ha0
    exact ((hu.tendsto _).comp (tendsto_const_nhds.sub (hs.mul_const σ))).mul_const _

theorem abs_heatSmooth_le_bound {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) (x : ℝ) : |heatSmooth a u x| ≤ B := by
  rw [heatSmooth_eq_average ha]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  calc |∫ σ, u (x - Real.sqrt a * σ) * unitGauss σ|
      ≤ ∫ σ, |u (x - Real.sqrt a * σ) * unitGauss σ| := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * unitGauss σ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_unitGauss.const_mul B) (Filter.Eventually.of_forall fun σ => ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (unitGauss_nonneg σ)]
        exact mul_le_mul_of_nonneg_right (hB _) (unitGauss_nonneg σ)
    _ = B := by rw [integral_const_mul, integral_unitGauss, mul_one]

/-- `(2πa)^{-1/2} e^{-x²/(8a)} ≤ 2 (2π)^{-1/2} e^{-x²}` for `0 < a ≤ 1/16`, `|x| ≥ 1`. -/
theorem heatKernelTail_le {a x : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (hx : 1 ≤ |x|) :
    (2 * π * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2 / (8 * a))) ≤
      2 * (2 * π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2)) := by
  set s := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hrpow : (2 * π * a) ^ (-(1 / 2 : ℝ)) = (2 * π) ^ (-(1 / 2 : ℝ)) * (1 / s) := by
    rw [Real.mul_rpow (by positivity) ha.le, hs, Real.sqrt_eq_rpow, Real.rpow_neg ha.le]
    simp only [one_div]
  rw [hrpow]
  set y := 1 / (16 * a) with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hexp : Real.exp (-(x ^ 2 / (8 * a))) ≤ Real.exp (-y) * Real.exp (-(x ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : x ^ 2 / (8 * a) = x ^ 2 / (16 * a) + x ^ 2 / (16 * a) := by ring
    have h2 : y ≤ x ^ 2 / (16 * a) := by
      rw [hy]; exact div_le_div_of_nonneg_right hx2 (by positivity)
    have h3 : x ^ 2 ≤ x ^ 2 / (16 * a) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hsy : 1 / s = 4 * Real.sqrt y := by
    rw [hy, Real.sqrt_div' _ (by positivity), Real.sqrt_mul' _ ha.le, show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_one, ← hs]
    field_simp
  have hkey : 4 * Real.sqrt y * Real.exp (-y) ≤ 2 := by
    have h1 : 2 * Real.sqrt y ≤ 1 + y := by
      nlinarith [sq_nonneg (Real.sqrt y - 1), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith)]
    have h2 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-y)
    nlinarith
  have hc := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 * π by positivity) (-(1 / 2 : ℝ))
  calc (2 * π) ^ (-(1 / 2 : ℝ)) * (1 / s) * Real.exp (-(x ^ 2 / (8 * a)))
      ≤ (2 * π) ^ (-(1 / 2 : ℝ)) * (1 / s) * (Real.exp (-y) * Real.exp (-(x ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (2 * π) ^ (-(1 / 2 : ℝ)) * (4 * Real.sqrt y * Real.exp (-y)) * Real.exp (-(x ^ 2)) := by
        rw [hsy]; ring
    _ ≤ (2 * π) ^ (-(1 / 2 : ℝ)) * 2 * Real.exp (-(x ^ 2)) := by gcongr
    _ = _ := by ring

/-- **The heat smoothing converges in `L²`.** -/
theorem tendsto_integral_sq_heatSmooth_sub {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (heatSmooth (a n) u x - u x) ^ 2) atTop (𝓝 0) := by
  have huc := hu.continuous
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuous huc
  have hB' : ∀ t, |u t| ≤ B := fun t => by rw [← Real.norm_eq_abs]; exact hB t
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  set U₁ := ∫ t, |u t| with hU₁
  have hU₁0 : 0 ≤ U₁ := integral_nonneg fun _ => abs_nonneg _
  set X₀ := max (2 * A) 1 with hX₀
  set c := 2 * (2 * π) ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set D : ℝ → ℝ := fun x => (Icc (-X₀) X₀).indicator (fun _ => (2 * B) ^ 2) x +
    (U₁ * c) ^ 2 * Real.exp (-(2 * x ^ 2)) with hD
  have hDi : Integrable D := by
    refine (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc |>.add ?_
    have := (integrable_exp_neg_mul_sq (b := 2) (by norm_num)).const_mul ((U₁ * c) ^ 2)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hev : ∀ᶠ n in atTop, a n ≤ 1 / 16 := ha0.eventually (ge_mem_nhds (by norm_num))
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := (atTop : Filter ℕ)) (F := fun n x => (heatSmooth (a n) u x - u x) ^ 2) (f := fun _ => (0 : ℝ)) D
    (Filter.Eventually.of_forall fun n => ?_) ?_ hDi ?_
  · simpa using h
  · exact (((continuous_heatSmooth hu hcpt (ha n)).sub huc).pow 2).aestronglyMeasurable
  · filter_upwards [hev] with n hn
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hD0 : 0 ≤ (Icc (-X₀) X₀).indicator (fun _ => (2 * B) ^ 2) x :=
      Set.indicator_nonneg (fun _ _ => by positivity) x
    have hE0 : 0 ≤ (U₁ * c) ^ 2 * Real.exp (-(2 * x ^ 2)) := by positivity
    by_cases hx : x ∈ Icc (-X₀) X₀
    · simp only [hD, Set.indicator_of_mem hx]
      have h1 := abs_heatSmooth_le_bound (ha n) hB' x
      have h2 := hB' x
      have : |heatSmooth (a n) u x - u x| ≤ 2 * B := by
        have := abs_sub (heatSmooth (a n) u x) (u x); linarith
      have h3 : (heatSmooth (a n) u x - u x) ^ 2 ≤ (2 * B) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
    · simp only [hD, Set.indicator_of_notMem hx, zero_add]
      have hxX : X₀ < |x| := by
        rw [Set.mem_Icc, not_and_or] at hx
        rcases hx with h1 | h1
        · push Not at h1; exact lt_abs.2 (Or.inr (by linarith))
        · push Not at h1; exact lt_abs.2 (Or.inl h1)
      have hA : A < |x| := by
        have : A ≤ X₀ := by
          rcases le_or_gt 0 A with h | h
          · exact (by linarith : A ≤ 2 * A).trans (le_max_left _ _)
          · exact (by linarith : A ≤ 1).trans (le_max_right _ _)
        linarith
      have hux : u x = 0 := hsupp x hA
      have h2A : 2 * A ≤ |x| := (le_max_left _ _).trans hxX.le
      have h1x : 1 ≤ |x| := (le_max_right _ _).trans hxX.le
      have hfar := abs_heatSmooth_le_of_far huc hcpt hsupp (ha n) h2A
      have htail := heatKernelTail_le (ha n) hn h1x
      have hbd : |heatSmooth (a n) u x| ≤ U₁ * c * Real.exp (-(x ^ 2)) := by
        calc |heatSmooth (a n) u x|
            ≤ U₁ * ((2 * π * a n) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2 / (8 * a n)))) := hfar
          _ ≤ U₁ * (2 * (2 * π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2))) :=
              mul_le_mul_of_nonneg_left htail hU₁0
          _ = U₁ * c * Real.exp (-(x ^ 2)) := by rw [hc]; ring
      rw [hux, sub_zero, ← sq_abs]
      calc |heatSmooth (a n) u x| ^ 2 ≤ (U₁ * c * Real.exp (-(x ^ 2))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hbd 2
        _ = (U₁ * c) ^ 2 * Real.exp (-(2 * x ^ 2)) := by
            rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  · refine Filter.Eventually.of_forall fun x => ?_
    have := tendsto_heatSmooth_apply huc hB' ha ha0 x
    have h2 := ((this.sub_const (u x)).pow 2)
    simpa using h2

/-! ## The pole-corrected witness, with its pole coefficient -/

/-- The comparison of `exists_poleCorrected_near_smoothed` for an explicit preimage `P₀`, together
with the bound `|P₀(−1/4)| ≤ ∫ |g − u_a| e^{|x|/2}` on the pole coefficient. -/
theorem poleCorrected_near_smoothed_of_eq {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {a : ℝ} (ha : 0 < a)
    (ha16 : a ≤ 1 / 16) (n : ℕ) {P₀ : ℝ[X]}
    (hP₀ : heatPolyR a P₀ = truncHeatPoly u hu hcpt ha (2 * n + 1)) :
    |P₀.eval (-1 / 4)| ≤ stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) ∧
      ‖heatHankel a ((P₀ - C (P₀.eval (-1 / 4))).map (algebraMap ℝ ℂ))
          ((P₀ - C (P₀.eval (-1 / 4))).map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤
        stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
            (stripMass (truncHeatTestDD u hu hcpt ha n) +
              Real.exp (1 / 8) * stripMass (deriv (deriv u))) *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 +
          stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
            (2 * (Real.exp (1 / 8) * stripMass (truncHeatTestDD u hu hcpt ha n) *
                ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) +
              stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
                (Real.exp (1 / 2) * (1 + 1 / a) *
                  ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖))) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  set Q := truncHeatPoly u hu hcpt ha (2 * n + 1) with hQ_def
  have hQe : Q.comp (-X) = Q := truncHeatPoly_comp_neg u hu hcpt heven ha _
  have hQd : Q.natDegree ≤ 2 * n := (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  set c := P₀.eval (-1 / 4) with hc_def
  -- notation
  set g := truncHeatTest u hu hcpt ha n with hg_def
  have hgQ : g = gaussPolyFun Q (1 / (2 * a)) := rfl
  set Ngu := stripMass (fun x => g x - heatSmooth a u x) with hNgu
  set Ng2 := stripMass (truncHeatTestDD u hu hcpt ha n) with hNg2
  set U2 := stripMass (deriv (deriv u)) with hU2
  set S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 with hS₂
  set S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS
  set Fg : ℂ → ℂ := heatStripTransform (fun x => ((g x : ℝ) : ℂ)) with hFg_def
  set Fw : ℂ → ℂ := heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ)) with hFw_def
  set Fu : ℂ → ℂ := heatStripTransform (fun x => ((u x : ℝ) : ℂ)) with hFu_def
  have hFgP : ∀ z, Fg z = Complex.exp (-(a : ℂ) * z ^ 2 / 2) *
      (P₀.map (algebraMap ℝ ℂ)).eval (z ^ 2) := fun z => by
    have h := heatStripTransform_heatPhysical ha P₀ z
    rw [hP₀] at h
    exact h
  have hFw : ∀ z, Fw z = Complex.exp (-(a : ℂ) * z ^ 2 / 2) * Fu z := fun z =>
    heatStripTransform_heatSmooth ha hu.continuous hcpt z
  -- integrability
  have hgi : Integrable (fun x => ‖((g x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) :=
    integrable_norm_ofReal_gaussPolyFun_mul_exp Q hβ
  have hwi : Integrable (fun x => ‖((heatSmooth a u x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
    simpa only [norm_ofReal_mul_exp] using
      integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp
  have hgc : Continuous g := continuous_gaussPolyFun _ _
  have hwc : Continuous (heatSmooth a u) := continuous_heatSmooth hu hcpt ha
  have hdi : Integrable (fun x => ‖(((g x - heatSmooth a u x) : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
    refine (hgi.add hwi).mono' ((continuous_norm.comp (Complex.continuous_ofReal.comp
      (hgc.sub hwc))).mul (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [Complex.ofReal_sub, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
  -- (b1) the difference on the strip
  have hb1 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Fg z - Fw z‖ ≤ Ngu := fun z hz => by
    have h1 := integrable_mul_cexp_of_strip (f := fun x => ((g x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hgc) hgi hz
    have h2 := integrable_mul_cexp_of_strip (f := fun x => ((heatSmooth a u x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hwc) hwi hz
    have e : Fg z - Fw z = heatStripTransform (fun x => (((g x - heatSmooth a u x) : ℝ) : ℂ)) z := by
      rw [hFg_def, hFw_def]
      unfold heatStripTransform
      rw [← integral_sub h1 h2]
      congr 1; funext x; push_cast; ring
    rw [e]
    have := norm_heatStripTransform_le hdi hz
    simpa only [Complex.norm_real, Real.norm_eq_abs, hNgu, stripMass] using this
  -- (b2), (b3)
  have hb2 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖z‖ ^ 2 * ‖Fg z‖ ≤ Ng2 := fun z hz =>
    sq_norm_mul_heatStripTransform_gaussPolyFun_le Q hβ hz
  have hb3 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖z‖ ^ 2 * ‖Fw z‖ ≤ Real.exp (1 / 8) * U2 := fun z hz => by
    rw [hFw, norm_mul]
    have he : ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ ≤ Real.exp (1 / 8) :=
      (norm_cexp_heat_le ha.le hz).trans (Real.exp_le_exp.2 (by linarith))
    have hu2 := sq_norm_mul_heatStripTransform_source_le hu hcpt hz
    calc ‖z‖ ^ 2 * (‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ * ‖Fu z‖)
        = ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ * (‖z‖ ^ 2 * ‖Fu z‖) := by ring
      _ ≤ Real.exp (1 / 8) * U2 := mul_le_mul he hu2 (by positivity) (Real.exp_pos _).le
  -- (b4) the pole value
  have hU2 : 0 ≤ U2 := integral_nonneg fun _ => by positivity
  have hNgu0 : 0 ≤ Ngu := integral_nonneg fun _ => by positivity
  have hcb : |c| ≤ Ngu := by
    have hzI : |(I / 2 : ℂ).im| ≤ 1 / 2 := by simp [abs_of_pos]
    have h := hb1 (I / 2) hzI
    have hw0 : Fw (I / 2) = 0 := by
      rw [hFw, hFu_def, heatStripTransform_I_half_eq_zero heven hpole, mul_zero]
    have hg0 : Fg (I / 2) = Complex.exp ((a : ℂ) / 8) * ((c : ℝ) : ℂ) := by
      rw [hFgP, hc_def]
      have hsq : (I / 2 : ℂ) ^ 2 = (((-1 / 4 : ℝ)) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
      rw [hsq, eval_map_ofReal]
      congr 1
      congr 1
      push_cast
      ring_nf
    rw [hw0, sub_zero, hg0, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs] at h
    have : (((a : ℂ) / 8).re) = a / 8 := by simp
    rw [this] at h
    have he : 1 ≤ Real.exp (a / 8) := Real.one_le_exp (by positivity)
    nlinarith [abs_nonneg c]
  refine ⟨hcb, ?_⟩
  -- (b5), (b6) cross terms
  have hcross := norm_heatHankel_one_le (P := P₀.map (algebraMap ℝ ℂ)) ha.le (M := Ng2)
    fun z hz => by rw [← hFgP]; exact hb2 z hz
  have he8 : Real.exp (a / 8) ≤ Real.exp (1 / 8) := Real.exp_le_exp.2 (by linarith)
  have he2 : Real.exp (a / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have h11 := norm_heatHankel_one_one_le ha
  -- (b7) comparison
  obtain ⟨-, -, hcmp⟩ := norm_tsum_sq_sub_le (F := fun q => Fg (xiSpectralPoint q))
    (G := fun q => Fw (xiSpectralPoint q)) (D := Ngu) (MF := Ng2) (MG := Real.exp (1 / 8) * U2)
    (fun q => hb1 _ (abs_im_xiSpectralPoint_le_half q))
    (fun q => hb2 _ (abs_im_xiSpectralPoint_le_half q))
    (fun q => hb3 _ (abs_im_xiSpectralPoint_le_half q))
  have hH0 : heatHankel a (P₀.map (algebraMap ℝ ℂ)) (P₀.map (algebraMap ℝ ℂ)) =
      ∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2 := by
    have h := heatHankel_map_eq_tsum_sq ha P₀
    rw [hP₀] at h
    exact h
  have hmap : (P₀ - C c).map (algebraMap ℝ ℂ) = P₀.map (algebraMap ℝ ℂ) - C (c : ℂ) := by
    rw [Polynomial.map_sub, Polynomial.map_C]; rfl
  rw [hmap, heatHankel_sub_C ha, hH0]
  have hc' : ‖(c : ℂ)‖ ≤ Ngu := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hcb
  have hcc : ‖((starRingEnd ℂ) (c : ℂ))‖ ≤ Ngu := by rw [Complex.norm_conj]; exact hc'
  have hns : ‖((Complex.normSq (c : ℂ) : ℝ) : ℂ)‖ ≤ Ngu * Ngu := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, sq]
    exact mul_le_mul hc' hc' (norm_nonneg _) hNgu0
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun _ => by positivity
  have hNg20 : 0 ≤ Ng2 := integral_nonneg fun _ => by positivity
  have hA1 : ‖heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1‖ ≤ Real.exp (1 / 8) * Ng2 * S₂ :=
    hcross.1.trans (by gcongr)
  have hA2 : ‖heatHankel a 1 (P₀.map (algebraMap ℝ ℂ))‖ ≤ Real.exp (1 / 8) * Ng2 * S₂ :=
    hcross.2.trans (by gcongr)
  have hA3 : ‖heatHankel a 1 1‖ ≤ Real.exp (1 / 2) * (1 + 1 / a) * S :=
    h11.trans (by gcongr)
  calc ‖(∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2) -
          (starRingEnd ℂ) (c : ℂ) * heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1 -
          (c : ℂ) * heatHankel a 1 (P₀.map (algebraMap ℝ ℂ)) +
          ((Complex.normSq (c : ℂ) : ℝ) : ℂ) * heatHankel a 1 1 -
          ∑' q : XiZeroCopy, Fw (xiSpectralPoint q) ^ 2‖
      = ‖((∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2) -
            ∑' q : XiZeroCopy, Fw (xiSpectralPoint q) ^ 2) -
          ((starRingEnd ℂ) (c : ℂ) * heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1 +
            (c : ℂ) * heatHankel a 1 (P₀.map (algebraMap ℝ ℂ))) +
          ((Complex.normSq (c : ℂ) : ℝ) : ℂ) * heatHankel a 1 1‖ := by ring_nf
    _ ≤ Ngu * (Ng2 + Real.exp (1 / 8) * U2) * S₂ +
          (Ngu * (Real.exp (1 / 8) * Ng2 * S₂) + Ngu * (Real.exp (1 / 8) * Ng2 * S₂)) +
          Ngu * Ngu * (Real.exp (1 / 2) * (1 + 1 / a) * S) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hcmp
          ((norm_add_le _ _).trans (add_le_add ?_ ?_)))) ?_)
        · rw [norm_mul]; exact mul_le_mul hcc hA1 (norm_nonneg _) hNgu0
        · rw [norm_mul]; exact mul_le_mul hc' hA2 (norm_nonneg _) hNgu0
        · rw [norm_mul]; exact mul_le_mul hns hA3 (norm_nonneg _) (by positivity)
    _ = _ := by ring


/-! ## The `L²` size of the corrected witness -/

theorem heatPolyR_sub_C (a : ℝ) (P : ℝ[X]) (c : ℝ) :
    heatPolyR a (P - C c) = heatPolyR a P - C ((2 * π * a) ^ (-(1 / 2 : ℝ)) * c) := by
  have h1 : P - C c = P + C (-c) * X ^ 0 := by simp [sub_eq_add_neg]
  rw [h1, heatPolyR_add, heatPolyR_C_mul_X_pow]
  simp [gaussDerivPolyR, sub_eq_add_neg]

theorem gaussPolyFun_heatPolyR_sub_C {a : ℝ} (P : ℝ[X]) (c x : ℝ) :
    gaussPolyFun (heatPolyR a (P - C c)) (1 / (2 * a)) x =
      gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x - c * gaussHeatKernel a x := by
  rw [heatPolyR_sub_C]
  simp only [gaussPolyFun, eval_sub, eval_C, gaussHeatKernel]
  rw [show -(1 / (2 * a) * x ^ 2) = -(x ^ 2 / (2 * a)) by ring]
  ring

theorem gaussHeatKernel_sq_eq {a : ℝ} (ha : 0 < a) :
    (fun x => gaussHeatKernel a x ^ 2) =
      fun x => (2 * π * a) ^ (-(1 : ℝ)) * Real.exp (-(1 / a) * x ^ 2) := by
  funext x
  unfold gaussHeatKernel
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.exp_nat_mul]
  push_cast
  congr 1
  · norm_num
  · congr 1; field_simp

theorem integral_gaussHeatKernel_sq {a : ℝ} (ha : 0 < a) :
    ∫ x, gaussHeatKernel a x ^ 2 = (2 * π * a) ^ (-(1 : ℝ)) * Real.sqrt (π * a) := by
  rw [gaussHeatKernel_sq_eq ha, integral_const_mul, integral_gaussian,
    show π / (1 / a) = π * a by field_simp]

theorem integrable_gaussHeatKernel_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun x => gaussHeatKernel a x ^ 2) := by
  rw [gaussHeatKernel_sq_eq ha]
  exact (integrable_exp_neg_mul_sq (b := 1 / a) (by positivity)).const_mul _

/-- The explicit-preimage form of `exists_poleCorrected_err_le`. -/
theorem poleCorrected_err_le_of_eq {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) (he1 : witnessE1 u a θ n ≤ 1) {P₀ : ℝ[X]}
    (hP₀ : heatPolyR a P₀ = truncHeatPoly u hu hcpt ha (2 * n + 1)) :
      ‖heatHankel a ((P₀ - C (P₀.eval (-1 / 4))).map (algebraMap ℝ ℂ))
          ((P₀ - C (P₀.eval (-1 / 4))).map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤
        witnessErr (Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n))
          (4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a)))) σ (4 * (1 / (2 * a)) * (2 * n + 3))
          (witnessG u B X) (heatStripConstant X) (stripMass (deriv (deriv u)))
          (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
          (∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) := by
  refine (poleCorrected_near_smoothed_of_eq hu hcpt hsupp heven hpole ha ha16 n hP₀).2.trans ?_
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have ha1 : a < 1 := by linarith
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set U₁ := ∫ t, |u t| with hU₁
  have hU₁0 : 0 ≤ U₁ := integral_nonneg fun _ => abs_nonneg _
  set e1 := witnessE1 u a θ n with he1_def
  have he10 : 0 ≤ e1 := by
    have : 0 ≤ (θ * Real.exp (1 - θ)) ^ (2 * n + 1) / (1 - θ) :=
      div_nonneg (pow_nonneg (mul_nonneg hθ0 (Real.exp_pos _).le) _) (by linarith)
    have := heatHermiteScale_pos ha
    rw [he1_def, witnessE1]
    positivity
  set Bw := 2 * X * (B * Real.exp (X / 2)) + 4 * U₁ with hBw
  set G := Real.sqrt (2 + 2 * (B * Bw)) with hG
  have hG2 : G ^ 2 = 2 + 2 * (B * Bw) := Real.sq_sqrt (by positivity)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  set ι := Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1) with hι
  have hι2 : ι ^ 2 = 2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1 := Real.sq_sqrt (by positivity)
  set τu := 4 * U₁ * Real.exp (-(X ^ 2 / (32 * a))) with hτu
  set Y := 4 * (1 / (2 * a)) * (2 * n + 3) with hY
  set E := heatStripConstant X with hE
  have hE0 : 0 ≤ E := by rw [hE, heatStripConstant]; positivity
  set g := truncHeatTest u hu hcpt ha n with hg_def
  have hgQ : g = gaussPolyFun (truncHeatPoly u hu hcpt ha (2 * n + 1)) (1 / (2 * a)) := rfl
  have hQd : (truncHeatPoly u hu hcpt ha (2 * n + 1)).natDegree ≤ 2 * n :=
    (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  -- the `L²` error
  have hE1 : ∫ x, (g x - heatSmooth a u x) ^ 2 ≤ e1 := by
    have h := integral_sq_truncHeatTest_sub_le u hu hcpt hsupp ha hθ0 hθ1 hN
    rw [integral_norm_scaledSource hu hcpt (heatHermiteScale_pos ha)] at h
    rw [he1_def, witnessE1]
    exact h
  -- `∫ u_a² ≤ B Bw`
  obtain ⟨hua_int, hua⟩ := integral_heatSmooth_sq_le hu hcpt hsupp ha ha16 hB
  have hBw := stripMass_heatSmooth_le hu hcpt hsupp ha ha16 hB hX1 hXA
  have hua2 : ∫ x, heatSmooth a u x ^ 2 ≤ B * Bw := hua.trans (mul_le_mul_of_nonneg_left hBw hB0)
  -- `∫ g² ≤ G²`
  have hg_int : Integrable (fun x => g x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ (by linarith)
  have hd_int : Integrable (fun x => (g x - heatSmooth a u x) ^ 2) := by
    refine ((hg_int.add hua_int).const_mul 2).mono'
      (((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    have key : 2 * (g x ^ 2 + heatSmooth a u x ^ 2) - (g x - heatSmooth a u x) ^ 2 =
        (g x + heatSmooth a u x) ^ 2 := by ring
    linarith [sq_nonneg (g x + heatSmooth a u x)]
  have hg2 : ∫ x, g x ^ 2 ≤ G ^ 2 := by
    have hpt : ∀ x, g x ^ 2 ≤ 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 :=
      fun x => by
        have key : 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 - g x ^ 2 =
            (g x - 2 * heatSmooth a u x) ^ 2 := by ring
        linarith [sq_nonneg (g x - 2 * heatSmooth a u x)]
    have := integral_mono hg_int ((hd_int.const_mul 2).add (hua_int.const_mul 2)) hpt
    simp only [Pi.add_apply] at this
    rw [integral_add (hd_int.const_mul 2) (hua_int.const_mul 2), integral_const_mul,
      integral_const_mul] at this
    rw [hG2]
    linarith
  have hgV0 : 0 ≤ ∫ x, g x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- tails and second derivative
  have hτg : stripMassOn g (heatTailSet X) ≤ Real.sqrt E * σ * G := by
    have h := sq_stripMassOn_tail_le hQd ha ha1 hX0 k hk
    rw [hσ, ← hgQ] at h
    have h2 : stripMassOn g (heatTailSet X) ^ 2 ≤ (Real.sqrt E * σ * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMassOn g (heatTailSet X) ^ 2 ≤ E * σ ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * σ ^ 2 * G ^ 2 := by gcongr
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have hNg2 : stripMass (truncHeatTestDD u hu hcpt ha n) ≤ Real.sqrt E * Y * G := by
    have h := sq_stripMass_dd_le hQd ha ha1 hX0 k hk
    have h2 : stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ (Real.sqrt E * Y * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ E * Y ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * Y ^ 2 * G ^ 2 := by gcongr
    have hY0 : 0 ≤ Y := by positivity
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  -- the inner part and the source tail
  have hinner : ∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2) ≤ ι := by
    obtain ⟨-, h⟩ := sq_setIntegral_inner_abs_mul_exp_half_le
      ((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)) hd_int hX0.le
    have h2 : (∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2)) ^ 2 ≤ ι ^ 2 := by
      rw [hι2]
      calc _ ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) * ∫ x, (g x - heatSmooth a u x) ^ 2 := h
        _ ≤ _ := by gcongr
    have hι0 : 0 ≤ ι := Real.sqrt_nonneg _
    exact abs_le_of_sq_le_sq' h2 hι0 |>.2
  obtain ⟨-, htail⟩ := integrableOn_tail_heatSmooth hu hcpt hsupp ha ha16 hX1 hXA
  have hNgu : stripMass (fun x => g x - heatSmooth a u x) ≤
      ι + stripMassOn g (heatTailSet X) + τu := by
    have h := stripMass_sub_le (f₁ := g) (continuous_gaussPolyFun _ _)
      (continuous_heatSmooth hu hcpt ha)
      (sq_integral_abs_gaussPolyFun_mul_exp_half_le (truncHeatPoly u hu hcpt ha (2 * n + 1)) hβ
        one_pos 0).1
      (integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp) X
    have h3 : stripMassOn (heatSmooth a u) (heatTailSet X) ≤ τu := htail
    linarith
  -- collect
  have hN0 : 0 ≤ stripMass (fun x => g x - heatSmooth a u x) :=
    integral_nonneg fun _ => by positivity
  have hM0 : 0 ≤ stripMass (truncHeatTestDD u hu hcpt ha n) := integral_nonneg fun _ => by positivity
  have hU2 : 0 ≤ stripMass (deriv (deriv u)) := integral_nonneg fun _ => by positivity
  have hinv : 1 / a ≤ Y := by
    rw [hY]
    have : (1 : ℝ) / a = 2 * (1 / (2 * a)) := by field_simp
    rw [this]
    have h3 : (0 : ℝ) < 1 / (2 * a) := by positivity
    have h4 : (2 : ℝ) ≤ 4 * (2 * n + 3) := by
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith only [this]
    calc 2 * (1 / (2 * a)) ≤ (4 * (2 * n + 3)) * (1 / (2 * a)) :=
          mul_le_mul_of_nonneg_right h4 h3.le
      _ = 4 * (1 / (2 * a)) * (2 * n + 3) := by ring
  have hfinal := comparison_error_le (N := stripMass (fun x => g x - heatSmooth a u x))
    (M := stripMass (truncHeatTestDD u hu hcpt ha n)) (ι := ι) (τg := stripMassOn g (heatTailSet X))
    (τu := τu) (σ := σ) (Y := Y) (G := G) (E := E) (U := stripMass (deriv (deriv u)))
    (S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
    (S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (n := 1) (K := a)
    (c := Real.exp (1 / 8)) (e := Real.exp (1 / 2)) hN0 (Real.sqrt_nonneg _) (by positivity) hσ0
    hG0 hE0 hU2 (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity)
    (Real.exp_pos _).le (Real.exp_pos _).le (by positivity) hinv hNgu hτg hNg2 hM0
  exact hfinal


/-- The `L²` and strip-mass errors of the truncated test. -/
theorem witness_aux_bounds {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) (he1 : witnessE1 u a θ n ≤ 1) :
    (∫ x, (truncHeatTest u hu hcpt ha n x - heatSmooth a u x) ^ 2 ≤ witnessE1 u a θ n) ∧
      stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) ≤
        Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n) +
          Real.sqrt (heatStripConstant X) * σ * witnessG u B X +
          4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a))) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have ha1 : a < 1 := by linarith
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set U₁ := ∫ t, |u t| with hU₁
  have hU₁0 : 0 ≤ U₁ := integral_nonneg fun _ => abs_nonneg _
  set e1 := witnessE1 u a θ n with he1_def
  have he10 : 0 ≤ e1 := by
    have : 0 ≤ (θ * Real.exp (1 - θ)) ^ (2 * n + 1) / (1 - θ) :=
      div_nonneg (pow_nonneg (mul_nonneg hθ0 (Real.exp_pos _).le) _) (by linarith)
    have := heatHermiteScale_pos ha
    rw [he1_def, witnessE1]
    positivity
  set Bw := 2 * X * (B * Real.exp (X / 2)) + 4 * U₁ with hBw
  set G := Real.sqrt (2 + 2 * (B * Bw)) with hG
  have hG2 : G ^ 2 = 2 + 2 * (B * Bw) := Real.sq_sqrt (by positivity)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  set ι := Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1) with hι
  have hι2 : ι ^ 2 = 2 * Real.exp 1 * π * Real.exp (X ^ 2) * e1 := Real.sq_sqrt (by positivity)
  set τu := 4 * U₁ * Real.exp (-(X ^ 2 / (32 * a))) with hτu
  set Y := 4 * (1 / (2 * a)) * (2 * n + 3) with hY
  set E := heatStripConstant X with hE
  have hE0 : 0 ≤ E := by rw [hE, heatStripConstant]; positivity
  set g := truncHeatTest u hu hcpt ha n with hg_def
  have hgQ : g = gaussPolyFun (truncHeatPoly u hu hcpt ha (2 * n + 1)) (1 / (2 * a)) := rfl
  have hQd : (truncHeatPoly u hu hcpt ha (2 * n + 1)).natDegree ≤ 2 * n :=
    (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  -- the `L²` error
  have hE1 : ∫ x, (g x - heatSmooth a u x) ^ 2 ≤ e1 := by
    have h := integral_sq_truncHeatTest_sub_le u hu hcpt hsupp ha hθ0 hθ1 hN
    rw [integral_norm_scaledSource hu hcpt (heatHermiteScale_pos ha)] at h
    rw [he1_def, witnessE1]
    exact h
  -- `∫ u_a² ≤ B Bw`
  obtain ⟨hua_int, hua⟩ := integral_heatSmooth_sq_le hu hcpt hsupp ha ha16 hB
  have hBw := stripMass_heatSmooth_le hu hcpt hsupp ha ha16 hB hX1 hXA
  have hua2 : ∫ x, heatSmooth a u x ^ 2 ≤ B * Bw := hua.trans (mul_le_mul_of_nonneg_left hBw hB0)
  -- `∫ g² ≤ G²`
  have hg_int : Integrable (fun x => g x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ (by linarith)
  have hd_int : Integrable (fun x => (g x - heatSmooth a u x) ^ 2) := by
    refine ((hg_int.add hua_int).const_mul 2).mono'
      (((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    have key : 2 * (g x ^ 2 + heatSmooth a u x ^ 2) - (g x - heatSmooth a u x) ^ 2 =
        (g x + heatSmooth a u x) ^ 2 := by ring
    linarith [sq_nonneg (g x + heatSmooth a u x)]
  have hg2 : ∫ x, g x ^ 2 ≤ G ^ 2 := by
    have hpt : ∀ x, g x ^ 2 ≤ 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 :=
      fun x => by
        have key : 2 * (g x - heatSmooth a u x) ^ 2 + 2 * heatSmooth a u x ^ 2 - g x ^ 2 =
            (g x - 2 * heatSmooth a u x) ^ 2 := by ring
        linarith [sq_nonneg (g x - 2 * heatSmooth a u x)]
    have := integral_mono hg_int ((hd_int.const_mul 2).add (hua_int.const_mul 2)) hpt
    simp only [Pi.add_apply] at this
    rw [integral_add (hd_int.const_mul 2) (hua_int.const_mul 2), integral_const_mul,
      integral_const_mul] at this
    rw [hG2]
    linarith
  have hgV0 : 0 ≤ ∫ x, g x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- tails and second derivative
  have hτg : stripMassOn g (heatTailSet X) ≤ Real.sqrt E * σ * G := by
    have h := sq_stripMassOn_tail_le hQd ha ha1 hX0 k hk
    rw [hσ, ← hgQ] at h
    have h2 : stripMassOn g (heatTailSet X) ^ 2 ≤ (Real.sqrt E * σ * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMassOn g (heatTailSet X) ^ 2 ≤ E * σ ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * σ ^ 2 * G ^ 2 := by gcongr
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have hNg2 : stripMass (truncHeatTestDD u hu hcpt ha n) ≤ Real.sqrt E * Y * G := by
    have h := sq_stripMass_dd_le hQd ha ha1 hX0 k hk
    have h2 : stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ (Real.sqrt E * Y * G) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hE0]
      calc stripMass (truncHeatTestDD u hu hcpt ha n) ^ 2 ≤ E * Y ^ 2 * ∫ x, g x ^ 2 := h
        _ ≤ E * Y ^ 2 * G ^ 2 := by gcongr
    have hY0 : 0 ≤ Y := by positivity
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  -- the inner part and the source tail
  have hinner : ∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2) ≤ ι := by
    obtain ⟨-, h⟩ := sq_setIntegral_inner_abs_mul_exp_half_le
      ((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)) hd_int hX0.le
    have h2 : (∫ x in Ioo (-X) X, |g x - heatSmooth a u x| * Real.exp (|x| / 2)) ^ 2 ≤ ι ^ 2 := by
      rw [hι2]
      calc _ ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) * ∫ x, (g x - heatSmooth a u x) ^ 2 := h
        _ ≤ _ := by gcongr
    have hι0 : 0 ≤ ι := Real.sqrt_nonneg _
    exact abs_le_of_sq_le_sq' h2 hι0 |>.2
  obtain ⟨-, htail⟩ := integrableOn_tail_heatSmooth hu hcpt hsupp ha ha16 hX1 hXA
  have hNgu : stripMass (fun x => g x - heatSmooth a u x) ≤
      ι + stripMassOn g (heatTailSet X) + τu := by
    have h := stripMass_sub_le (f₁ := g) (continuous_gaussPolyFun _ _)
      (continuous_heatSmooth hu hcpt ha)
      (sq_integral_abs_gaussPolyFun_mul_exp_half_le (truncHeatPoly u hu hcpt ha (2 * n + 1)) hβ
        one_pos 0).1
      (integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp) X
    have h3 : stripMassOn (heatSmooth a u) (heatTailSet X) ≤ τu := htail
    linarith
  have hGw : G = witnessG u B X := rfl
  refine ⟨?_, hNgu.trans ?_⟩
  · rw [he1_def] at hE1
    exact hE1
  · rw [← hGw]
    linarith only [hτg]

/-- The squared difference of the truncated test and the smoothing is integrable. -/
theorem integrable_sq_truncHeatTest_sub {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) :
    Integrable (fun x => (truncHeatTest u hu hcpt ha n x - heatSmooth a u x) ^ 2) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨hua_int, -⟩ := integral_heatSmooth_sq_le hu hcpt hsupp ha ha16 hB
  have hg_int : Integrable (fun x => truncHeatTest u hu hcpt ha n x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ (by linarith)
  refine ((hg_int.add hua_int).const_mul 2).mono'
    (((continuous_gaussPolyFun _ _).sub (continuous_heatSmooth hu hcpt ha)).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (truncHeatTest u hu hcpt ha n x + heatSmooth a u x)]

/-- **The `L²` error of the corrected witness.** With `c = P₀(−1/4)` and `|c| ≤ M`,
`∫ (g_P − u_a)² ≤ 2 ∫ (g − u_a)² + 2 M² ∫ G_a²`. -/
theorem integral_sq_corrected_sub_le {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {P₀ : ℝ[X]}
    (hP₀ : heatPolyR a P₀ = truncHeatPoly u hu hcpt ha (2 * n + 1)) {M : ℝ}
    (hM : |P₀.eval (-1 / 4)| ≤ M) :
    ∫ x, (gaussPolyFun (heatPolyR a (P₀ - C (P₀.eval (-1 / 4)))) (1 / (2 * a)) x -
        heatSmooth a u x) ^ 2 ≤
      2 * (∫ x, (truncHeatTest u hu hcpt ha n x - heatSmooth a u x) ^ 2) +
        2 * M ^ 2 * ((2 * π * a) ^ (-(1 : ℝ)) * Real.sqrt (π * a)) := by
  set c := P₀.eval (-1 / 4) with hc
  set g := truncHeatTest u hu hcpt ha n with hg
  have hgP : ∀ x, gaussPolyFun (heatPolyR a (P₀ - C c)) (1 / (2 * a)) x - heatSmooth a u x =
      (g x - heatSmooth a u x) - c * gaussHeatKernel a x := fun x => by
    rw [gaussPolyFun_heatPolyR_sub_C, hP₀]
    simp only [hg, truncHeatTest]
    ring
  simp_rw [hgP]
  have hk2 := integrable_gaussHeatKernel_sq ha
  have hd_int := integrable_sq_truncHeatTest_sub hu hcpt hsupp hB ha ha16 n
  have hpt : ∀ x, ((g x - heatSmooth a u x) - c * gaussHeatKernel a x) ^ 2 ≤
      2 * (g x - heatSmooth a u x) ^ 2 + 2 * c ^ 2 * gaussHeatKernel a x ^ 2 := fun x => by
    nlinarith [sq_nonneg ((g x - heatSmooth a u x) + c * gaussHeatKernel a x)]
  have hint2 : Integrable (fun x => 2 * (g x - heatSmooth a u x) ^ 2 +
      2 * c ^ 2 * gaussHeatKernel a x ^ 2) := (hd_int.const_mul 2).add (hk2.const_mul _)
  have hk0 : 0 ≤ (2 * π * a) ^ (-(1 : ℝ)) * Real.sqrt (π * a) := by positivity
  have hc2 : c ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
  calc ∫ x, ((g x - heatSmooth a u x) - c * gaussHeatKernel a x) ^ 2
      ≤ ∫ x, (2 * (g x - heatSmooth a u x) ^ 2 + 2 * c ^ 2 * gaussHeatKernel a x ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint2
          (Filter.Eventually.of_forall hpt)
    _ = 2 * (∫ x, (g x - heatSmooth a u x) ^ 2) + 2 * c ^ 2 * ∫ x, gaussHeatKernel a x ^ 2 := by
        rw [integral_add (hd_int.const_mul 2) (hk2.const_mul _), integral_const_mul,
          integral_const_mul, hg]
    _ ≤ _ := by
        rw [integral_gaussHeatKernel_sq ha, hg]
        gcongr

/-! ## The witness approximates the source in energy and in `L²` -/

/-- `(2πa)^{-1} √(πa) ≤ Y²` once `6/a ≤ Y` and `a ≤ 1`. -/
theorem gaussHeatKernel_sq_mass_le {a Y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hY : 6 / a ≤ Y) :
    (2 * π * a) ^ (-(1 : ℝ)) * Real.sqrt (π * a) ≤ Y ^ 2 := by
  rw [Real.rpow_neg_one]
  have hπ := Real.pi_gt_three
  have hs : Real.sqrt (π * a) ≤ π * a + 1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ π * a by positivity), Real.sqrt_nonneg (π * a),
      sq_nonneg (Real.sqrt (π * a) - 1)]
  have h1 : (2 * π * a)⁻¹ * Real.sqrt (π * a) ≤ (2 * π * a)⁻¹ * (π * a + 1) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : (2 * π * a)⁻¹ * (π * a + 1) ≤ 1 / a := by
    rw [inv_mul_le_iff₀ (by positivity), mul_one_div, le_div_iff₀ ha]
    have h4 : π * a + 1 ≤ 2 * π := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h4 ha.le]
  have h3 : 1 / a ≤ (6 / a) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    calc 1 / a * a ^ 2 = a := by field_simp
      _ ≤ 6 ^ 2 := by nlinarith
  have h6 : 0 ≤ 6 / a := by positivity
  nlinarith [pow_le_pow_left₀ h6 hY 2]

/-- The arithmetic of the `L²` witness bound. -/
theorem near_L2_arith {L I e₁ C₁ ι τ σ Y ξ s G k : ℝ}
    (hL : L ≤ 2 * I + 2 * (ι + s * σ * G + τ) ^ 2 * k) (hI : I ≤ e₁) (he₁ : 0 ≤ e₁) (hC₁ : 1 ≤ C₁)
    (hY0 : 0 ≤ Y) (hι : C₁ * e₁ * (1 + Y) ^ 2 ≤ ξ ^ 2) (hιd : ι ^ 2 = C₁ * e₁) (hι0 : 0 ≤ ι)
    (hτ0 : 0 ≤ τ) (hτ : τ ^ 2 * (1 + Y) ^ 2 ≤ ξ ^ 2) (hσ0 : 0 ≤ σ) (hσY : σ * Y ≤ ξ)
    (hs : 0 ≤ s) (hG : 0 ≤ G) (hk : k ≤ Y ^ 2) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    L ≤ ξ ^ 2 * (2 + 2 * (2 + s * G) ^ 2) := by
  have h1Y : 1 ≤ (1 + Y) ^ 2 := one_le_pow₀ (by linarith only [hY0])
  have he1ξ : e₁ ≤ ξ ^ 2 := by
    calc e₁ = 1 * e₁ * 1 := by ring
      _ ≤ C₁ * e₁ * (1 + Y) ^ 2 := by gcongr
      _ ≤ ξ ^ 2 := hι
  have hι2 : ι ^ 2 * (1 + Y) ^ 2 ≤ ξ ^ 2 := by rw [hιd]; exact hι
  obtain ⟨-, hιY, -⟩ := small_of_sq_mul_le hι0 hY0 hξ0 hξ1 hι2
  obtain ⟨-, hτY, -⟩ := small_of_sq_mul_le hτ0 hY0 hξ0 hξ1 hτ
  have hS : 0 ≤ s * G := mul_nonneg hs hG
  have hM0 : 0 ≤ ι + s * σ * G + τ := by
    have : 0 ≤ s * σ * G := mul_nonneg (mul_nonneg hs hσ0) hG
    linarith only [this, hι0, hτ0]
  have hSσ : s * G * (σ * Y) ≤ s * G * ξ := mul_le_mul_of_nonneg_left hσY hS
  have hMY : (ι + s * σ * G + τ) * Y ≤ ξ * (2 + s * G) := by
    have e : (ι + s * σ * G + τ) * Y = ι * Y + s * G * (σ * Y) + τ * Y := by ring
    rw [e]
    linarith only [hιY, hτY, hSσ]
  have hMk : (ι + s * σ * G + τ) ^ 2 * k ≤ (ξ * (2 + s * G)) ^ 2 := by
    calc (ι + s * σ * G + τ) ^ 2 * k ≤ (ι + s * σ * G + τ) ^ 2 * Y ^ 2 :=
          mul_le_mul_of_nonneg_left hk (sq_nonneg _)
      _ = ((ι + s * σ * G + τ) * Y) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hM0 hY0) hMY 2
  have e2 : ξ ^ 2 * (2 + 2 * (2 + s * G) ^ 2) = 2 * ξ ^ 2 + 2 * (ξ * (2 + s * G)) ^ 2 := by ring
  rw [e2]
  linarith only [hL, hI, he1ξ, hMk]

/-- The `L²` distance from the corrected witness to the smoothed source is `O(ξ²)`. -/
theorem near_L2_of_small {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (he1 : witnessE1 u a θ n ≤ 1)
    (hι : 2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hτ : (4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a)))) ^ 2 *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hσY : σ * (4 * (1 / (2 * a)) * (2 * n + 3)) ≤ ξ) {P₀ : ℝ[X]}
    (hP₀ : heatPolyR a P₀ = truncHeatPoly u hu hcpt ha (2 * n + 1)) :
    ∫ x, (heatTest a (P₀ - C (P₀.eval (-1 / 4))) x - heatSmooth a u x) ^ 2 ≤
      ξ ^ 2 * (2 + 2 * (2 + Real.sqrt (heatStripConstant X) * witnessG u B X) ^ 2) := by
  obtain ⟨hI, hM⟩ := witness_aux_bounds hu hcpt hsupp hB ha ha16 n hX1 hXA hθ0 hθ1 hN hk hσ0 hσ he1
  have hc := (poleCorrected_near_smoothed_of_eq hu hcpt hsupp heven hpole ha ha16 n hP₀).1
  have hY6 : 6 / a ≤ 4 * (1 / (2 * a)) * (2 * (n : ℝ) + 3) := by
    rw [show 4 * (1 / (2 * a)) * (2 * (n : ℝ) + 3) = (4 * n + 6) / a by field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) n]) ha.le
  have he10 : 0 ≤ witnessE1 u a θ n :=
    witnessE1_nonneg u (heatHermiteScale_pos ha).le (mul_nonneg hθ0 (Real.exp_pos _).le)
      (sub_nonneg.2 hθ1.le) n
  have hC₁1 : 1 ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le one_le_two (Real.one_le_exp zero_le_one))
      (by linarith [Real.pi_gt_three])) (Real.one_le_exp (sq_nonneg X))
  have hU₁ : 0 ≤ ∫ t, |u t| := integral_nonneg fun _ => abs_nonneg _
  have hL := integral_sq_corrected_sub_le hu hcpt hsupp hB ha ha16 n hP₀ (hc.trans hM)
  exact near_L2_arith hL hI he10 hC₁1 ((by positivity : (0 : ℝ) ≤ 6 / a).trans hY6) hι
    (Real.sq_sqrt (mul_nonneg (by linarith) he10)) (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hU₁) (Real.exp_pos _).le) hτ hσ0 hσY
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (gaussHeatKernel_sq_mass_le ha
      (by linarith) hY6) hξ0 hξ1

/-- **The witness at one heat time, with energy and `L²` control.** -/
theorem exists_poleHyperplane_near_of_small {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) (n : ℕ) {X : ℝ} (hX1 : 1 ≤ X)
    (hXA : 2 * A ≤ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hN : π * (A / heatHermiteScale a) ^ 2 ≤ θ * (2 * n + 1 : ℕ)) {k : ℕ}
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : heatMomentRatio (n + 1) k a X ^ k = σ ^ 2) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (he1 : witnessE1 u a θ n ≤ 1)
    (hι : 2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hτ : (4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a)))) ^ 2 *
      (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2)
    (hσξ : σ ≤ ξ) (hσY : σ * (4 * (1 / (2 * a)) * (2 * n + 3)) ≤ ξ) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      ‖heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤ ξ * witnessConst u B X ∧
      ∫ x, (heatTest a P x - heatSmooth a u x) ^ 2 ≤
        ξ ^ 2 * (2 + 2 * (2 + Real.sqrt (heatStripConstant X) * witnessG u B X) ^ 2) := by
  set Q := truncHeatPoly u hu hcpt ha (2 * n + 1) with hQ_def
  have hQe : Q.comp (-Polynomial.X) = Q := truncHeatPoly_comp_neg u hu hcpt heven ha _
  have hQd : Q.natDegree ≤ 2 * n := (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  obtain ⟨P₀, hP₀d, hP₀⟩ := exists_heatPolyR_eq ha n Q hQe hQd
  refine ⟨P₀ - C (P₀.eval (-1 / 4)), (natDegree_sub_C.le).trans hP₀d,
    by rw [eval_sub, eval_C, sub_self], ?_, ?_⟩
  · refine (poleCorrected_err_le_of_eq hu hcpt hsupp heven hpole hB ha ha16 n hX1 hXA hθ0 hθ1 hN
      hk hσ0 hσ he1 hP₀).trans ?_
    have hY0 : 0 ≤ 4 * (1 / (2 * a)) * (2 * (n : ℝ) + 3) :=
      mul_nonneg (mul_nonneg (by norm_num) (one_div_nonneg.2 (mul_pos two_pos ha).le))
        (by positivity)
    have he10 : 0 ≤ witnessE1 u a θ n :=
      witnessE1_nonneg u (heatHermiteScale_pos ha).le (mul_nonneg hθ0 (Real.exp_pos _).le)
        (sub_nonneg.2 hθ1.le) n
    have hC₁ : 0 ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) := by positivity
    have hι2 : Real.sqrt (2 * Real.exp 1 * π * Real.exp (X ^ 2) * witnessE1 u a θ n) ^ 2 *
        (1 + 4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 ≤ ξ ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg hC₁ he10)]; exact hι
    have hU₁ : 0 ≤ ∫ t, |u t| := integral_nonneg fun _ => abs_nonneg _
    obtain ⟨hι1, hι2', hι3⟩ := small_of_sq_mul_le (Real.sqrt_nonneg _) hY0 hξ0 hξ1 hι2
    obtain ⟨hτ1, hτ2', hτ3⟩ := small_of_sq_mul_le
      (mul_nonneg (mul_nonneg (by norm_num) hU₁) (Real.exp_pos _).le) hY0 hξ0 hξ1 hτ
    exact witnessErr_le (G := witnessG u B X) (E := heatStripConstant X)
      (U := stripMass (deriv (deriv u))) (S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)
      (S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (Real.sqrt_nonneg _) hσ0 hY0
      (Real.sqrt_nonneg _) (heatStripConstant_nonneg X) (stripMass_nonneg _)
      (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity) hξ1 hι1 hι2' hι3
      hτ1 hτ2' hτ3 hσξ hσY
  · exact near_L2_of_small hu hcpt hsupp heven hpole hB ha ha16 n hX1 hXA hθ0 hθ1 hN hk hσ0 hσ hξ0 hξ1 he1 hι
      hτ hσY hP₀

/-- **The near witness at level `n`**, heat time `K/n`. -/
theorem exists_poleHyperplane_near_at_level {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {K : ℝ} (hK0 : 0 < K) {X : ℝ} (hX1 : 1 ≤ X) (hXA : 2 * A ≤ X)
    {θ : ℝ} (hθ : θ = A ^ 2 / (4 * K)) (hθ1 : θ < 1) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 2)
    {m n : ℕ}
    (hn1 : 16 * K < n)
    (hn2 : ∀ a : ℝ, 0 < a → a ≤ 2 * K / ((n + 1 : ℕ) : ℝ) → a < 1 ∧
      heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) a X ^ ((n + 1) / m + 1) ≤ ξ ∧
      heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) a X ^ ((n + 1) / m + 1) *
        (4 * (1 / (2 * a)) * (2 * ((n + 1 : ℕ) : ℝ) + 1)) ≤ ξ)
    (hn3 : witnessTruncConst u K X θ * (((n : ℝ) + 1) ^ 5 * (θ * Real.exp (1 - θ)) ^ n) ≤
      min (ξ ^ 2) 1)
    (hn4 : 16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2 *
      (((n : ℝ) + 1) ^ 4 * Real.exp (-(X ^ 2 / (32 * K))) ^ n) ≤ ξ ^ 2) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      ‖heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤ ξ * witnessConst u B X ∧
      ∫ x, (heatTest (K / n) P x - heatSmooth (K / n) u x) ^ 2 ≤
        ξ ^ 2 * (2 + 2 * (2 + Real.sqrt (heatStripConstant X) * witnessG u B X) ^ 2) := by
  have hn' : (0 : ℝ) < n := (mul_pos (by norm_num) hK0).trans hn1
  have hnpos : 0 < n := by exact_mod_cast hn'
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have ha : 0 < K / n := div_pos hK0 hn'
  have ha16 : K / n ≤ 1 / 16 := by
    rw [div_le_iff₀ hn']; linarith only [hn1]
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hρ0 : 0 ≤ θ * Real.exp (1 - θ) := mul_nonneg hθ0 (Real.exp_pos _).le
  have hN : π * (A / heatHermiteScale (K / n)) ^ 2 ≤ θ * ((2 * n + 1 : ℕ) : ℝ) := by
    have e : π * (A / heatHermiteScale (K / n)) ^ 2 = θ * (2 * n) := by
      rw [div_pow, heatHermiteScale_sq ha, hθ]
      field_simp
      ring
    rw [e]
    push_cast
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hθ0
  have ha2 : K / n ≤ 2 * K / ((n + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hn' (by positivity)]
    push_cast
    linarith only [mul_le_mul_of_nonneg_left hn1' hK0.le]
  obtain ⟨ha1, hσδ, hσY⟩ := hn2 (K / n) ha ha2
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hσ0 : 0 ≤ heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ ((n + 1) / m + 1) :=
    pow_nonneg (heatMomentRatio_pos ha ha1 hX0).le _
  have hσsq : heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ (2 * ((n + 1) / m + 1)) =
      (heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ ((n + 1) / m + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm ((n + 1) / m + 1) 2]
  have hk : heatMomentRatio (n + 1) (2 * ((n + 1) / m + 1)) (K / n) X ^ (2 * ((n + 1) / m + 1)) ≤
      1 / 2 := by
    rw [hσsq]
    calc _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hσ0 (hσδ.trans hξ1) 2
      _ ≤ 1 / 2 := by norm_num
  have hY : 4 * (1 / (2 * (K / n))) * (2 * ((n + 1 : ℕ) : ℝ) + 1) =
      4 * (1 / (2 * (K / n))) * (2 * n + 3) := by
    push_cast; ring
  rw [hY] at hσY
  have hYb := one_add_Y_sq_le hK0 n
  obtain ⟨he1, hι⟩ := witness_trunc_small (C := 2 * Real.exp 1 * π * Real.exp (X ^ 2))
    (witnessE1_le u hK0 hθ0 hθ1 hnpos) hYb
    (by
      unfold witnessTruncD
      have : 0 < 1 - θ := sub_pos.2 hθ1
      positivity)
    (by positivity) hρ0 hn3
  have hr₀ : 0 ≤ Real.exp (-(X ^ 2 / (32 * K))) := (Real.exp_pos _).le
  have hr₁ : Real.exp (-(X ^ 2 / (32 * K))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hτ := witness_tail_small hr₀ hr₁ hYb hn4
  have hτu_eq : Real.exp (-(X ^ 2 / (32 * K))) ^ n = Real.exp (-(X ^ 2 / (32 * (K / n)))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hτu_eq] at hτ
  exact exists_poleHyperplane_near_of_small hu hcpt hsupp heven hpole hB ha ha16 n hX1 hXA hθ0 hθ1
    hN hk hσ0 hσsq hξ0.le (hξ1.trans (by norm_num)) he1 hι hτ hσδ hσY

/-! ## The spectral dictionary -/

theorem integrable_sq_sub_of_sq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf2 : Integrable (fun x => f x ^ 2)) (hg2 : Integrable (fun x => g x ^ 2)) :
    Integrable (fun x => (f x - g x) ^ 2) := by
  refine ((hf2.add hg2).const_mul 2).mono' ((hf.sub hg).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (f x + g x)]

/-- `∫ (f − h)² ≤ 2 ∫ (f − g)² + 2 ∫ (g − h)²`. -/
theorem integral_sq_sub_le_two {f g h : ℝ → ℝ} (h1 : Integrable (fun x => (f x - g x) ^ 2))
    (h2 : Integrable (fun x => (g x - h x) ^ 2)) :
    ∫ x, (f x - h x) ^ 2 ≤ 2 * (∫ x, (f x - g x) ^ 2) + 2 * ∫ x, (g x - h x) ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul 2) (h2.const_mul 2)]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    ((h1.const_mul 2).add (h2.const_mul 2)) (Filter.Eventually.of_forall fun x => ?_)
  simp only
  nlinarith [sq_nonneg (f x - 2 * g x + h x)]

theorem integrable_sq_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) : Integrable (fun x => u x ^ 2) := by
  have h2 : HasCompactSupport (fun x => u x ^ 2) := by
    simpa [Function.comp_def] using hcpt.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact (hu.continuous.pow 2).integrable_of_hasCompactSupport h2

/-- `∫ (u_{K/n} − u)² → 0`. -/
theorem tendsto_integral_sq_heatSmooth_window_sub {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0) {K : ℝ}
    (hK : 0 < K) :
    Tendsto (fun n : ℕ => ∫ x, (heatSmooth (K / n) u x - u x) ^ 2) atTop (𝓝 0) := by
  have ha : ∀ n : ℕ, 0 < K / ((n : ℝ) + 1) := fun n => div_pos hK (by positivity)
  have ha0 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat K |>.comp (tendsto_add_atTop_nat 1) |>.congr
      fun n => by simp
  have h := tendsto_integral_sq_heatSmooth_sub hu hcpt hsupp ha ha0
  refine (tendsto_add_atTop_iff_nat 1).1 (h.congr fun n => ?_)
  simp only [Nat.cast_add, Nat.cast_one]

/-- The arithmetic closing the spectral dictionary at one level. -/
theorem dictionary_level_arith {h zε l1 l2 ξ C D ε : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hε : 0 < ε) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hξ : ξ * (C + D + 1) ≤ ε / 4)
    (hh : h ≤ ξ * C) (hz : zε < ε / 2) (hl1 : l1 ≤ ξ ^ 2 * D) (hl2 : l2 < ε / 8) :
    h + zε < ε ∧ 2 * l1 + 2 * l2 < ε := by
  have hξξ : ξ ^ 2 ≤ ξ := by rw [sq]; exact mul_le_of_le_one_left hξ0 hξ1
  have h1 : ξ * C ≤ ε / 4 := by nlinarith [mul_nonneg hξ0 hD]
  have h2 : ξ * D ≤ ε / 4 := by nlinarith [mul_nonneg hξ0 hC]
  have h3 : ξ ^ 2 * D ≤ ξ * D := mul_le_mul_of_nonneg_right hξξ hD
  constructor <;> linarith

/-- **The HCF spectral dictionary.**  For a smooth even pole-vanishing source `u` of half-width
`A` and every window `K > A²/4`, the pole hyperplane at heat time `K/n` carries, for all large `n`,
a polynomial whose heat Hankel energy is `ε`-close to the even Weil energy `Σ F_u(z_q)²` of `u`
and whose physical heat test is `ε`-close to `u` in `L²`. -/
theorem eventually_exists_poleHyperplane_near_source {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {A : ℝ}
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (heven : ∀ x, u (-x) = u x)
    (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {K : ℝ} (hK0 : 0 < K) (hK : A ^ 2 < 4 * K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      ‖heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ < ε ∧
      ∫ x, (heatTest (K / n) P x - u x) ^ 2 < ε := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∑' q : XiZeroCopy,
      heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuous hu.continuous
  have hB' : ∀ t, |u t| ≤ B := fun t => by rw [← Real.norm_eq_abs]; exact hB t
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 2 * |A| + 3 * Real.sqrt K + 1 := ⟨_, rfl⟩
  have hsK := Real.sqrt_nonneg K
  have hsK2 := Real.sq_sqrt hK0.le
  have hA0 := abs_nonneg A
  have hX1 : 1 ≤ X := by rw [hX]; linarith only [hsK, hA0]
  have hXA : 2 * A ≤ X := by rw [hX]; linarith only [hsK, le_abs_self A]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hX8 : 4 * (2 * K) < X ^ 2 := by
    have h3 : 3 * Real.sqrt K < X := by rw [hX]; linarith only [hA0]
    have h2 : (3 * Real.sqrt K) ^ 2 < X ^ 2 :=
      pow_lt_pow_left₀ h3 (mul_nonneg (by norm_num) hsK) two_ne_zero
    rw [mul_pow, hsK2] at h2
    linarith only [h2, hK0]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = A ^ 2 / (4 * K) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; exact hK
  have hρ0 : 0 ≤ θ * Real.exp (1 - θ) := mul_nonneg hθ0 (Real.exp_pos _).le
  have hρ1 : θ * Real.exp (1 - θ) < 1 := GaloisForLFunctions.mul_exp_one_sub_lt_one hθ0 hθ1
  have hC₀0 := witnessConst_nonneg u B X
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = 2 + 2 * (2 + Real.sqrt (heatStripConstant X) * witnessG u B X) ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = min (1 / 2) (ε / (4 * (witnessConst u B X + D + 1))) :=
    ⟨_, rfl⟩
  have hden : 0 < 4 * (witnessConst u B X + D + 1) := by linarith only [hC₀0, hD0]
  have hξ0 : 0 < ξ := by rw [hξ]; exact lt_min (by norm_num) (div_pos hε hden)
  have hξ1 : ξ ≤ 1 / 2 := by rw [hξ]; exact min_le_left _ _
  have hξε : ξ * (witnessConst u B X + D + 1) ≤ ε / 4 := by
    have h1 : ξ ≤ ε / (4 * (witnessConst u B X + D + 1)) := by rw [hξ]; exact min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith only [hC₀0, hD0] :
      (0 : ℝ) ≤ witnessConst u B X + D + 1)
    calc ξ * (witnessConst u B X + D + 1)
        ≤ ε / (4 * (witnessConst u B X + D + 1)) * (witnessConst u B X + D + 1) := h2
      _ = ε / 4 := by field_simp
  obtain ⟨m, -, hmom⟩ := exists_heatMomentOrder (K := 2 * K) (L := X) (by positivity) hX0 hX8
  have hmom' := (tendsto_add_atTop_nat 1).eventually (hmom ξ hξ0)
  have hdec1 := (tendsto_succ_pow_mul_pow hρ0 hρ1 5).const_mul (witnessTruncConst u K X θ)
  rw [mul_zero] at hdec1
  have hr₀ : 0 ≤ Real.exp (-(X ^ 2 / (32 * K))) := (Real.exp_pos _).le
  have hr₁ : Real.exp (-(X ^ 2 / (32 * K))) < 1 :=
    (Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))).trans_eq Real.exp_zero
  have hdec2 := (tendsto_succ_pow_mul_pow hr₀ hr₁ 4).const_mul
    (16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2)
  rw [mul_zero] at hdec2
  have hconv := tendsto_tsum_heatSmooth_sq hu hcpt hK0
  rw [← hZ] at hconv
  have hε2 : 0 < ε / 2 := by linarith only [hε]
  have hε8 : 0 < ε / 8 := by linarith only [hε]
  have hev5 : ∀ᶠ n : ℕ in atTop, ‖(∑' q : XiZeroCopy, heatStripTransform
      (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) - Z‖ < ε / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hconv).eventually (gt_mem_nhds hε2)
  have hev6 : ∀ᶠ n : ℕ in atTop, ∫ x, (heatSmooth (K / n) u x - u x) ^ 2 < ε / 8 :=
    (tendsto_integral_sq_heatSmooth_window_sub hu hcpt hsupp hK0).eventually (gt_mem_nhds hε8)
  have hev1 : ∀ᶠ n : ℕ in atTop, 16 * K < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  have hev3 : ∀ᶠ n : ℕ in atTop, witnessTruncConst u K X θ *
      (((n : ℝ) + 1) ^ 5 * (θ * Real.exp (1 - θ)) ^ n) ≤ min (ξ ^ 2) 1 :=
    hdec1.eventually (ge_mem_nhds (lt_min (pow_pos hξ0 2) one_pos))
  have hev4 : ∀ᶠ n : ℕ in atTop, 16 * (∫ t, |u t|) ^ 2 * (1 + 6 / K) ^ 2 *
      (((n : ℝ) + 1) ^ 4 * Real.exp (-(X ^ 2 / (32 * K))) ^ n) ≤ ξ ^ 2 :=
    hdec2.eventually (ge_mem_nhds (pow_pos hξ0 2))
  filter_upwards [hev1, hmom', hev5, hev3, hev4, hev6] with n hn1 hn2 hn5 hn3 hn4 hn6
  obtain ⟨P, hPd, hPe, hH, hL⟩ := exists_poleHyperplane_near_at_level hu hcpt hsupp heven hpole hB'
    hK0 hX1 hXA hθ hθ1 hξ0 hξ1 hn1 hn2 hn3 hn4
  rw [← hD] at hL
  refine ⟨P, hPd, hPe, ?_⟩
  have hn' : (0 : ℝ) < n := (mul_pos (by norm_num) hK0).trans hn1
  have ha : 0 < K / n := div_pos hK0 hn'
  have ha16 : K / n ≤ 1 / 16 := by rw [div_le_iff₀ hn']; linarith only [hn1]
  have hβ : 1 / 2 < 1 / (2 * (K / n)) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  obtain ⟨hua2, -⟩ := integral_heatSmooth_sq_le hu hcpt hsupp ha ha16 hB'
  have hg2 : Integrable (fun x => heatTest (K / n) P x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ (by linarith)
  have hI1 := integrable_sq_sub_of_sq (continuous_gaussPolyFun _ _)
    (continuous_heatSmooth hu hcpt ha) hg2 hua2
  have hI2 := integrable_sq_sub_of_sq (continuous_heatSmooth hu hcpt ha) hu.continuous hua2
    (integrable_sq_of_contDiff hu hcpt)
  have htri := integral_sq_sub_le_two hI1 hI2
  have hnorm : ‖heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) - Z‖ ≤
      ‖heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ +
        ‖(∑' q : XiZeroCopy, heatStripTransform
          (fun x => ((heatSmooth (K / n) u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2) - Z‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  obtain ⟨h1, h2⟩ := dictionary_level_arith hC₀0 hD0 hε hξ0.le (hξ1.trans (by norm_num)) hξε hH
    hn5 hL hn6
  exact ⟨hnorm.trans_lt h1, htri.trans_lt h2⟩

/-- `|∫ f² − ∫ g²| ≤ (1 + 1/t) ∫ (f − g)² + t ∫ g²` for `t > 0`. -/
theorem abs_integral_sq_sub_le {f g : ℝ → ℝ} (hfg : Integrable (fun x => (f x - g x) ^ 2))
    (hf : Integrable (fun x => f x ^ 2)) (hg : Integrable (fun x => g x ^ 2)) {t : ℝ}
    (ht : 0 < t) :
    |(∫ x, f x ^ 2) - ∫ x, g x ^ 2| ≤ (1 + 1 / t) * (∫ x, (f x - g x) ^ 2) + t * ∫ x, g x ^ 2 := by
  have hR : Integrable (fun x => (1 + 1 / t) * (f x - g x) ^ 2 + t * g x ^ 2) :=
    (hfg.const_mul _).add (hg.const_mul _)
  have hpt : ∀ x, |f x ^ 2 - g x ^ 2| ≤ (1 + 1 / t) * (f x - g x) ^ 2 + t * g x ^ 2 := fun x => by
    have h1 : 2 * |g x * (f x - g x)| ≤ t * g x ^ 2 + 1 / t * (f x - g x) ^ 2 := by
      have key : 2 * t * (|g x| * |f x - g x|) ≤ t ^ 2 * g x ^ 2 + (f x - g x) ^ 2 := by
        nlinarith [sq_nonneg (t * |g x| - |f x - g x|), sq_abs (g x), sq_abs (f x - g x)]
      have h2 : t * (2 * |g x * (f x - g x)|) ≤ t * (t * g x ^ 2 + 1 / t * (f x - g x) ^ 2) := by
        have e : t * (t * g x ^ 2 + 1 / t * (f x - g x) ^ 2) = t ^ 2 * g x ^ 2 + (f x - g x) ^ 2 := by
          field_simp
        rw [e, abs_mul]
        linarith only [key]
      exact le_of_mul_le_mul_left h2 ht
    have e2 : f x ^ 2 - g x ^ 2 = (f x - g x) ^ 2 + 2 * (g x * (f x - g x)) := by ring
    rw [e2, abs_le]
    have h3 := abs_le.1 (le_refl |g x * (f x - g x)|)
    have h4 := neg_abs_le (g x * (f x - g x))
    have h5 := le_abs_self (g x * (f x - g x))
    have h6 : 0 ≤ (f x - g x) ^ 2 := sq_nonneg _
    have h7 : 0 ≤ 1 / t * (f x - g x) ^ 2 := by positivity
    constructor <;> nlinarith
  rw [← integral_sub hf hg, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hfg.const_mul _) (hg.const_mul _)]
  calc |∫ x, (f x ^ 2 - g x ^ 2)| ≤ ∫ x, |f x ^ 2 - g x ^ 2| := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hR
        (Filter.Eventually.of_forall hpt)

/-- The arithmetic of the Rayleigh comparison. -/
theorem rayleigh_arith {h q G N l ε δ₁ δ₂ : ℝ} (hN : 0 < N) (hε : 0 < ε) (hq : q = l * N)
    (hh : h < q + δ₁) (hG : |G - N| < δ₂) (hδ₁ : δ₁ = ε * N / 2)
    (hδ₂ : δ₂ * (|l| + ε + 1) ≤ ε * N / 2) (hδ₂N : δ₂ ≤ N / 2) :
    0 < G ∧ h < (l + ε) * G := by
  have hδ₂0 : 0 < δ₂ := (abs_nonneg _).trans_lt hG
  have hGN := abs_lt.1 hG
  refine ⟨by linarith only [hGN.1, hδ₂N, hN], ?_⟩
  have h1 : |(l + ε) * (G - N)| ≤ (|l| + ε) * δ₂ := by
    rw [abs_mul]
    refine mul_le_mul ((abs_add_le _ _).trans (by rw [abs_of_pos hε])) hG.le (abs_nonneg _)
      (by positivity)
  have h2 := neg_abs_le ((l + ε) * (G - N))
  have e : (l + ε) * G = l * N + ε * N + (l + ε) * (G - N) := by ring
  have h3 : (|l| + ε) * δ₂ = δ₂ * (|l| + ε + 1) - δ₂ := by ring
  rw [e]
  linarith only [hh, hq, hδ₁, hδ₂, h1, h2, h3, hδ₂0]

/-- **Rayleigh form of the dictionary.**  The ground energy of the heat Hankel form on the pole
hyperplane at heat time `K/n`, normalised by `∫ g_P²`, is eventually below
`Re Σ F_u(z_q)² / ∫ u² + ε` for every smooth even pole-vanishing source of half-width
`A < 2√K`. -/
theorem eventually_exists_poleHyperplane_rayleigh_lt {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {A : ℝ}
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (heven : ∀ x, u (-x) = u x)
    (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {K : ℝ} (hK0 : 0 < K) (hK : A ^ 2 < 4 * K)
    (hN : 0 < ∫ x, u x ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      0 < ∫ x, heatTest (K / n) P x ^ 2 ∧
      (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re <
        ((∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
          (xiSpectralPoint q) ^ 2).re / (∫ x, u x ^ 2) + ε) * ∫ x, heatTest (K / n) P x ^ 2 := by
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = ∫ x, u x ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∑' q : XiZeroCopy,
      heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 := ⟨_, rfl⟩
  rw [← hNd] at hN ⊢
  rw [← hZ]
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Z.re / N := ⟨_, rfl⟩
  rw [← hl]
  have hq : Z.re = l * N := by rw [hl]; field_simp
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂ : ℝ, δ₂ = min (N / 2) (ε * N / (2 * (|l| + ε + 1))) := ⟨_, rfl⟩
  have hl1 : 0 < |l| + ε + 1 := by positivity
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; exact lt_min (by positivity) (by positivity)
  have hδ₂N : δ₂ ≤ N / 2 := by rw [hδ₂]; exact min_le_left _ _
  have hδ₂l : δ₂ * (|l| + ε + 1) ≤ ε * N / 2 := by
    have h1 : δ₂ ≤ ε * N / (2 * (|l| + ε + 1)) := by rw [hδ₂]; exact min_le_right _ _
    calc δ₂ * (|l| + ε + 1) ≤ ε * N / (2 * (|l| + ε + 1)) * (|l| + ε + 1) :=
          mul_le_mul_of_nonneg_right h1 hl1.le
      _ = ε * N / 2 := by field_simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ₂ / (2 * (N + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have htN : t * N < δ₂ / 2 := by
    rw [ht, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min (ε * N / 2) (δ₂ * t / (2 * (1 + t))) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; exact lt_min (by positivity) (by positivity)
  have hδ'1 : δ' ≤ ε * N / 2 := by rw [hδ']; exact min_le_left _ _
  have hδ'2 : (1 + 1 / t) * δ' ≤ δ₂ / 2 := by
    have h1 : δ' ≤ δ₂ * t / (2 * (1 + t)) := by rw [hδ']; exact min_le_right _ _
    calc (1 + 1 / t) * δ' ≤ (1 + 1 / t) * (δ₂ * t / (2 * (1 + t))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ₂ / 2 := by field_simp; ring
  filter_upwards [eventually_exists_poleHyperplane_near_source hu hcpt hsupp heven hpole hK0 hK
    hδ'0, tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)] with n hn hn0
  obtain ⟨P, hPd, hPe, hH, hL⟩ := hn
  rw [← hZ] at hH
  have ha : 0 < K / n := div_pos hK0 hn0
  have hβ : 0 < 1 / (2 * (K / n)) := by positivity
  have hg2 : Integrable (fun x => heatTest (K / n) P x ^ 2) :=
    GaloisForLFunctions.integrable_gaussPolyFun_sq _ hβ
  have hu2 := integrable_sq_of_contDiff hu hcpt
  have hI : Integrable (fun x => (heatTest (K / n) P x - u x) ^ 2) :=
    integrable_sq_sub_of_sq (continuous_gaussPolyFun _ _) hu.continuous hg2 hu2
  have habs := abs_integral_sq_sub_le (f := heatTest (K / n) P) hI hg2 hu2 ht0
  rw [← hNd] at habs
  have hG : |(∫ x, heatTest (K / n) P x ^ 2) - N| < δ₂ := by
    have h1 : (1 + 1 / t) * (∫ x, (heatTest (K / n) P x - u x) ^ 2) < (1 + 1 / t) * δ' :=
      mul_lt_mul_of_pos_left hL (by positivity)
    linarith only [habs, h1, hδ'2, htN]
  have hre : (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re <
      Z.re + ε * N / 2 := by
    have h1 := Complex.re_le_norm
      (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) - Z)
    rw [Complex.sub_re] at h1
    linarith only [h1, hH, hδ'1]
  obtain ⟨hG0, hlt⟩ := rayleigh_arith hN hε hq hre hG rfl hδ₂l hδ₂N
  exact ⟨P, hPd, hPe, hG0, hlt⟩

end

end RHTower
