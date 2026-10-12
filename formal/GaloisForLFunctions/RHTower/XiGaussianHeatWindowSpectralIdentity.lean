import GaloisForLFunctions.RHTower.XiGaussianHeatWindowConditioning

/-!
# The HCF spectral identity: heat windows compute the even Weil ground energy

Call `μ` an *even Weil floor* at half-width `A` if `μ ∫u² ≤ Re Σ_q F_u(z_q)²` for every smooth
even real source `u` vanishing outside `[−A, A]` with `∫ u e^{x/2} = 0`.  Every real `μ` is
allowed: no sign is assumed, so the statement is unconditional.

**Lower bound** (`eventually_le_re_heatHankel_of_evenWeilFloor`).  If `μ` is an even Weil floor at
`A` and `4K < A²`, then for every `ε > 0`, for all large `n`, every `0 < a ≤ K/n` and every
real `P` of degree `≤ n` with `P(−1/4) = 0`, `(μ − ε) ∫ g_P² ≤ Re H_a(P, P)`.  The proof
truncates the heat test `g` to `u = (g − κ)χ` with the pole correction `κ`. The comparison
`|∫u² − ∫g²| ≤ T + t∫g² + (1 + 1/t)·2B₁κ²` costs `O(σ)` relative to `∫g²`, where `σ` is the
moment ratio. The zero sums differ by the strip integration by parts error, also `O(σ)∫g²`.

With the dictionary MUST-1289 this pins the window ground energy between the even Weil floors
just outside and just inside half-width `2√K`.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly continuous_gaussPolyFun
  hasDerivAt_gaussPolyFun gaussPolyFun_neg_of_even sq_integral_abs_gaussPolyFun_mul_exp_half_le
  integrable_gaussPolyFun_sq)

namespace RHTower

noncomputable section

/-- `μ` is an even Weil floor at half-width `A`. -/
def EvenWeilFloor (A μ : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → (∀ t : ℝ, A < |t| → u t = 0) →
    (∀ x, u (-x) = u x) → ∫ x, u x * Real.exp (x / 2) = 0 →
      μ * ∫ x, u x ^ 2 ≤
        (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2).re

variable {B₀ B₁ : ℝ}

/-- **The comparison with an even Weil floor.** -/
theorem mul_integral_heatSource_sq_le_re_heatHankel {A μ : ℝ} (hfloor : EvenWeilFloor A μ)
    (h0 : 0 < B₀) (h01 : B₀ < B₁) (h1A : B₁ < A) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (P : ℝ[X])
    {C : ℝ} (hC : ∀ x, |deriv (heatCutoff B₀ B₁) x| ≤ C) :
    μ * ∫ x, heatSource a P B₀ B₁ x ^ 2 ≤
      (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re +
        (2 * (∫ x, |heatTestDeriv a P x| * Real.exp (|x| / 2)) *
            (stripMassOn (heatTestDeriv a P) (heatTailSet B₀) +
              C * stripMassOn (heatTest a P) (heatTailSet B₀) +
              |heatPoleCorrection a P B₀ B₁| *
                ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2)) +
          (stripMassOn (heatTestDeriv a P) (heatTailSet B₀) +
              C * stripMassOn (heatTest a P) (heatTailSet B₀) +
              |heatPoleCorrection a P B₀ B₁| *
                ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2)) ^ 2) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  set κ := heatPoleCorrection a P B₀ B₁ with hκ
  set g := heatTest a P with hg_def
  set g' := heatTestDeriv a P with hg'_def
  set χ := heatCutoff B₀ B₁ with hχ_def
  set χ' := deriv (heatCutoff B₀ B₁) with hχ'_def
  set u := heatSource a P B₀ B₁ with hu_def
  set M := ∫ x, |g' x| * Real.exp (|x| / 2) with hM_def
  set ρ := stripMassOn g' (heatTailSet B₀) + C * stripMassOn g (heatTailSet B₀) +
    |κ| * ∫ x, |χ' x| * Real.exp (|x| / 2) with hρ_def
  have hsupp : ∀ t : ℝ, A < |t| → u t = 0 := fun t ht => by
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have h := tsupport_heatSource_subset h0.le h01 a P hm
    have : |t| ≤ B₁ := abs_le.2 ⟨h.1, h.2⟩
    linarith
  have hpole : ∫ x, u x * Real.exp (x / 2) = 0 := by
    rw [← integral_exp_half_mul_heatSource h0 h01 a P]
    congr 1; funext x; ring
  -- the Weil floor
  have hfl := hfloor u (contDiff_heatSource a P) (hasCompactSupport_heatSource h0.le h01 a P) hsupp
    (heatSource_neg a P) hpole
  -- derivatives and integrability
  have hgd : ∀ x, HasDerivAt g (g' x) x := hasDerivAt_heatTest a P
  have hχd : ∀ x, HasDerivAt χ (χ' x) x := fun x => hasDerivAt_heatCutoff x
  have hud : ∀ x, HasDerivAt u (g' x * χ x + (g x - κ) * χ' x) x := fun x =>
    ((hgd x).sub_const κ).mul (hχd x)
  have hgc : Continuous g := continuous_heatTest a P
  have hg'c : Continuous g' := continuous_heatTestDeriv a P
  have hχc : Continuous χ := continuous_heatCutoff
  have hχ'c : Continuous χ' := continuous_deriv_heatCutoff
  have hχcpt : HasCompactSupport χ := hasCompactSupport_heatCutoff h0.le h01
  have hχ'cpt : HasCompactSupport χ' := hasCompactSupport_deriv_heatCutoff h0.le h01
  have huc : Continuous u := (contDiff_heatSource a P).continuous
  have hucpt : HasCompactSupport u := hasCompactSupport_heatSource h0.le h01 a P
  have hu'c : Continuous fun x => g' x * χ x + (g x - κ) * χ' x :=
    (hg'c.mul hχc).add ((hgc.sub continuous_const).mul hχ'c)
  have hu'cpt : HasCompactSupport fun x => g' x * χ x + (g x - κ) * χ' x :=
    (hχcpt.mul_left).add (hχ'cpt.mul_left)
  have hgi := integrable_abs_heatTest_mul_exp ha ha1 P
  have hg'i := integrable_abs_heatTestDeriv_mul_exp ha ha1 P
  have hui := integrable_abs_of_compact huc hucpt
  have hu'i := integrable_abs_of_compact hu'c hu'cpt
  have hχ'i := integrable_abs_of_compact hχ'c hχ'cpt
  have hcast : ∀ {f : ℝ → ℝ}, Integrable (fun x => |f x| * Real.exp (|x| / 2)) →
      Integrable (fun x => ‖((f x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := fun h => by
    simpa only [norm_ofReal_mul_exp] using h
  -- the function h = g − u and its derivative
  set h : ℝ → ℝ := fun x => g x - u x with hh_def
  set h' : ℝ → ℝ := fun x => g' x - (g' x * χ x + (g x - κ) * χ' x) with hh'_def
  have hhd : ∀ x, HasDerivAt h (h' x) x := fun x => (hgd x).sub (hud x)
  have hhi : Integrable (fun x => |h x| * Real.exp (|x| / 2)) := by
    refine (hgi.add hui).mono' ((continuous_abs.comp (hgc.sub huc)).mul (Real.continuous_exp.comp
      (continuous_abs.div_const 2))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := abs_sub (g x) (u x)
    have he := Real.exp_pos (|x| / 2)
    simp only [Pi.add_apply]
    nlinarith
  have hh'i : Integrable (fun x => |h' x| * Real.exp (|x| / 2)) := by
    refine (hg'i.add hu'i).mono' ((continuous_abs.comp (hg'c.sub hu'c)).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := abs_sub (g' x) (g' x * χ x + (g x - κ) * χ' x)
    have he := Real.exp_pos (|x| / 2)
    simp only [Pi.add_apply]
    nlinarith
  -- strip bounds
  have hstrip : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ 1 / 2 :=
    abs_im_xiSpectralPoint_le_half
  have hG : ∀ q : XiZeroCopy, ‖xiSpectralPoint q‖ *
      ‖heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q)‖ ≤ M := fun q => by
    have := norm_mul_norm_heatStripTransform_le (f := fun x => ((g x : ℝ) : ℂ))
      (f' := fun x => ((g' x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hgc)
      (Complex.continuous_ofReal.comp hg'c) (fun x => (hgd x).ofReal_comp) (hcast hgi)
      (hcast hg'i) (hstrip q)
    simpa only [norm_ofReal_mul_exp] using this
  have hdiff : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      heatStripTransform (fun x => ((g x : ℝ) : ℂ)) z -
        heatStripTransform (fun x => ((u x : ℝ) : ℂ)) z =
      heatStripTransform (fun x => ((h x : ℝ) : ℂ)) z := fun z hz => by
    have i1 := integrable_mul_cexp_of_strip (f := fun x => ((g x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hgc) (hcast hgi) hz
    have i2 := integrable_mul_cexp_of_strip (f := fun x => ((u x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp huc) (hcast hui) hz
    unfold heatStripTransform
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    simp only [hh_def]
    push_cast
    ring
  have hpt : ∀ x, |h' x| * Real.exp (|x| / 2) ≤
      (heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
        C * (|g x| * Real.exp (|x| / 2))) x + |κ| * (|χ' x| * Real.exp (|x| / 2)) := fun x => by
    have he := Real.exp_pos (|x| / 2)
    by_cases hx : x ∈ heatTailSet B₀
    · rw [indicator_of_mem hx]
      have hχ0 := heatCutoff_nonneg (B₀ := B₀) (B₁ := B₁) x
      have hχ1 := heatCutoff_le_one (B₀ := B₀) (B₁ := B₁) x
      have hb : |h' x| ≤ |g' x| + C * |g x| + |κ| * |χ' x| := by
        have e : h' x = g' x * (1 - χ x) - g x * χ' x + κ * χ' x := by
          simp only [hh'_def]; ring
        rw [e]
        have h1 : |g' x * (1 - χ x)| ≤ |g' x| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - χ x)]
          nlinarith [abs_nonneg (g' x)]
        have h2 : |g x * χ' x| ≤ C * |g x| := by
          rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
        have h3 : |κ * χ' x| = |κ| * |χ' x| := abs_mul _ _
        have t1 := abs_sub (g' x * (1 - χ x)) (g x * χ' x)
        have t2 := abs_add_le (g' x * (1 - χ x) - g x * χ' x) (κ * χ' x)
        linarith
      nlinarith [abs_nonneg (κ), abs_nonneg (χ' x)]
    · rw [indicator_of_notMem hx]
      have hx' : |x| < B₀ := lt_of_not_ge hx
      have e : h' x = 0 := by
        simp only [hh'_def, hχ_def, hχ'_def, heatCutoff_eq_one h0.le h01 hx'.le,
          deriv_heatCutoff_eq_zero h0.le h01 hx']
        ring
      rw [e, abs_zero, zero_mul]
      positivity
  have hρbound : ∫ x, |h' x| * Real.exp (|x| / 2) ≤ ρ := by
    have hind : Integrable ((heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
        C * (|g x| * Real.exp (|x| / 2)))) :=
      (hg'i.add (hgi.const_mul C)).indicator (measurableSet_heatTailSet B₀)
    calc ∫ x, |h' x| * Real.exp (|x| / 2)
        ≤ ∫ x, ((heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
            C * (|g x| * Real.exp (|x| / 2))) x + |κ| * (|χ' x| * Real.exp (|x| / 2))) :=
          integral_mono hh'i (hind.add (hχ'i.const_mul _)) hpt
      _ = ρ := by
          rw [integral_add hind (hχ'i.const_mul _), integral_indicator (measurableSet_heatTailSet B₀),
            integral_add hg'i.integrableOn (hgi.const_mul C).integrableOn, integral_const_mul,
            integral_const_mul, hρ_def, stripMassOn, stripMassOn]
  have hR : ∀ q : XiZeroCopy, ‖xiSpectralPoint q‖ *
      ‖heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q) -
        heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q)‖ ≤ ρ := fun q => by
    rw [hdiff _ (hstrip q)]
    have := norm_mul_norm_heatStripTransform_le (f := fun x => ((h x : ℝ) : ℂ))
      (f' := fun x => ((h' x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hgc.sub huc))
      (Complex.continuous_ofReal.comp (hg'c.sub hu'c)) (fun x => (hhd x).ofReal_comp) (hcast hhi)
      (hcast hh'i) (hstrip q)
    simp only [norm_ofReal_mul_exp] at this
    exact this.trans hρbound
  have hcmp := re_tsum_sq_le_of_strip hG hR
  have hH : heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) =
      ∑' q : XiZeroCopy, heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 :=
    heatHankel_map_eq_tsum_sq ha P
  rw [← hH] at hcmp
  exact hfl.trans hcmp

/-! ## The mass of the truncation -/

theorem abs_sq_truncation_sub_le {g χ κ t : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (ht : 0 < t) :
    |((g - κ) * χ) ^ 2 - g ^ 2| ≤ g ^ 2 * (1 - χ ^ 2) + t * g ^ 2 + (1 + 1 / t) * (κ ^ 2 * χ ^ 2) := by
  have hχ2 : χ ^ 2 ≤ 1 := by nlinarith
  have hχ20 : 0 ≤ χ ^ 2 := sq_nonneg χ
  have e : ((g - κ) * χ) ^ 2 - g ^ 2 = -(g ^ 2 * (1 - χ ^ 2)) - 2 * (κ * g) * χ ^ 2 + κ ^ 2 * χ ^ 2 := by
    ring
  have hkg : 2 * |κ * g| ≤ t * g ^ 2 + κ ^ 2 / t := by
    have key : 2 * t * (|κ| * |g|) ≤ t ^ 2 * g ^ 2 + κ ^ 2 := by
      nlinarith [sq_nonneg (t * |g| - |κ|), sq_abs g, sq_abs κ]
    have h2 : t * (2 * |κ * g|) ≤ t * (t * g ^ 2 + κ ^ 2 / t) := by
      have e2 : t * (t * g ^ 2 + κ ^ 2 / t) = t ^ 2 * g ^ 2 + κ ^ 2 := by field_simp
      rw [e2, abs_mul]
      linarith only [key]
    exact le_of_mul_le_mul_left h2 ht
  have h3 : |2 * (κ * g) * χ ^ 2| ≤ t * g ^ 2 + κ ^ 2 / t * χ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hχ20, abs_two]
    have h4 : 2 * |κ * g| * χ ^ 2 ≤ (t * g ^ 2 + κ ^ 2 / t) * χ ^ 2 :=
      mul_le_mul_of_nonneg_right hkg hχ20
    have h5 : t * g ^ 2 * χ ^ 2 ≤ t * g ^ 2 := mul_le_of_le_one_right (by positivity) hχ2
    nlinarith
  have h6 : 0 ≤ g ^ 2 * (1 - χ ^ 2) := mul_nonneg (sq_nonneg g) (by linarith)
  rw [e]
  have t1 := abs_add_le (-(g ^ 2 * (1 - χ ^ 2)) - 2 * (κ * g) * χ ^ 2) (κ ^ 2 * χ ^ 2)
  have t2 := abs_sub (-(g ^ 2 * (1 - χ ^ 2))) (2 * (κ * g) * χ ^ 2)
  rw [abs_neg, abs_of_nonneg h6] at t2
  rw [abs_of_nonneg (by positivity : 0 ≤ κ ^ 2 * χ ^ 2)] at t1
  have e3 : (1 + 1 / t) * (κ ^ 2 * χ ^ 2) = κ ^ 2 * χ ^ 2 + κ ^ 2 / t * χ ^ 2 := by ring
  linarith

/-- **The truncation keeps the mass.**
`|∫u² − ∫g²| ≤ ∫_{|x| ≥ B₀} g² + t∫g² + (1 + 1/t)·2B₁κ²`. -/
theorem abs_integral_heatSource_sq_sub_le (h0 : 0 < B₀) (h01 : B₀ < B₁) {a : ℝ} (ha : 0 < a)
    (P : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    |(∫ x, heatSource a P B₀ B₁ x ^ 2) - ∫ x, heatTest a P x ^ 2| ≤
      (∫ x in heatTailSet B₀, heatTest a P x ^ 2) + t * (∫ x, heatTest a P x ^ 2) +
        (1 + 1 / t) * (2 * B₁ * heatPoleCorrection a P B₀ B₁ ^ 2) := by
  set κ := heatPoleCorrection a P B₀ B₁ with hκ
  have hV := integrable_heatTest_sq ha P
  have hu : Integrable (fun x => heatSource a P B₀ B₁ x ^ 2) := by
    have hc : Continuous fun x => heatSource a P B₀ B₁ x ^ 2 :=
      (contDiff_heatSource (B₀ := B₀) (B₁ := B₁) a P).continuous.pow 2
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_heatSource h0.le h01 a P).comp_left (g := fun y : ℝ => y ^ 2)
        (by norm_num))
  have hS := measurableSet_heatTailSet B₀
  have hT : Integrable ((heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2)) :=
    hV.indicator hS
  have hI : Integrable ((Icc (-B₁) B₁).indicator (fun _ => (1 + 1 / t) * κ ^ 2)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hT2 : Integrable (fun x => (heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2) x +
      t * heatTest a P x ^ 2) := hT.add (hV.const_mul t)
  have hR : Integrable (fun x => (heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2) x +
      t * heatTest a P x ^ 2 + (Icc (-B₁) B₁).indicator (fun _ => (1 + 1 / t) * κ ^ 2) x) :=
    hT2.add hI
  have hpt : ∀ x, |heatSource a P B₀ B₁ x ^ 2 - heatTest a P x ^ 2| ≤
      (heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2) x + t * heatTest a P x ^ 2 +
        (Icc (-B₁) B₁).indicator (fun _ => (1 + 1 / t) * κ ^ 2) x := fun x => by
    have hχ0 := heatCutoff_nonneg (B₀ := B₀) (B₁ := B₁) x
    have hχ1 := heatCutoff_le_one (B₀ := B₀) (B₁ := B₁) x
    have h := abs_sq_truncation_sub_le (g := heatTest a P x) (κ := κ) hχ0 hχ1 ht
    have e : heatSource a P B₀ B₁ x = (heatTest a P x - κ) * heatCutoff B₀ B₁ x := rfl
    rw [e]
    refine h.trans ?_
    have hA : heatTest a P x ^ 2 * (1 - heatCutoff B₀ B₁ x ^ 2) ≤
        (heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2) x := by
      by_cases hx : x ∈ heatTailSet B₀
      · rw [indicator_of_mem hx]
        have : 0 ≤ heatCutoff B₀ B₁ x ^ 2 := sq_nonneg _
        nlinarith [sq_nonneg (heatTest a P x)]
      · rw [indicator_of_notMem hx]
        have hx' : |x| ≤ B₀ := le_of_lt (lt_of_not_ge hx)
        rw [heatCutoff_eq_one h0.le h01 hx']
        ring_nf; rfl
    have hB : (1 + 1 / t) * (κ ^ 2 * heatCutoff B₀ B₁ x ^ 2) ≤
        (Icc (-B₁) B₁).indicator (fun _ => (1 + 1 / t) * κ ^ 2) x := by
      by_cases hx : x ∈ Icc (-B₁) B₁
      · rw [indicator_of_mem hx]
        have h2 : heatCutoff B₀ B₁ x ^ 2 ≤ 1 := by nlinarith
        have : κ ^ 2 * heatCutoff B₀ B₁ x ^ 2 ≤ κ ^ 2 := mul_le_of_le_one_right (sq_nonneg κ) h2
        have : 0 ≤ 1 + 1 / t := by positivity
        nlinarith
      · rw [indicator_of_notMem hx]
        have hx' : B₁ ≤ |x| := by
          rw [Set.mem_Icc, not_and_or] at hx
          rcases hx with h | h
          · push Not at h; exact le_abs.2 (Or.inr (by linarith))
          · push Not at h; exact le_abs.2 (Or.inl h.le)
        rw [heatCutoff_eq_zero h0.le h01 hx']
        simp
    linarith
  have hsub : (∫ x, heatSource a P B₀ B₁ x ^ 2) - ∫ x, heatTest a P x ^ 2 =
      ∫ x, (heatSource a P B₀ B₁ x ^ 2 - heatTest a P x ^ 2) := (integral_sub hu hV).symm
  rw [hsub]
  calc |∫ x, (heatSource a P B₀ B₁ x ^ 2 - heatTest a P x ^ 2)|
      ≤ ∫ x, |heatSource a P B₀ B₁ x ^ 2 - heatTest a P x ^ 2| := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((heatTailSet B₀).indicator (fun x => heatTest a P x ^ 2) x + t * heatTest a P x ^ 2 +
          (Icc (-B₁) B₁).indicator (fun _ => (1 + 1 / t) * κ ^ 2) x) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hR
          (Filter.Eventually.of_forall hpt)
    _ = _ := by
        rw [integral_add hT2 hI, integral_add hT (hV.const_mul t),
          integral_indicator hS, integral_const_mul, integral_indicator measurableSet_Icc,
          setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith : (0 : ℝ) ≤ B₁ - -B₁)]
        ring

/-! ## The arithmetic of the sharp floor -/

theorem le_of_floor_bounds {μ V T κ M ρ τ₀ τ₁ N c₀ C B₁ E S σ Y H U : ℝ}
    (hS : 0 ≤ S) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (hN : 0 ≤ N) (hB₁ : 0 ≤ B₁) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hY : 0 ≤ Y) (hτ₀ : 0 ≤ τ₀) (hτ₁ : 0 ≤ τ₁)
    (hmain : μ * U ≤ H + (2 * M * ρ + ρ ^ 2) * S)
    (hU : |U - V| ≤ T + σ * V + (1 + 1 / σ) * (2 * B₁ * κ ^ 2))
    (hρ : ρ = τ₁ + C * τ₀ + |κ| * N) (hT : T ≤ σ ^ 2 * V) (hτ₀b : τ₀ ^ 2 ≤ E * σ ^ 2 * V)
    (hτ₁b : τ₁ ^ 2 ≤ E * σ ^ 2 * Y * V) (hMb : M ^ 2 ≤ E * Y * V) (hκ : |κ| * c₀ ≤ τ₀) :
    V * (μ - |μ| * (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) -
      S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))) ≤ H := by
  have hκ0 := abs_nonneg κ
  have hκ2 : κ ^ 2 * c₀ ^ 2 ≤ E * σ ^ 2 * V := by
    have h1 : (|κ| * c₀) ^ 2 ≤ τ₀ ^ 2 := pow_le_pow_left₀ (by positivity) hκ 2
    rw [mul_pow, sq_abs] at h1
    linarith
  have hκ2' : κ ^ 2 ≤ E * σ ^ 2 * V / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hκ2
  set W := Y + C ^ 2 + N ^ 2 / c₀ ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ2 : ρ ^ 2 ≤ 3 * E * σ ^ 2 * V * W := by
    have h3 : ρ ^ 2 ≤ 3 * (τ₁ ^ 2 + C ^ 2 * τ₀ ^ 2 + κ ^ 2 * N ^ 2) := by
      rw [hρ]
      nlinarith [sq_nonneg (τ₁ - C * τ₀), sq_nonneg (τ₁ - |κ| * N), sq_nonneg (C * τ₀ - |κ| * N),
        sq_abs κ]
    have h4 : C ^ 2 * τ₀ ^ 2 ≤ C ^ 2 * (E * σ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hτ₀b (sq_nonneg C)
    have h5 : κ ^ 2 * N ^ 2 ≤ E * σ ^ 2 * V / c₀ ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_right hκ2' (sq_nonneg N)
    have h6 : 3 * E * σ ^ 2 * V * W =
        3 * (E * σ ^ 2 * Y * V + C ^ 2 * (E * σ ^ 2 * V) + E * σ ^ 2 * V / c₀ ^ 2 * N ^ 2) := by
      rw [hW]; ring
    rw [h6]
    linarith
  have hsum : 2 * M * ρ + ρ ^ 2 ≤ σ * E * V * (Y + 6 * W) := by
    have hMρ : σ * (2 * M * ρ) ≤ σ ^ 2 * M ^ 2 + ρ ^ 2 := by nlinarith [sq_nonneg (σ * M - ρ)]
    have a2 : σ ^ 2 * M ^ 2 ≤ σ ^ 2 * (E * Y * V) := mul_le_mul_of_nonneg_left hMb (sq_nonneg σ)
    have a3 : σ * ρ ^ 2 ≤ ρ ^ 2 := mul_le_of_le_one_left (sq_nonneg ρ) hσ1
    have a1 : σ * (2 * M * ρ + ρ ^ 2) = σ * (2 * M * ρ) + σ * ρ ^ 2 := by ring
    have a4 : σ * (σ * E * V * (Y + 6 * W)) = σ ^ 2 * (E * Y * V) + 2 * (3 * E * σ ^ 2 * V * W) := by
      ring
    have h3 : σ * (2 * M * ρ + ρ ^ 2) ≤ σ * (σ * E * V * (Y + 6 * W)) := by
      rw [a1, a4]; linarith
    exact le_of_mul_le_mul_left h3 hσ0
  have hsumS : (2 * M * ρ + ρ ^ 2) * S ≤ σ * E * V * (Y + 6 * W) * S :=
    mul_le_mul_of_nonneg_right hsum hS
  -- the mass comparison
  have hκB : (1 + 1 / σ) * (2 * B₁ * κ ^ 2) ≤ (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2) * V := by
    have h1 : 2 * B₁ * κ ^ 2 ≤ 2 * B₁ * (E * σ ^ 2 * V / c₀ ^ 2) :=
      mul_le_mul_of_nonneg_left hκ2' (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + 1 / σ)
    have e : (1 + 1 / σ) * (2 * B₁ * (E * σ ^ 2 * V / c₀ ^ 2)) =
        (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2) * V := by
      field_simp
    linarith
  have hUV : |U - V| ≤ (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) * V := by
    have e : (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) * V =
        σ ^ 2 * V + σ * V + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2) * V := by ring
    linarith
  have hμU : μ * V - |μ| * ((σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) * V) ≤ μ * U := by
    have h1 : μ * U - μ * V = μ * (U - V) := by ring
    have h2 := neg_abs_le (μ * (U - V))
    rw [abs_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left hUV (abs_nonneg μ)
    linarith
  have hfin : V * (μ - |μ| * (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) -
      S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))) =
      μ * V - |μ| * ((σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) * V) -
        σ * E * V * (Y + 6 * W) * S := by
    rw [hW]; ring
  rw [hfin]
  linarith

/-- **The sharp even-floor converse.** -/
theorem eventually_le_re_heatHankel_of_evenWeilFloor {A μ : ℝ} (hA : 0 < A)
    (hfloor : EvenWeilFloor A μ) {K : ℝ} (hK : 0 < K) (hKA : 4 * K < A ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n → ∀ P : ℝ[X], P.natDegree ≤ n →
      P.eval (-1 / 4) = 0 →
        (μ - ε) * ∫ x, heatTest a P x ^ 2 ≤
          (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re := by
  obtain ⟨B₀, B₁, hB₀, h01, h1A, hKB⟩ := exists_cutoff_radii hA hKA
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_heatCutoff (B₀ := B₀) (B₁ := B₁) hB₀.le h01
  have hc₀ : 0 < cutoffMoment B₀ B₁ := cutoffMoment_pos hB₀ h01
  have hN : 0 ≤ ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2) :=
    integral_nonneg fun _ => by positivity
  have hE : 0 ≤ heatStripConstant B₀ := by unfold heatStripConstant; positivity
  have hS : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_nonneg fun _ => by positivity
  -- opaque names for the constants
  obtain ⟨c₀, hc₀e⟩ : ∃ c₀, c₀ = cutoffMoment B₀ B₁ := ⟨_, rfl⟩
  obtain ⟨N, hNe⟩ : ∃ N, N = ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2) := ⟨_, rfl⟩
  obtain ⟨E, hEe⟩ : ∃ E, E = heatStripConstant B₀ := ⟨_, rfl⟩
  obtain ⟨S, hSe⟩ : ∃ S, S = ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := ⟨_, rfl⟩
  rw [← hc₀e] at hc₀
  rw [← hNe] at hN
  rw [← hEe] at hE
  rw [← hSe] at hS
  have hB₁ : 0 < B₁ := hB₀.trans h01
  obtain ⟨Z, hZe⟩ : ∃ Z, Z = C ^ 2 + N ^ 2 / c₀ ^ 2 := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZe]; positivity
  obtain ⟨D, hDe⟩ : ∃ D, D = |μ| * (2 + 4 * B₁ * E / c₀ ^ 2) + S * E * (7 + 6 * Z) + 1 :=
    ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDe]; positivity
  obtain ⟨δ, hδe⟩ : ∃ δ : ℝ, δ = min (1 / 2) (ε / D) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδe]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := by rw [hδe]; exact min_le_left _ _
  have hδD : δ * D ≤ ε := by
    have h := min_le_right (1 / 2 : ℝ) (ε / D)
    rw [← hδe] at h
    calc δ * D ≤ ε / D * D := mul_le_mul_of_nonneg_right h hD.le
      _ = ε := by field_simp
  obtain ⟨m, hm0, hmom⟩ := exists_heatMomentOrder hK hB₀ hKB
  filter_upwards [hmom δ hδ0] with n hn a ha haK P hdeg hP
  obtain ⟨ha1, hσδ, hσYδ⟩ := hn a ha haK
  have htpos : 0 < heatMomentRatio n (2 * (n / m + 1)) a B₀ := heatMomentRatio_pos ha ha1 hB₀
  obtain ⟨σ, hσe⟩ : ∃ σ, σ = heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (n / m + 1) := ⟨_, rfl⟩
  rw [← hσe] at hσδ hσYδ
  have hσ0 : 0 < σ := by rw [hσe]; exact pow_pos htpos _
  have hσ1 : σ ≤ 1 := by linarith only [hσδ, hδ1]
  have hσ2 : heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (2 * (n / m + 1)) = σ ^ 2 := by
    rw [hσe, ← pow_mul, mul_comm]
  have hk : heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (2 * (n / m + 1)) ≤ 1 / 2 := by
    rw [hσ2]
    have h := mul_le_mul_of_nonneg_left hσ1 hσ0.le
    rw [mul_one, ← pow_two] at h
    linarith only [h, hσδ, hδ1]
  obtain ⟨hT, hτ₀, hτ₁, hM⟩ := heatTest_tail_bounds ha ha1 hdeg hB₀ (2 * (n / m + 1)) hk
  rw [hσ2] at hT hτ₀ hτ₁
  rw [← hEe] at hτ₀ hτ₁ hM
  have hmain := mul_integral_heatSource_sq_le_re_heatHankel hfloor hB₀ h01 h1A ha ha1 P hC
  rw [← hNe, ← hSe] at hmain
  have hκ := abs_heatPoleCorrection_mul_le hB₀ h01 ha ha1 P hP
  rw [← hc₀e] at hκ
  obtain ⟨Y, hYe⟩ : ∃ Y : ℝ, Y = 4 * (1 / (2 * a)) * (2 * n + 1) := ⟨_, rfl⟩
  rw [← hYe] at hσYδ hτ₁ hM
  have hY : 0 ≤ Y := by rw [hYe]; positivity
  have hτ₀0 : 0 ≤ stripMassOn (heatTest a P) (heatTailSet B₀) :=
    setIntegral_nonneg (measurableSet_heatTailSet B₀) fun _ _ => by positivity
  have hτ₁0 : 0 ≤ stripMassOn (heatTestDeriv a P) (heatTailSet B₀) :=
    setIntegral_nonneg (measurableSet_heatTailSet B₀) fun _ _ => by positivity
  have hU := abs_integral_heatSource_sq_sub_le hB₀ h01 ha P hσ0
  have hfin := le_of_floor_bounds hS hc₀ hC0 hN (by linarith) hσ0 hσ1 hY hτ₀0 hτ₁0 hmain hU rfl
    hT hτ₀ hτ₁ hM hκ
  rw [← hZe] at hfin
  have hV : 0 ≤ ∫ x, heatTest a P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hbr : μ - ε ≤ μ - |μ| * (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) -
      S * E * σ * (7 * Y + 6 * Z) := by
    have hσσ : σ ^ 2 ≤ σ := by
      have h := mul_le_mul_of_nonneg_left hσ1 hσ0.le
      rw [mul_one, ← pow_two] at h
      exact h
    have hs2 : σ ^ 2 + σ ≤ 2 * δ := by linarith only [hσσ, hσδ]
    have hBE : 0 ≤ 2 * B₁ * E / c₀ ^ 2 := by
      have : 0 ≤ B₁ := by linarith
      positivity
    have h1 : |μ| * (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) ≤
        δ * (|μ| * (2 + 4 * B₁ * E / c₀ ^ 2)) := by
      have e : δ * (|μ| * (2 + 4 * B₁ * E / c₀ ^ 2)) =
          |μ| * (2 * δ + 2 * δ * (2 * B₁ * E / c₀ ^ 2)) := by ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)
      have := mul_le_mul_of_nonneg_right hs2 hBE
      linarith only [this, hs2]
    have h2 : S * E * σ * (7 * Y + 6 * Z) ≤ δ * (S * E * (7 + 6 * Z)) := by
      have hSE : 0 ≤ S * E := mul_nonneg hS hE
      have e1 : S * E * σ * (7 * Y + 6 * Z) = S * E * (7 * (σ * Y) + 6 * Z * σ) := by ring
      have e2 : δ * (S * E * (7 + 6 * Z)) = S * E * (7 * δ + 6 * Z * δ) := by ring
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ hSE
      have := mul_le_mul_of_nonneg_left hσδ (by positivity : (0 : ℝ) ≤ 6 * Z)
      linarith only [this, hσYδ]
    have hDexp : δ * D = δ * (|μ| * (2 + 4 * B₁ * E / c₀ ^ 2)) + δ * (S * E * (7 + 6 * Z)) + δ := by
      rw [hDe]; ring
    linarith only [h1, h2, hδD, hDexp, hδ0]
  calc (μ - ε) * ∫ x, heatTest a P x ^ 2
      ≤ (∫ x, heatTest a P x ^ 2) * (μ - |μ| * (σ ^ 2 + σ + (σ ^ 2 + σ) * (2 * B₁ * E / c₀ ^ 2)) -
          S * E * σ * (7 * Y + 6 * Z)) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hbr hV
    _ ≤ _ := hfin

/-! ## The spectral bracket -/

/-- **The HCF spectral bracket.**  Let `μ` be an even Weil floor at half-width `A` and let `u` be
a smooth even pole-vanishing source of half-width `A'` with `A'² < 4K < A²`.  Then for every
`ε > 0`, for all large `n`, every nonzero real `P` of degree `≤ n` on the pole hyperplane has
heat Rayleigh quotient at time `K/n` at least `μ − ε`, and some such `P` has quotient below
`Re Σ F_u(z_q)² / ∫u² + ε`.  Hence the window ground energy converges to the even Weil ground
energy at half-width `2√K` wherever the latter is continuous. -/
theorem heatWindow_spectral_bracket {A μ : ℝ} (hA : 0 < A) (hfloor : EvenWeilFloor A μ)
    {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {A' : ℝ}
    (hsupp : ∀ t : ℝ, A' < |t| → u t = 0) (heven : ∀ x, u (-x) = u x)
    (hpole : ∫ x, u x * Real.exp (x / 2) = 0) (hN : 0 < ∫ x, u x ^ 2) {K : ℝ} (hK : 0 < K)
    (hA'K : A' ^ 2 < 4 * K) (hKA : 4 * K < A ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∀ P : ℝ[X], P.natDegree ≤ n → P.eval (-1 / 4) = 0 → P ≠ 0 →
        μ - ε ≤ (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re /
          ∫ x, heatTest (K / n) P x ^ 2) ∧
      ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧ 0 < ∫ x, heatTest (K / n) P x ^ 2 ∧
        (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re /
            ∫ x, heatTest (K / n) P x ^ 2 <
          (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2).re / (∫ x, u x ^ 2) + ε := by
  filter_upwards [eventually_le_re_heatHankel_of_evenWeilFloor hA hfloor hK hKA hε,
    eventually_exists_poleHyperplane_rayleigh_lt hu hcpt hsupp heven hpole hK hA'K hN hε,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)] with n h1 h2 hn0
  have ha : 0 < K / n := div_pos hK hn0
  refine ⟨fun P hP hPe hP0 => ?_, ?_⟩
  · have hV := integral_heatTest_sq_pos ha hP0
    rw [le_div_iff₀ hV]
    exact h1 (K / n) ha le_rfl P hP hPe
  · obtain ⟨P, hPd, hPe, hV, hlt⟩ := h2
    exact ⟨P, hPd, hPe, hV, by rw [div_lt_iff₀ hV]; exact hlt⟩

end

end RHTower
