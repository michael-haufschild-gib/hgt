import GaloisForLFunctions.RHTower.ConnesFractionalSymbolGrowth
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# §VII (39): the fractional convolution operator is an absolutely convergent double integral

§VII (39) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `(C_{α,v} * η)(x) = ∫ ψ(|ε|)(η(x+ε) − η(x)) dε/|ε|^{1+α}`.

Everything downstream — the multiplier identity `F(C*η) = F(C)·F(η)`, hence (41) — rests on the
double integral `∫∫ |ψ(|ε|)| |η(y+ε) − η(y)| |ε|^{-1-α} dy dε` being finite.  It is, and the
majorant factorises: the first difference of a Schwartz function is bounded by
`|ε| · 4C (1+|y|)^{-2}` for `|ε| ≤ 1` (mean value theorem plus the observation that a unit shift
changes `1+|y|` by at most a factor two), and `|ε|^{-1-α}·|ε| = |ε|^{-α}` has finite mass on
`[-1,1]` exactly when `α < 1`.

The swap is stated against an arbitrary *unimodular* weight `u`, so that the Fourier character can
be substituted for it downstream without redoing the integrability.
-/

open MeasureTheory Real Set
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The radial weight of (39). -/
def connesFracWeight (α : ℝ) (ψ : ℝ → ℝ) (ε : ℝ) : ℝ := ψ |ε| * |ε| ^ (-1 - α)

/-- Connes' convolution operator (39) at the archimedean place. -/
def connesFracConv (α : ℝ) (ψ : ℝ → ℝ) (η : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (y + ε) - η y)

theorem connes_absRpow_neg_eq {α : ℝ} (hα : -1 < α) :
    (fun ε : ℝ => |ε| ^ (-1 - α)) = fun ε : ℝ => (|ε| ^ (1 + α))⁻¹ := by
  funext ε
  rcases eq_or_ne ε 0 with h | h
  · subst h
    rw [abs_zero, Real.zero_rpow (by linarith : (-1 - α : ℝ) ≠ 0),
      Real.zero_rpow (by linarith : (1 + α : ℝ) ≠ 0), inv_zero]
  · rw [show (-1 - α : ℝ) = -(1 + α) by ring, Real.rpow_neg (abs_nonneg ε)]

theorem connesFracWeight_measurable {α : ℝ} (hα : -1 < α) {ψ : ℝ → ℝ} (hψc : Continuous ψ) :
    Measurable (connesFracWeight α ψ) := by
  have hm2 : Measurable (fun ε : ℝ => |ε| ^ (-1 - α)) := by
    rw [connes_absRpow_neg_eq hα]
    exact ((continuous_abs.rpow_const (fun _ => Or.inr (by linarith))).measurable).inv
  exact ((hψc.measurable).comp measurable_abs).mul hm2

theorem connesFracWeight_eq_zero {α : ℝ} {ψ : ℝ → ℝ} (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0)
    {ε : ℝ} (hε : 1 < |ε|) : connesFracWeight α ψ ε = 0 := by
  simp [connesFracWeight, hψsupp |ε| hε]

/-! ## The Schwartz first difference -/

/-- A Schwartz derivative decays quadratically. -/
theorem connes_schwartz_deriv_weight (η : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ C * (1 + |z|) ^ (-(2 : ℝ)) := by
  set g : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ η with hg
  set σ₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 g with hσ₀
  set σ₂ : ℝ := SchwartzMap.seminorm ℂ 2 0 g with hσ₂
  have hσ₀0 : (0 : ℝ) ≤ σ₀ := apply_nonneg _ g
  have hσ₂0 : (0 : ℝ) ≤ σ₂ := apply_nonneg _ g
  refine ⟨2 * σ₀ + 2 * σ₂, by positivity, fun z => ?_⟩
  have hcoe : deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z = g z := by
    rw [hg, SchwartzMap.derivCLM_apply]
  have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ g 0 z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ g 2 z
  rw [Real.norm_eq_abs] at h0 h2
  simp only [pow_zero, one_mul] at h0
  have hzabs : |z| ^ 2 * ‖g z‖ ≤ σ₂ := h2
  have hpos : (0 : ℝ) < (1 + |z|) ^ (2 : ℕ) := by positivity
  have hexp : (1 + |z|) ^ (-(2 : ℝ)) = ((1 + |z|) ^ (2 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast (1 + |z|) 2, ← Real.rpow_neg (by positivity)]
    norm_num
  rw [hcoe, hexp, le_mul_inv_iff₀ hpos]
  have hsq : (1 + |z|) ^ (2 : ℕ) = 1 + 2 * |z| + |z| ^ 2 := by ring
  have hcross : 2 * |z| ≤ 1 + |z| ^ 2 := by nlinarith [sq_nonneg (|z| - 1)]
  have hgnn : (0 : ℝ) ≤ ‖g z‖ := norm_nonneg _
  calc ‖g z‖ * (1 + |z|) ^ (2 : ℕ)
      = ‖g z‖ * (1 + 2 * |z| + |z| ^ 2) := by rw [hsq]
    _ ≤ ‖g z‖ * (2 + 2 * |z| ^ 2) := by nlinarith
    _ = 2 * ‖g z‖ + 2 * (|z| ^ 2 * ‖g z‖) := by ring
    _ ≤ 2 * σ₀ + 2 * σ₂ := by linarith

/-- **The first difference of a Schwartz function**, for a shift of size at most one. -/
theorem connes_schwartz_diff_bound (η : 𝓢(ℝ, ℂ)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z : ℝ, ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ C * (1 + |z|) ^ (-(2 : ℝ)))
    {y ε : ℝ} (hε : |ε| ≤ 1) :
    ‖η (y + ε) - η y‖ ≤ (4 * C * (1 + |y|) ^ (-(2 : ℝ))) * |ε| := by
  have hball : ∀ z ∈ Metric.closedBall y 1,
      ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖ ≤ 4 * C * (1 + |y|) ^ (-(2 : ℝ)) := by
    intro z hz
    have hzy : |z - y| ≤ 1 := by
      have := Metric.mem_closedBall.mp hz
      rwa [Real.dist_eq] at this
    have hlow : (1 + |y|) / 2 ≤ 1 + |z| := by
      have h1 : |y| - 1 ≤ |z| := by
        have := abs_sub_abs_le_abs_sub y z
        rw [abs_sub_comm y z] at this
        linarith
      rcases le_or_gt 1 |y| with hy | hy
      · linarith
      · have : (0 : ℝ) ≤ |z| := abs_nonneg z
        linarith
    have hyp : (0 : ℝ) < (1 + |y|) / 2 := by positivity
    have hsq : ((1 + |y|) / 2) ^ (2 : ℕ) ≤ (1 + |z|) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hyp.le hlow 2
    have hzpos : (0 : ℝ) < (1 + |z|) ^ (2 : ℕ) := by positivity
    have hypos : (0 : ℝ) < ((1 + |y|) / 2) ^ (2 : ℕ) := by positivity
    have hz2 : (1 + |z|) ^ (-(2 : ℝ)) = ((1 + |z|) ^ (2 : ℕ))⁻¹ := by
      rw [← Real.rpow_natCast (1 + |z|) 2, ← Real.rpow_neg (by positivity)]
      norm_num
    have hy2 : (1 + |y|) ^ (-(2 : ℝ)) = ((1 + |y|) ^ (2 : ℕ))⁻¹ := by
      rw [← Real.rpow_natCast (1 + |y|) 2, ← Real.rpow_neg (by positivity)]
      norm_num
    have hkey : ((1 + |z|) ^ (2 : ℕ))⁻¹ ≤ 4 * ((1 + |y|) ^ (2 : ℕ))⁻¹ := by
      have hexp : ((1 + |y|) / 2) ^ (2 : ℕ) = (1 + |y|) ^ (2 : ℕ) / 4 := by ring
      rw [hexp] at hsq
      have hinv : ((1 + |z|) ^ (2 : ℕ))⁻¹ ≤ ((1 + |y|) ^ (2 : ℕ) / 4)⁻¹ := by
        have h4 : (0 : ℝ) < (1 + |y|) ^ (2 : ℕ) / 4 := by positivity
        have hm : ((1 + |z|) ^ (2 : ℕ))⁻¹ * ((1 + |y|) ^ (2 : ℕ) / 4)
            ≤ ((1 + |z|) ^ (2 : ℕ))⁻¹ * ((1 + |z|) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        rw [inv_mul_cancel₀ (ne_of_gt hzpos)] at hm
        calc ((1 + |z|) ^ (2 : ℕ))⁻¹
            = ((1 + |z|) ^ (2 : ℕ))⁻¹ * ((1 + |y|) ^ (2 : ℕ) / 4)
                * ((1 + |y|) ^ (2 : ℕ) / 4)⁻¹ := by field_simp
          _ ≤ 1 * ((1 + |y|) ^ (2 : ℕ) / 4)⁻¹ :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = ((1 + |y|) ^ (2 : ℕ) / 4)⁻¹ := one_mul _
      have hrw : ((1 + |y|) ^ (2 : ℕ) / 4)⁻¹ = 4 * ((1 + |y|) ^ (2 : ℕ))⁻¹ := by
        field_simp
      rwa [hrw] at hinv
    calc ‖deriv ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z‖
        ≤ C * (1 + |z|) ^ (-(2 : ℝ)) := hC z
      _ = C * ((1 + |z|) ^ (2 : ℕ))⁻¹ := by rw [hz2]
      _ ≤ C * (4 * ((1 + |y|) ^ (2 : ℕ))⁻¹) := mul_le_mul_of_nonneg_left hkey hC0
      _ = 4 * C * (1 + |y|) ^ (-(2 : ℝ)) := by rw [hy2]; ring
  have hdiff : ∀ z ∈ Metric.closedBall y 1,
      DifferentiableAt ℝ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) z := fun z _ => η.differentiable z
  have hconv : Convex ℝ (Metric.closedBall y 1) := convex_closedBall y 1
  have hys : y ∈ Metric.closedBall y 1 := Metric.mem_closedBall_self (by norm_num)
  have hxs : y + ε ∈ Metric.closedBall y 1 := by
    rw [Metric.mem_closedBall, Real.dist_eq]
    simpa using hε
  have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hball hys hxs
  simpa [Real.norm_eq_abs] using hmvt

/-! ## The `ε`-side majorant -/

theorem connes_absRpow_intervalIntegrable_unit {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun ε : ℝ => |ε| ^ p) volume (-1) 1 := by
  have h01 : IntervalIntegrable (fun ε : ℝ => |ε| ^ p) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine MeasureTheory.IntegrableOn.congr_fun
      ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (1 : ℝ)) hp).1)
      (fun x hx => ?_) measurableSet_Ioc
    rw [abs_of_pos hx.1]
  have hneg : (fun x : ℝ => (fun ε : ℝ => |ε| ^ p) (-x)) = fun ε : ℝ => |ε| ^ p := by
    funext x
    show |(-x)| ^ p = |x| ^ p
    rw [abs_neg]
  have hm10 : IntervalIntegrable (fun ε : ℝ => |ε| ^ p) volume (-1) 0 := by
    refine (IntervalIntegrable.iff_comp_neg (a := (-1 : ℝ)) (b := (0 : ℝ))
      (f := fun ε : ℝ => |ε| ^ p) (by finiteness)).mpr ?_
    rw [hneg]
    simpa using h01.symm
  exact hm10.trans h01

theorem connes_absRpow_integrableOn_Icc {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun ε : ℝ => |ε| ^ p) (Icc (-1 : ℝ) 1) volume := by
  exact (connes_absRpow_intervalIntegrable_unit hp).1.congr_set_ae
    (MeasureTheory.Ioc_ae_eq_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).symm

theorem connes_fracEps_integrable {α : ℝ} (hα : α < 1) :
    Integrable (Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α))) volume := by
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact connes_absRpow_integrableOn_Icc (by linarith)

theorem connes_fracEps_nonneg {α : ℝ} (ε : ℝ) :
    0 ≤ Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε := by
  rcases Set.indicator_eq_zero_or_self (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε with h | h
  · rw [h]
  · rw [h]
    exact Real.rpow_nonneg (abs_nonneg ε) _

/-! ## The joint majorant and the swap -/

/-- **§VII (39) is an absolutely convergent double integral**, and its order may be exchanged with
any bounded measurable weight. -/
theorem connes_fracConv_swap {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψsupp : ∀ x : ℝ, 1 < x → ψ x = 0)
    (η : 𝓢(ℝ, ℂ)) {u : ℝ → ℂ} (humeas : Measurable u) (hu : ∀ y, ‖u y‖ ≤ 1) :
    (∫ y : ℝ, u y * connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y)
      = ∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) *
          ∫ y : ℝ, u y * (η (y + ε) - η y) := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_deriv_weight η
  set F : ℝ → ℝ → ℂ := fun y ε =>
    u y * (((connesFracWeight α ψ ε : ℝ)) : ℂ) * (η (y + ε) - η y) with hF
  -- majorant
  have hg : Integrable (fun y : ℝ => 4 * C * (1 + |y|) ^ (-(2 : ℝ))) volume := by
    have hbase : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) volume := by
      exact integrable_one_add_norm (E := ℝ) (by simp)
    have hcoe : (fun y : ℝ => 4 * C * (1 + |y|) ^ (-(2 : ℝ)))
        = fun y : ℝ => 4 * C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
      funext y
      rw [Real.norm_eq_abs]
    rw [hcoe]
    exact hbase.const_mul _
  have hh : Integrable (Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α))) volume :=
    connes_fracEps_integrable hα1
  have hmaj : Integrable (fun q : ℝ × ℝ =>
      (4 * C * (1 + |q.1|) ^ (-(2 : ℝ))) *
        Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) q.2)
      (volume.prod volume) := hg.mul_prod hh
  have hwmeas : Measurable (connesFracWeight α ψ) :=
    connesFracWeight_measurable (by linarith) hψc
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : Measurable (fun q : ℝ × ℝ => u q.1) := humeas.comp measurable_fst
    have h2 : Measurable (fun q : ℝ × ℝ => ((connesFracWeight α ψ q.2 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hwmeas.comp measurable_snd)
    have h3 : Measurable (fun q : ℝ × ℝ => (η (q.1 + q.2) - η q.1 : ℂ)) := by
      have hcont : Continuous fun q : ℝ × ℝ => (η (q.1 + q.2) - η q.1 : ℂ) :=
        (η.continuous.comp (continuous_fst.add continuous_snd)).sub
          (η.continuous.comp continuous_fst)
      exact hcont.measurable
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hbound : ∀ q : ℝ × ℝ, ‖Function.uncurry F q‖
      ≤ (4 * C * (1 + |q.1|) ^ (-(2 : ℝ))) *
          Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) q.2 := by
    rintro ⟨y, ε⟩
    have hval : Function.uncurry F (y, ε)
        = u y * (((connesFracWeight α ψ ε : ℝ)) : ℂ) * (η (y + ε) - η y) := rfl
    by_cases hmem : ε ∈ Icc (-1 : ℝ) 1
    · have hεle : |ε| ≤ 1 := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hind : Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε = |ε| ^ (-α) :=
        Set.indicator_of_mem hmem (fun ε : ℝ => |ε| ^ (-α))
      rw [hval, hind, norm_mul, norm_mul]
      have hwabs : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ ≤ |ε| ^ (-1 - α) := by
        rw [Complex.norm_real, Real.norm_eq_abs, connesFracWeight,
          abs_of_nonneg (mul_nonneg (hψ0 _) (Real.rpow_nonneg (abs_nonneg ε) _))]
        calc ψ |ε| * |ε| ^ (-1 - α) ≤ 1 * |ε| ^ (-1 - α) :=
              mul_le_mul_of_nonneg_right (hψ1 _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = |ε| ^ (-1 - α) := one_mul _
      have hdiff := connes_schwartz_diff_bound η hC0 hC (y := y) (ε := ε) hεle
      have hpow : (0 : ℝ) ≤ |ε| ^ (-1 - α) := Real.rpow_nonneg (abs_nonneg ε) _
      have hDnn : (0 : ℝ) ≤ 4 * C * (1 + |y|) ^ (-(2 : ℝ)) := by positivity
      rcases eq_or_ne ε 0 with hε0 | hε0
      · subst hε0
        have h0 : (0 : ℝ) ≤ 4 * C * (1 + |y|) ^ (-(2 : ℝ)) :=
          mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
        have hrhs : (0 : ℝ) ≤ 4 * C * (1 + |y|) ^ (-(2 : ℝ)) * |(0 : ℝ)| ^ (-α) :=
          mul_nonneg h0 (Real.rpow_nonneg (abs_nonneg _) _)
        simpa using hrhs
      · have hεpos : (0 : ℝ) < |ε| := abs_pos.mpr hε0
        have hcomb : |ε| ^ (-1 - α) * |ε| = |ε| ^ (-α) := by
          rw [show (-1 - α : ℝ) = -α + -1 by ring, Real.rpow_add hεpos,
            Real.rpow_neg_one, inv_mul_cancel_right₀ (ne_of_gt hεpos)]
        calc ‖u y‖ * ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ * ‖η (y + ε) - η y‖
            ≤ 1 * (|ε| ^ (-1 - α)) * ((4 * C * (1 + |y|) ^ (-(2 : ℝ))) * |ε|) := by
              refine mul_le_mul (mul_le_mul (hu y) hwabs (norm_nonneg _) zero_le_one)
                hdiff (norm_nonneg _) (by positivity)
          _ = (4 * C * (1 + |y|) ^ (-(2 : ℝ))) * (|ε| ^ (-1 - α) * |ε|) := by ring
          _ = (4 * C * (1 + |y|) ^ (-(2 : ℝ))) * |ε| ^ (-α) := by rw [hcomb]
    · have hgt : 1 < |ε| := by
        by_contra hcon
        exact hmem (abs_le.mp (not_lt.mp hcon) |> fun h => Set.mem_Icc.mpr ⟨h.1, h.2⟩)
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      have h4 : (0 : ℝ) ≤ 4 * C * (1 + |y|) ^ (-(2 : ℝ)) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
      rw [hval, hw0]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg h4 (connes_fracEps_nonneg ε)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) :=
    hmaj.mono' hmeas (Filter.Eventually.of_forall hbound)
  have hswap := MeasureTheory.integral_integral_swap hint
  have hL : (∫ y : ℝ, u y * connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y)
      = ∫ y : ℝ, ∫ ε : ℝ, F y ε := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show u y * (∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (y + ε) - η y))
      = ∫ ε : ℝ, F y ε
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
    simp only [hF]
    ring
  have hR : (∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) * ∫ y : ℝ, u y * (η (y + ε) - η y))
      = ∫ ε : ℝ, ∫ y : ℝ, F y ε := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
    show ((connesFracWeight α ψ ε : ℝ) : ℂ) * (∫ y : ℝ, u y * (η (y + ε) - η y))
      = ∫ y : ℝ, F y ε
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF]
    ring
  rw [hL, hR, hswap]

end

end GaloisForLFunctions.RHTower
