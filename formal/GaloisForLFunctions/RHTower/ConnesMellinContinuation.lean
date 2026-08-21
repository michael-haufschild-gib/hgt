import GaloisForLFunctions.RHTower.ConnesArchPeriodizationDecay
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Analyticity of the Mellin transform of the punctured periodization

Appendix I Lemma 3 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∫ E(f)(x) Χ_0(x) |x|^{s-1/2} d^*x = c L(Χ_0, s) Δ'_s(f)`   for `Re s > 0`.

Connes proves the identity for `Re s > 1` from Lemma 1 and then says *"since both sides are
analytic in `s` it holds in general"*.  That continuation step is what this file supplies: the
punctured periodization of a function in `𝒮(ℝ)_0` decays faster than every power at *both*
multiplicative ends, so its Mellin transform is entire (the corpus's
`RHTower.differentiable_mellin_of_rapidDecayRay`), and two entire functions agreeing on the
half-plane of absolute convergence agree everywhere.
-/

open Filter Topology MeasureTheory Set
open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Local uniform bound for the punctured lattice family. -/
theorem connes_archPunctured_continuousOn (f : SchwartzMap ℝ ℂ) :
    ContinuousOn (fun a : ℝ => connesArchPunctured f a) (Ioi (0 : ℝ)) := by
  intro a0 ha0
  have ha0' : (0 : ℝ) < a0 := ha0
  set c : ℝ := a0 / 2 with hc
  have hcpos : (0 : ℝ) < c := by rw [hc]; linarith
  set S : ℝ := SchwartzMap.seminorm ℂ 2 0 f with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ f
  set u : ℤ → ℝ := fun n => if n = 0 then 0 else S / (c ^ 2 * (n : ℝ) ^ 2) with hu
  have husummable : Summable u := by
    have hbase : Summable fun n : ℤ => S / c ^ 2 * (1 / ((n : ℝ) ^ (2 : ℕ))) :=
      ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left _
    refine hbase.congr_cofinite ?_
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    rw [hu]
    simp only [if_neg hn]
    field_simp
  have hbound : ∀ (n : ℤ) (a : ↥(Ioi c)),
      ‖(if n = 0 then 0 else f ((a : ℝ) * (n : ℝ)))‖ ≤ u n := by
    intro n a
    by_cases hn : n = 0
    · simp [hn, hu]
    · have hac : c < (a : ℝ) := a.2
      have ha : (0 : ℝ) < (a : ℝ) := lt_trans hcpos hac
      have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn
      have hprod : ((a : ℝ) * (n : ℝ)) ≠ 0 := mul_ne_zero (ne_of_gt ha) hnR
      have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 ((a : ℝ) * (n : ℝ))
      have habs : ‖(a : ℝ) * (n : ℝ)‖ ^ (2 : ℕ) = (a : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
        rw [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs, sq_abs]
      rw [habs] at hsem
      have hpos : (0 : ℝ) < (a : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
      have hle : ‖f ((a : ℝ) * (n : ℝ))‖ ≤ S / ((a : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
        rw [le_div_iff₀ hpos]
        linarith [hsem]
      have hmono : S / ((a : ℝ) ^ 2 * (n : ℝ) ^ 2) ≤ S / (c ^ 2 * (n : ℝ) ^ 2) := by
        refine div_le_div_of_nonneg_left hS0 (by positivity) ?_
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        have hc2 : c ^ 2 ≤ (a : ℝ) ^ 2 := by nlinarith [hcpos, hac]
        nlinarith [hn2, hc2]
      rw [hu]
      simp only [if_neg hn]
      linarith [hle, hmono]
  have hcontFam : ∀ n : ℤ,
      Continuous fun a : ↥(Ioi c) => (if n = 0 then 0 else f ((a : ℝ) * (n : ℝ))) := by
    intro n
    by_cases hn : n = 0
    · simpa [hn] using (continuous_const : Continuous fun _ : ↥(Ioi c) => (0 : ℂ))
    · simp only [if_neg hn]
      exact (f.continuous.comp ((continuous_subtype_val).mul continuous_const))
  have hcont : Continuous fun a : ↥(Ioi c) => connesArchPunctured f (a : ℝ) :=
    continuous_tsum hcontFam husummable hbound
  have hmem : Ioi c ∈ nhds a0 := Ioi_mem_nhds (by rw [hc]; linarith)
  have hcontOn : ContinuousOn (fun a : ℝ => connesArchPunctured f a) (Ioi c) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hcont
  exact (hcontOn.continuousAt hmem).continuousWithinAt

theorem connes_archPeriodization_continuousOn (f : SchwartzMap ℝ ℂ) :
    ContinuousOn (fun a : ℝ => connesArchPeriodization f a) (Ioi (0 : ℝ)) := by
  refine ContinuousOn.mul ?_ (connes_archPunctured_continuousOn f)
  exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn

theorem connes_archPeriodization_isBigO_atTop (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    (fun x : ℝ => connesArchPeriodization f x) =O[atTop] fun x : ℝ => x ^ (-a) := by
  obtain ⟨k, hk⟩ := exists_nat_gt a
  have hlim := connes_archPeriodization_rapidDecay f k
  have hev : ∀ᶠ x : ℝ in atTop, x ^ k * ‖connesArchPeriodization f x‖ ≤ 1 :=
    hlim.eventually_le_const (by norm_num)
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hpow : (0 : ℝ) < x ^ k := by positivity
  have h1 : ‖connesArchPeriodization f x‖ ≤ (x ^ k)⁻¹ := by
    rw [← one_div, le_div_iff₀ hpow]
    calc ‖connesArchPeriodization f x‖ * x ^ k
        = x ^ k * ‖connesArchPeriodization f x‖ := by ring
      _ ≤ 1 := hx
  have h2 : (x ^ k)⁻¹ = x ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
  have h3 : x ^ (-(k : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : ‖x ^ (-a)‖ = x ^ (-a) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [h4, one_mul]
  calc ‖connesArchPeriodization f x‖ ≤ (x ^ k)⁻¹ := h1
    _ = x ^ (-(k : ℝ)) := h2
    _ ≤ x ^ (-a) := h3

theorem connes_archPeriodization_isBigO_zero (f : SchwartzMap ℝ ℂ) (h0 : f 0 = 0)
    (hint : (∫ x : ℝ, f x) = 0) (b : ℝ) :
    (fun x : ℝ => connesArchPeriodization f x) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-b)
  have hlim := connes_archPeriodization_rapidDecay_zero f h0 hint k
  have hev : ∀ᶠ y : ℝ in atTop, y ^ k * ‖connesArchPeriodization f y⁻¹‖ ≤ 1 :=
    hlim.eventually_le_const (by norm_num)
  have hinvtend : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      (x⁻¹) ^ k * ‖connesArchPeriodization f x‖ ≤ 1 := by
    filter_upwards [hinvtend.eventually hev, self_mem_nhdsWithin] with x hx hx0
    rwa [inv_inv] at hx
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  have hle1 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun x hx => hx.le
  filter_upwards [hev', self_mem_nhdsWithin, hle1] with x hx hx0 hx1
  have hxpos : (0 : ℝ) < x := hx0
  have hpow : (0 : ℝ) < (x⁻¹) ^ k := by positivity
  have h1 : ‖connesArchPeriodization f x‖ ≤ ((x⁻¹) ^ k)⁻¹ := by
    rw [← one_div, le_div_iff₀ hpow]
    calc ‖connesArchPeriodization f x‖ * (x⁻¹) ^ k
        = (x⁻¹) ^ k * ‖connesArchPeriodization f x‖ := by ring
      _ ≤ 1 := hx
  have h2 : ((x⁻¹) ^ k)⁻¹ = x ^ ((k : ℝ)) := by
    rw [inv_pow, inv_inv, Real.rpow_natCast]
  have h3 : x ^ ((k : ℝ)) ≤ x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hxpos hx1 (by linarith)
  have h4 : ‖x ^ (-b)‖ = x ^ (-b) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  rw [h4, one_mul]
  calc ‖connesArchPeriodization f x‖ ≤ ((x⁻¹) ^ k)⁻¹ := h1
    _ = x ^ ((k : ℝ)) := h2
    _ ≤ x ^ (-b) := h3

/-- **Appendix I Lemma 3, decay input.**  The punctured periodization of a function in `𝒮(ℝ)_0`
lies in Meyer's rapid-decay class on the ray. -/
theorem connes_archPeriodization_rapidDecayRay (f : SchwartzMap ℝ ℂ) (h0 : f 0 = 0)
    (hint : (∫ x : ℝ, f x) = 0) :
    _root_.RHTower.RapidDecayRay (fun a : ℝ => connesArchPeriodization f a) where
  contOn := connes_archPeriodization_continuousOn f
  decayTop := connes_archPeriodization_isBigO_atTop f
  decayZero := connes_archPeriodization_isBigO_zero f h0 hint

/-- **Appendix I Lemma 3, analyticity.**  The Mellin transform of the punctured periodization of a
function in `𝒮(ℝ)_0` is entire. -/
theorem connes_differentiable_mellin_archPeriodization (f : SchwartzMap ℝ ℂ) (h0 : f 0 = 0)
    (hint : (∫ x : ℝ, f x) = 0) :
    Differentiable ℂ (mellin (fun a : ℝ => connesArchPeriodization f a)) :=
  _root_.RHTower.differentiable_mellin_of_rapidDecayRay
    (connes_archPeriodization_rapidDecayRay f h0 hint)

/-- **Appendix I Lemma 3, the continuation step.**  Two entire functions that agree on the
half-plane of absolute convergence agree everywhere. -/
theorem connes_entire_eq_of_eqOn_halfPlane {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (h : Set.EqOn F G {s : ℂ | 1 < s.re}) : F = G := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hGa : AnalyticOnNhd ℂ G Set.univ := hG.differentiableOn.analyticOnNhd isOpen_univ
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hev : F =ᶠ[nhds (2 : ℂ)] G :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) h
  have := hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  funext s
  exact this (Set.mem_univ s)

end

end GaloisForLFunctions.RHTower
