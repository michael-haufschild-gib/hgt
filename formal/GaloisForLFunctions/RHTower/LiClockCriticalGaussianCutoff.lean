import GaloisForLFunctions.RHTower.LiClockCriticalAngularKernel
import Mathlib

/-!
# Gaussian cutoff law for the critical Li-clock radial measures

Let `X, Y` be independent standard Gaussians and `R²_t = (2√t + X)² + Y²` (a noncentral
chi-square law with two degrees of freedom). For `t ≥ 0`, polar coordinates and the angular
Bessel integral show that the law of `R²_t` has density `½ e^{-2t - r/2} K(t r)` on `(0, ∞)`, with
`K(w) = ∑ wᵐ/(m!)²`. The cutoff measure `μ_t` uses instead the even kernel `E = (K + K⁻)/2`, so
`μ_t(s) = (P(R²_t ∈ s) + ∫_{s ∩ (0,∞)} ½ e^{-2t - r/2} K⁻(t r) dr) / 2`, where the oscillatory
part has total variation at most `e^{-2t}`. In the critical window `L → ∞`,
`(t - L/4)/√L → u`, the central limit for `R²_t` gives `P(R²_t ≤ L) → Φ(-2u)` and
`μ_t([0, L]) → Φ(-2u)/2`, with `Φ` the standard normal CDF; bands `[L - K, L]` of fixed width
have vanishing `μ_t`-mass, and the exponentially weighted cutoff loss
`∫_{[0,L]} e^{-(L - r)} dμ_t(r)` tends to `0`.

## Main results

- `tendsto_liClockCriticalRadialGaussian_cutoff`: in the window, `P(R²_t ∈ [0, L]) → Φ(-2u)`.
- `liClockCriticalRadialGaussian_eq_withDensity`: for `t ≥ 0`, the law of `R²_t` has density
  `½ e^{-2t - r/2} K(t r)` on `(0, ∞)`.
- `liClockCriticalCutoffMeasure_real_eq_half`: `μ_t` is half the law of `R²_t` plus half the
  oscillatory signed density.
- `liClockCriticalCutoffMeasure_mass_le_one`: `μ_t(ℝ) ≤ 1` for `t ≥ 0`.
- `tendsto_liClockCriticalCutoffMeasure_cutoff`: in the window, `μ_t([0, L]) → Φ(-2u)/2`.
- `tendsto_liClockCriticalCutoffMeasure_band`: in the window, `μ_t([L - K, L]) → 0` for `K > 0`.
- `tendsto_liClockCriticalCutoffLoss`: in the window, `∫_{[0,L]} e^{-(L - r)} dμ_t(r) → 0`.
- `liClockCriticalCutoffLoss_raw_integral`:
  `e^{-2t} ∫₀ᴸ e^{-L + r/2} E(t r) dr = 2 ∫_{[0,L]} e^{-(L - r)} dμ_t(r)`.

## Hypotheses

Unconditional. The window theorems assume `L n → ∞` and `(t n - L n / 4) / √(L n) → u`; the
density and mass statements assume `0 ≤ t`; band and loss bounds assume `0 < K < L`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace RHTower

private abbrev cgGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- Standard normal cumulative distribution function `Φ(x)`. -/
def liClockCriticalGaussianCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) x

/-- The standard Gaussian measure on `ℝ²` (product of two standard normals). -/
def liClockCriticalGaussianProduct : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)).prod
    (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))

/-- Squared radius `(2√t + x)² + y²` of the shifted Gaussian point. -/
def liClockCriticalGaussianRadiusSq (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * Real.sqrt t + p.1)^2 + p.2^2

/-- Law of `R²_t = (2√t + X)² + Y²` for independent standard Gaussians `X, Y`. -/
def liClockCriticalRadialGaussian (t : ℝ) : Measure ℝ :=
  Measure.map (liClockCriticalGaussianRadiusSq t) liClockCriticalGaussianProduct

private theorem cg_cdf_eq_real (x : ℝ) :
    liClockCriticalGaussianCDF x = cgGaussian.real (Iic x) :=
  ProbabilityTheory.cdf_eq_real _ x

private theorem cg_iic_real_pos {a b : ℝ} {s : Set ℝ}
    (hab : a < b) (hsub : Ioo a b ⊆ s) : 0 < cgGaussian.real s := by
  have hn : cgGaussian s ≠ 0 := by
    intro hs
    have hv : volume s = 0 :=
      ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num) hs
    have hi : volume (Ioo a b) = 0 := measure_mono_null hsub hv
    rw [Real.volume_Ioo] at hi
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) hi
  have hnr : cgGaussian.real s ≠ 0 := (measureReal_ne_zero_iff (μ := cgGaussian) (s := s)).mpr hn
  have hnonneg : 0 ≤ cgGaussian.real s := measureReal_nonneg
  by_contra h
  have hz : cgGaussian.real s = 0 := by linarith
  exact hnr hz

private theorem cg_iio_complement (x : ℝ) :
    cgGaussian.real (Ioi x) = 1 - liClockCriticalGaussianCDF x := by
  simpa only [compl_Iic, probReal_univ, cg_cdf_eq_real] using
    (measureReal_compl (μ := cgGaussian) (s := Iic x) measurableSet_Iic)

/-- `Φ(x) = (2π)^{-1/2} ∫_{y ≤ x} e^{-y²/2} dy`. -/
theorem liClockCriticalGaussianCDF_eq_integral (x : ℝ) :
  liClockCriticalGaussianCDF x = (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ y in Set.Iic x, Real.exp (-(y^2)/2) := by
  calc
    liClockCriticalGaussianCDF x =
        ∫ y in Iic x, ProbabilityTheory.gaussianPDFReal 0 1 y := by
      rw [cg_cdf_eq_real]
      change (cgGaussian (Iic x)).toReal = _
      rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num),
        ENNReal.toReal_ofReal]
      exact integral_nonneg (fun y => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 y)
    _ = _ := by
      simpa only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
        using (integral_const_mul (μ := volume.restrict (Iic x))
          ((Real.sqrt (2 * Real.pi))⁻¹) (fun y : ℝ => Real.exp (-(y^2)/2)))

/-- `0 < Φ(x) < 1` for every real `x`. -/
theorem liClockCriticalGaussianCDF_pos_lt_one (x : ℝ) :
    0 < liClockCriticalGaussianCDF x ∧ liClockCriticalGaussianCDF x < 1 := by
  have hp : 0 < cgGaussian.real (Iic x) :=
    cg_iic_real_pos (a := x - 1) (b := x) (by linarith)
      (fun y hy => le_of_lt hy.2)
  have hq : 0 < cgGaussian.real (Ioi x) :=
    cg_iic_real_pos (a := x) (b := x + 1) (by linarith)
      (fun y hy => hy.1)
  rw [cg_iio_complement] at hq
  rw [← cg_cdf_eq_real] at hp
  exact ⟨hp, by linarith⟩

/-- Symmetry of the normal CDF: `Φ(-x) = 1 - Φ(x)`. -/
theorem liClockCriticalGaussianCDF_neg (x : ℝ) :
    liClockCriticalGaussianCDF (-x) = 1 - liClockCriticalGaussianCDF x := by
  letI : NullSingletonClass cgGaussian :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  have hm : cgGaussian.map (fun y : ℝ => -y) = cgGaussian := by
    simpa only [neg_zero] using
      (ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := (1 : ℝ≥0)))
  have hpre : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  calc
    liClockCriticalGaussianCDF (-x) = cgGaussian.real (Iic (-x)) := cg_cdf_eq_real _
    _ = (cgGaussian.map (fun y : ℝ => -y)).real (Iic (-x)) := by rw [hm]
    _ = cgGaussian.real (Ici x) := by
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]
    _ = cgGaussian.real (Ioi x) :=
      measureReal_congr (Ioi_ae_eq_Ici (μ := cgGaussian) (a := x)).symm
    _ = 1 - liClockCriticalGaussianCDF x := cg_iio_complement x

/-- `Φ(0) = 1/2`. -/
theorem liClockCriticalGaussianCDF_zero : liClockCriticalGaussianCDF 0 = 1 / 2 := by
  have h := liClockCriticalGaussianCDF_neg 0
  simp only [neg_zero] at h
  linarith

private theorem cg_radius_measurable (t : ℝ) :
    Measurable (liClockCriticalGaussianRadiusSq t) := by
  unfold liClockCriticalGaussianRadiusSq
  fun_prop

private theorem cg_radius_nonneg (t : ℝ) (p : ℝ × ℝ) :
    0 ≤ liClockCriticalGaussianRadiusSq t p := by
  unfold liClockCriticalGaussianRadiusSq
  positivity

private theorem cg_vertical_null (a : ℝ) :
    liClockCriticalGaussianProduct {p : ℝ × ℝ | p.1 = a} = 0 := by
  letI : NullSingletonClass cgGaussian :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  have hset : {p : ℝ × ℝ | p.1 = a} = {a} ×ˢ (univ : Set ℝ) := by
    ext p
    simp
  rw [hset]
  change (cgGaussian.prod cgGaussian) ({a} ×ˢ univ) = 0
  rw [Measure.prod_prod]
  simp

/-- The law of `R²_t` is a probability measure. -/
theorem isProbabilityMeasure_liClockCriticalRadialGaussian (t : ℝ) :
    IsProbabilityMeasure (liClockCriticalRadialGaussian t) := by
  haveI : IsProbabilityMeasure liClockCriticalGaussianProduct := by
    unfold liClockCriticalGaussianProduct
    infer_instance
  exact Measure.isProbabilityMeasure_map (cg_radius_measurable t).aemeasurable

/-- Critical-window kinematics: if `L → ∞` and `(t - L/4)/√L → u`, then `t → ∞`, `t/L → 1/4`,
`√t/√L → 1/2` and `(L - 4t)/(4√t) → -2u`. -/
theorem liClockCriticalWindow_kinematics
    {L t : ℕ → ℝ} {u : ℝ}
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
  Tendsto t atTop atTop ∧
  Tendsto (fun n => t n / L n) atTop (nhds (1 / 4 : ℝ)) ∧
  Tendsto (fun n => Real.sqrt (t n) / Real.sqrt (L n)) atTop (nhds (1 / 2 : ℝ)) ∧
  Tendsto (fun n => (L n - 4 * t n) / (4 * Real.sqrt (t n))) atTop (nhds (-2 * u)) := by
  have hLp : ∀ᶠ n in atTop, 0 < L n := hL.eventually (eventually_gt_atTop 0)
  have hsL : Tendsto (fun n => Real.sqrt (L n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have heq : (fun n => 1 / 4 + ((t n - L n / 4) / Real.sqrt (L n)) /
      Real.sqrt (L n)) =ᶠ[atTop] (fun n => t n / L n) := by
    filter_upwards [hLp] with n hn
    rw [div_div, ← pow_two, Real.sq_sqrt hn.le]
    field_simp
    ring
  have hratio : Tendsto (fun n => t n / L n) atTop (nhds (1 / 4 : ℝ)) := by
    have hquarter : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (nhds (1 / 4 : ℝ)) :=
      tendsto_const_nhds
    have hh := hquarter.add (hT.div_atTop hsL)
    have hh' : Tendsto (fun n => (1 / 4 : ℝ) +
        ((t n - L n / 4) / Real.sqrt (L n)) / Real.sqrt (L n))
        atTop (nhds (1 / 4 : ℝ)) := by simpa only [add_zero] using hh
    exact hh'.congr' heq
  have htprod : Tendsto (fun n => (t n / L n) * L n) atTop atTop :=
    Filter.Tendsto.pos_mul_atTop (by norm_num : 0 < (1 / 4 : ℝ)) hratio hL
  have ht : Tendsto t atTop atTop := htprod.congr' (by
    filter_upwards [hLp] with n hn
    exact div_mul_cancel₀ (t n) hn.ne')
  have htp : ∀ᶠ n in atTop, 0 < t n := ht.eventually (eventually_gt_atTop 0)
  have hsratio : Tendsto (fun n => Real.sqrt (t n) / Real.sqrt (L n))
      atTop (nhds (1 / 2 : ℝ)) := by
    have hh := (Real.continuous_sqrt.tendsto (1 / 4 : ℝ)).comp hratio
    norm_num at hh
    exact hh.congr' (by
      filter_upwards [hLp] with n hn
      exact Real.sqrt_div' (t n) hn.le)
  have hsinv : Tendsto (fun n => (Real.sqrt (t n) / Real.sqrt (L n))⁻¹)
      atTop (nhds (2 : ℝ)) := by
    have he : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [← he]
    exact hsratio.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hth : Tendsto (fun n => -(((t n - L n / 4) / Real.sqrt (L n)) *
      (Real.sqrt (t n) / Real.sqrt (L n))⁻¹)) atTop (nhds (-2 * u)) := by
    have he : -(u * 2) = -2 * u := by ring
    simpa only [he] using (hT.mul hsinv).neg
  have hthreshold : Tendsto (fun n => (L n - 4 * t n) / (4 * Real.sqrt (t n)))
      atTop (nhds (-2 * u)) := hth.congr' (by
    filter_upwards [hLp, htp] with n hn ht_n
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hn), ne_of_gt (Real.sqrt_pos.mpr ht_n)]
    ring)
  exact ⟨ht, hratio, hsratio, hthreshold⟩

private theorem cg_moving_comparison
    {x a : ℝ} {r b : ℕ → ℝ}
    (hr : Tendsto r atTop (nhds x)) (hb : Tendsto b atTop (nhds a)) (hxa : x ≠ a) :
    ∀ᶠ n in atTop, (r n ≤ b n ↔ x ≤ a) := by
  rcases lt_or_gt_of_ne hxa with hlt | hgt
  · have hp : ∀ᶠ n in atTop, 0 < b n - r n :=
      (hb.sub hr).eventually_const_lt (by linarith : 0 < a - x)
    filter_upwards [hp] with n hn
    constructor
    · intro _; exact hlt.le
    · intro _; linarith
  · have hp : ∀ᶠ n in atTop, b n - r n < 0 :=
      (hb.sub hr).eventually_lt_const (by linarith : a - x < 0)
    filter_upwards [hp] with n hn
    constructor <;> intro h <;> linarith

private theorem cg_indicator_integral (a : ℝ) :
    (∫ p : ℝ × ℝ, if p.1 ≤ a then (1 : ℝ) else 0
      ∂liClockCriticalGaussianProduct) = liClockCriticalGaussianCDF a := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a} :=
    measurableSet_le measurable_fst measurable_const
  calc
    _ = liClockCriticalGaussianProduct.real {p : ℝ × ℝ | p.1 ≤ a} := by
      simpa only [Set.indicator_apply, Pi.one_apply, mem_setOf_eq] using
        (integral_indicator_one (μ := liClockCriticalGaussianProduct) hs)
    _ = cgGaussian.real (Iic a) * cgGaussian.real univ := by
      have hset : {p : ℝ × ℝ | p.1 ≤ a} = Iic a ×ˢ (univ : Set ℝ) := by
        ext p; simp
      rw [hset]
      exact measureReal_prod_prod _ _
    _ = liClockCriticalGaussianCDF a := by rw [probReal_univ, mul_one, cg_cdf_eq_real]

/-- Moving-threshold limit: if `Xₙ(p) → p₁` a.e. under the planar Gaussian and `bₙ → a`, then
`P(Xₙ ≤ bₙ) → Φ(a)` (dominated convergence; the line `p₁ = a` is null). -/
private theorem cg_moving_threshold
    {a : ℝ} {X : ℕ → (ℝ × ℝ) → ℝ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (nhds a))
    (hX : ∀ᵐ p ∂liClockCriticalGaussianProduct,
      Tendsto (fun n => X n p) atTop (nhds p.1))
    (hm : ∀ᶠ n in atTop, MeasurableSet {p : ℝ × ℝ | X n p ≤ b n}) :
    Tendsto (fun n => ∫ p : ℝ × ℝ,
      if X n p ≤ b n then (1 : ℝ) else 0 ∂liClockCriticalGaussianProduct)
      atTop (nhds (liClockCriticalGaussianCDF a)) := by
  letI : IsProbabilityMeasure liClockCriticalGaussianProduct := by
    unfold liClockCriticalGaussianProduct; infer_instance
  have hline : ∀ᵐ p ∂liClockCriticalGaussianProduct, p.1 ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using cg_vertical_null a
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun p : ℝ × ℝ => if X n p ≤ b n then (1 : ℝ) else 0)
      liClockCriticalGaussianProduct := by
    filter_upwards [hm] with n hn
    have he : ({p : ℝ × ℝ | X n p ≤ b n}.indicator
        (fun _ : ℝ × ℝ => (1 : ℝ))) =
        (fun p : ℝ × ℝ => if X n p ≤ b n then (1 : ℝ) else 0) := by
      funext p
      simp only [Set.indicator_apply, mem_setOf_eq]
    rw [← he]
    exact ((aestronglyMeasurable_const : AEStronglyMeasurable
      (fun _ : ℝ × ℝ => (1 : ℝ)) liClockCriticalGaussianProduct).indicator hn)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ p ∂liClockCriticalGaussianProduct,
      ‖if X n p ≤ b n then (1 : ℝ) else 0‖ ≤ 1 := by
    filter_upwards with n
    filter_upwards with p
    split_ifs <;> norm_num
  have hlim : ∀ᵐ p ∂liClockCriticalGaussianProduct,
      Tendsto (fun n => if X n p ≤ b n then (1 : ℝ) else 0)
        atTop (nhds (if p.1 ≤ a then (1 : ℝ) else 0)) := by
    filter_upwards [hX, hline] with p hp hpa
    apply tendsto_const_nhds.congr'
    filter_upwards [cg_moving_comparison hp hb hpa] with n hn
    simp only [hn]
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ × ℝ => (1 : ℝ)) hmeas hbound (integrable_const _) hlim
  simpa only [cg_indicator_integral] using h

/-- In the critical window (`L → ∞`, `(t - L/4)/√L → u`), `P(R²_t ∈ [0, L]) → Φ(-2u)`. -/
theorem tendsto_liClockCriticalRadialGaussian_cutoff
    {L t : ℕ → ℝ} {u : ℝ}
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
  Tendsto (fun n => (liClockCriticalRadialGaussian (t n)).real (Icc 0 (L n)))
    atTop (nhds (liClockCriticalGaussianCDF (-2 * u))) := by
  obtain ⟨ht, _, _, hb⟩ := liClockCriticalWindow_kinematics hL hT
  let X : ℕ → (ℝ × ℝ) → ℝ := fun n p =>
    p.1 + (p.1^2 + p.2^2) / (4 * Real.sqrt (t n))
  let b : ℕ → ℝ := fun n => (L n - 4 * t n) / (4 * Real.sqrt (t n))
  have hX : ∀ᵐ p ∂liClockCriticalGaussianProduct,
      Tendsto (fun n => X n p) atTop (nhds p.1) := by
    filter_upwards with p
    have hc := (Real.tendsto_sqrt_atTop.comp ht).const_div_atTop ((p.1^2 + p.2^2) / 4)
    have hc' : Tendsto (fun n => (p.1^2 + p.2^2) / (4 * Real.sqrt (t n)))
        atTop (nhds (0 : ℝ)) := by
      simpa only [div_mul_eq_div_div, Function.comp_apply] using hc
    have hp : Tendsto (fun _ : ℕ => p.1) atTop (nhds p.1) := tendsto_const_nhds
    simpa only [X, add_zero] using hp.add hc'
  have hm : ∀ᶠ n in atTop, MeasurableSet {p : ℝ × ℝ | X n p ≤ b n} := by
    filter_upwards with n
    apply measurableSet_le
    · dsimp [X]; fun_prop
    · exact measurable_const
  have hlim := cg_moving_threshold (b := b) (X := X) hb hX hm
  apply hlim.congr'
  have htp : ∀ᶠ n in atTop, 0 < t n := ht.eventually (eventually_gt_atTop 0)
  filter_upwards [htp] with n hn
  have hden : 0 < 4 * Real.sqrt (t n) := by positivity
  have hcmp (p : ℝ × ℝ) :
      X n p ≤ b n ↔ liClockCriticalGaussianRadiusSq (t n) p ≤ L n := by
    dsimp [X, b]
    rw [le_div_iff₀ hden, add_mul, div_mul_cancel₀ _ hden.ne']
    unfold liClockCriticalGaussianRadiusSq
    have hs := Real.sq_sqrt hn.le
    constructor <;> intro h <;> nlinarith
  rw [liClockCriticalRadialGaussian,
    map_measureReal_apply (cg_radius_measurable _) measurableSet_Icc]
  have hs : MeasurableSet ((liClockCriticalGaussianRadiusSq (t n)) ⁻¹' Icc 0 (L n)) :=
    (cg_radius_measurable _) measurableSet_Icc
  have hi := integral_indicator_one (μ := liClockCriticalGaussianProduct) hs
  simpa only [Set.indicator, Pi.one_apply, mem_preimage, mem_Icc,
    cg_radius_nonneg, true_and, hcmp] using hi


private theorem cg_translated_gaussian_product (t : ℝ) :
    ((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))).map
      (fun p : ℝ × ℝ => (p.1 + 2 * Real.sqrt t, p.2)) =
      (gaussianReal (2 * Real.sqrt t) (1 : NNReal)).prod
        (gaussianReal 0 (1 : NNReal)) := by
  change ((gaussianReal 0 (1 : NNReal)).prod (gaussianReal 0 (1 : NNReal))).map
    (Prod.map (fun x : ℝ => x + 2 * Real.sqrt t) id) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    gaussianReal_map_add_const, Measure.map_id, zero_add]

private theorem cg_translated_gaussian_pdf_integrable (t : ℝ) :
    Integrable
      (fun p : ℝ × ℝ => gaussianPDFReal (2 * Real.sqrt t) (1 : NNReal) p.1 *
        gaussianPDFReal 0 (1 : NNReal) p.2)
      (volume : Measure (ℝ × ℝ)) := by
  exact (integrable_gaussianPDFReal (2 * Real.sqrt t) (1 : NNReal)).mul_prod
    (integrable_gaussianPDFReal 0 (1 : NNReal))


private theorem cg_polar_integrable {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (polarCoord.symm p)) polarCoord.target := by
  have hi : IntegrableOn f (polarCoord.symm '' polarCoord.target) := by
    rw [polarCoord.symm_image_target_eq_source]
    exact hf.integrableOn
  have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn f).mp hi
  apply hp.congr_fun _ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
  rfl

private theorem cg_exp_envelope_integrable (t : ℝ) :
    IntegrableOn (fun r : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * t - r / 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => ((1 / 2 : ℝ) * Real.exp (-2 * t)) *
      Real.exp (-(1 / 2 : ℝ) * r)) (Ioi 0) := (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0).const_mul
    ((1 / 2 : ℝ) * Real.exp (-2 * t))
  apply hi.congr_fun _ measurableSet_Ioi
  intro r _
  dsimp only
  rw [show -2 * t - r / 2 = -2 * t + (-(1 / 2 : ℝ)) * r by ring, Real.exp_add]
  ring

private theorem cg_exp_envelope_integral (t : ℝ) :
    (∫ r in Ioi 0, (1 / 2 : ℝ) * Real.exp (-2 * t - r / 2)) = Real.exp (-2 * t) := by
  have he : (fun r : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * t - r / 2)) =
      (fun r : ℝ => ((1 / 2 : ℝ) * Real.exp (-2 * t)) * Real.exp (-(1 / 2 : ℝ) * r)) := by
    funext r
    rw [show -2 * t - r / 2 = -2 * t + (-(1 / 2 : ℝ)) * r by ring, Real.exp_add]
    ring
  rw [he, integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0]
  simp
  ring


private def cg_planar_pdf (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal (2 * Real.sqrt t) 1 p.1 *
    ProbabilityTheory.gaussianPDFReal 0 1 p.2

private theorem cg_shifted_gaussian_eq_density (t : ℝ) :
    (ProbabilityTheory.gaussianReal (2 * Real.sqrt t) 1).prod
      (ProbabilityTheory.gaussianReal 0 1) =
    volume.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (cg_planar_pdf t p)) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ (by norm_num),
    ProbabilityTheory.gaussianReal_of_var_ne_zero _ (by norm_num),
    prod_withDensity (ProbabilityTheory.measurable_gaussianPDF _ _)
      (ProbabilityTheory.measurable_gaussianPDF _ _)]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)).symm

private theorem cg_radial_gaussian_eq_shift_map (t : ℝ) :
    liClockCriticalRadialGaussian t =
    ((ProbabilityTheory.gaussianReal (2 * Real.sqrt t) 1).prod
      (ProbabilityTheory.gaussianReal 0 1)).map (fun p : ℝ × ℝ => p.1^2 + p.2^2) := by
  rw [← cg_translated_gaussian_product, Measure.map_map (by fun_prop) (by fun_prop)]
  unfold liClockCriticalRadialGaussian liClockCriticalGaussianRadiusSq
  congr 1
  funext p
  dsimp
  ring

private theorem cg_radial_gaussian_apply_eq_integral (t : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    liClockCriticalRadialGaussian t s = ENNReal.ofReal
      (∫ p in (fun p : ℝ × ℝ => p.1^2 + p.2^2) ⁻¹' s, cg_planar_pdf t p) := by
  rw [cg_radial_gaussian_eq_shift_map, Measure.map_apply (by fun_prop) hs,
    cg_shifted_gaussian_eq_density, withDensity_apply _ ((by fun_prop :
      Measurable (fun p : ℝ × ℝ => p.1^2 + p.2^2)) hs),
    ← ofReal_integral_eq_lintegral_ofReal]
  · exact (cg_translated_gaussian_pdf_integrable t).integrableOn
  · exact ae_of_all _ (fun p => mul_nonneg
      (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _) (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _))

private theorem cg_planar_pdf_polar {t : ℝ} (ht : 0 ≤ t) (r θ : ℝ) :
    cg_planar_pdf t (polarCoord.symm (r, θ)) =
    (2 * Real.pi)⁻¹ * Real.exp (-2 * t - r^2 / 2) *
      Real.exp (2 * Real.sqrt t * r * Real.cos θ) := by
  have hn : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ =
      (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
  have hs := Real.sq_sqrt ht
  have htrig : r^2 * ((Real.cos θ)^2 + (Real.sin θ)^2) = r^2 := by
    rw [Real.cos_sq_add_sin_sq, mul_one]
  dsimp [cg_planar_pdf, polarCoord]
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
        Real.exp (-((r * Real.cos θ - 2 * Real.sqrt t)^2) / 2 -
          (r * Real.sin θ)^2 / 2) := by simp only [sub_eq_add_neg, Real.exp_add, neg_div]; ring
    _ = (2 * Real.pi)⁻¹ * Real.exp (-2 * t - r^2 / 2 +
        2 * Real.sqrt t * r * Real.cos θ) := by
      rw [hn]
      congr 2
      nlinarith
    _ = _ := by rw [Real.exp_add]; ring

private theorem cg_polar_radius_sq (r θ : ℝ) :
    (polarCoord.symm (r, θ)).1^2 + (polarCoord.symm (r, θ)).2^2 = r^2 := by
  dsimp [polarCoord]
  nlinarith [mul_self_nonneg r, Real.cos_sq_add_sin_sq θ,
    show r^2 * ((Real.cos θ)^2 + (Real.sin θ)^2) = r^2 by
      rw [Real.cos_sq_add_sin_sq, mul_one]]

private theorem cg_squared_radius_integrable_iff (f : ℝ → ℝ) :
    IntegrableOn (fun r : ℝ => 2 * r * f (r^2)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] using
    (integrableOn_Ioi_comp_rpow_iff f (p := 2) (by norm_num))

private theorem cg_squared_radius_integral (f : ℝ → ℝ) :
    (∫ r in Ioi 0, 2 * r * f (r^2)) = ∫ r in Ioi 0, f r := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] using
    (integral_comp_rpow_Ioi f (p := 2) (by norm_num))


/-- Positive radial density `½ e^{-2t - r/2} K(t r)`. -/
def liClockCriticalPositiveRadialDensity (t r : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-2 * t - r / 2) * liClockCriticalPositiveKernel (t * r)

/-- Oscillatory radial density `½ e^{-2t - r/2} K⁻(t r)`. -/
def liClockCriticalOscillatoryRadialDensity (t r : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-2 * t - r / 2) * liClockCriticalOscillatoryKernel (t * r)

/-- Even radial density `½ e^{-2t - r/2} E(t r)`. -/
def liClockCriticalEvenRadialDensity (t r : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-2 * t - r / 2) * liClockCriticalEvenKernel (t * r)

/-- Cutoff measure `μ_t` on `(0, ∞)` with density `½ e^{-2t - r/2} E(t r)`. -/
def liClockCriticalCutoffMeasure (t : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun r => ENNReal.ofReal (liClockCriticalEvenRadialDensity t r))

/-- Cutoff loss `∫_{[0,L]} e^{-(L - r)} dμ_t(r)`. -/
def liClockCriticalCutoffLoss (t L : ℝ) : ℝ :=
  ∫ r in Icc 0 L, Real.exp (-(L - r)) ∂liClockCriticalCutoffMeasure t

private theorem cg_even_density_integrable {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (liClockCriticalEvenRadialDensity t) (Ioi 0) := by
  have hi := (integrableOn_liClockCriticalEvenKernel_decay (a := (1 / 2 : ℝ))
    (by norm_num) ht).const_mul ((1 / 2 : ℝ) * Real.exp (-2 * t))
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro r _
  dsimp [liClockCriticalEvenRadialDensity]
  rw [show -2 * t - r / 2 = -2 * t + -(1 / 2 : ℝ) * r by ring, Real.exp_add]
  ring

private theorem cg_oscillatory_density_norm_le {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    ‖liClockCriticalOscillatoryRadialDensity t r‖ ≤ (1 / 2 : ℝ) * Real.exp (-2 * t - r / 2) := by
  have ha := abs_liClockCriticalOscillatoryKernel_le_one (mul_nonneg ht hr)
  unfold liClockCriticalOscillatoryRadialDensity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) ha

/-- For `t ≥ 0`, the oscillatory radial density is integrable on `(0, ∞)` with
`∫ |½ e^{-2t - r/2} K⁻(t r)| dr ≤ e^{-2t}`. -/
theorem liClockCriticalOscillatoryRadialDensity_integrable_bound
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (liClockCriticalOscillatoryRadialDensity t) (Ioi 0) ∧
      (∫ r in Ioi 0, |liClockCriticalOscillatoryRadialDensity t r|) ≤ Real.exp (-2 * t) := by
  have hm : Continuous (liClockCriticalOscillatoryRadialDensity t) := by
    unfold liClockCriticalOscillatoryRadialDensity
    exact ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul
      (continuous_liClockCriticalOscillatoryKernel.comp (continuous_const.mul continuous_id)))
  have hi : IntegrableOn (liClockCriticalOscillatoryRadialDensity t) (Ioi 0) :=
    (cg_exp_envelope_integrable t).mono' hm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _
        (fun r hr => cg_oscillatory_density_norm_le ht hr.le)))
  refine ⟨hi, ?_⟩
  rw [← cg_exp_envelope_integral t]
  exact integral_mono_ae hi.norm (cg_exp_envelope_integrable t)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _
      (fun r hr => cg_oscillatory_density_norm_le ht hr.le)))

private theorem cg_density_half (t r : ℝ) :
    liClockCriticalEvenRadialDensity t r =
    (liClockCriticalPositiveRadialDensity t r + liClockCriticalOscillatoryRadialDensity t r) / 2 := by
  unfold liClockCriticalEvenRadialDensity liClockCriticalPositiveRadialDensity
    liClockCriticalOscillatoryRadialDensity
  rw [liClockCriticalEvenKernel_eq_half]
  ring

private theorem cg_positive_density_integrable {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (liClockCriticalPositiveRadialDensity t) (Ioi 0) := by
  have h := ((cg_even_density_integrable ht).const_mul 2).sub
    (liClockCriticalOscillatoryRadialDensity_integrable_bound ht).1
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro r _
  change 2 * liClockCriticalEvenRadialDensity t r - liClockCriticalOscillatoryRadialDensity t r =
    liClockCriticalPositiveRadialDensity t r
  have he := cg_density_half t r
  linarith

private theorem cg_planar_test_integral_eq_polar (t : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ p in (fun p : ℝ × ℝ => p.1^2 + p.2^2) ⁻¹' s, cg_planar_pdf t p) =
      ∫ r in Ioi 0, ∫ θ in Ioo (-Real.pi) Real.pi,
        if r^2 ∈ s then r * cg_planar_pdf t (polarCoord.symm (r, θ)) else 0 := by
  let A := (fun p : ℝ × ℝ => p.1^2 + p.2^2) ⁻¹' s
  let f := A.indicator (cg_planar_pdf t)
  have hA : MeasurableSet A := (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1^2 + p.2^2)) hs
  have hf : Integrable f := (cg_translated_gaussian_pdf_integrable t).indicator hA
  have hp := cg_polar_integrable hf
  calc
    _ = ∫ p, f p := (integral_indicator hA).symm
    _ = ∫ p in polarCoord.target, p.1 * f (polarCoord.symm p) := by
      simpa only [smul_eq_mul] using (integral_comp_polarCoord_symm f).symm
    _ = ∫ r in Ioi 0, ∫ θ in Ioo (-Real.pi) Real.pi,
        r * f (polarCoord.symm (r, θ)) := setIntegral_prod _ hp
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      simp only [f, A, Set.indicator_apply, mem_preimage, cg_polar_radius_sq,
        mul_ite, mul_zero]

/-- For `t ≥ 0`, integrating the shifted planar Gaussian density over the circle of radius `r`
gives `2 r · ½ e^{-2t - r²/2} K(t r²)`. -/
private theorem cg_planar_angular_integral {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, r * cg_planar_pdf t (polarCoord.symm (r, θ))) =
      2 * r * liClockCriticalPositiveRadialDensity t (r^2) := by
  have ha := liClockCriticalAngularIntegral_real_exp (2 * Real.sqrt t * r)
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at ha
  have hq : (2 * Real.sqrt t * r)^2 / 4 = t * r^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    ring
  rw [hq] at ha
  have he : (fun θ : ℝ => r * cg_planar_pdf t (polarCoord.symm (r, θ))) =
      (fun θ : ℝ => (r * (2 * Real.pi)⁻¹ * Real.exp (-2 * t - r^2 / 2)) *
        Real.exp ((2 * Real.sqrt t * r) * Real.cos θ)) := by
    funext θ
    rw [cg_planar_pdf_polar ht]
    ring
  rw [he, integral_const_mul, ha]
  unfold liClockCriticalPositiveRadialDensity
  field_simp [Real.pi_ne_zero]

/-- For `t ≥ 0`, the law of `R²_t` is the measure on `(0, ∞)` with density
`½ e^{-2t - r/2} K(t r)`. -/
theorem liClockCriticalRadialGaussian_eq_withDensity {t : ℝ} (ht : 0 ≤ t) :
    liClockCriticalRadialGaussian t = (volume.restrict (Ioi 0)).withDensity
      (fun r => ENNReal.ofReal (liClockCriticalPositiveRadialDensity t r)) := by
  ext s hs
  have hi : IntegrableOn (s.indicator (liClockCriticalPositiveRadialDensity t)) (Ioi 0) :=
    (cg_positive_density_integrable ht).indicator hs
  rw [cg_radial_gaussian_apply_eq_integral t hs, cg_planar_test_integral_eq_polar t hs]
  have he : (fun r : ℝ => ∫ θ in Ioo (-Real.pi) Real.pi,
      if r^2 ∈ s then r * cg_planar_pdf t (polarCoord.symm (r, θ)) else 0) =
      (fun r : ℝ => 2 * r * s.indicator (liClockCriticalPositiveRadialDensity t) (r^2)) := by
    funext r
    by_cases hr : r^2 ∈ s
    · simp only [if_pos hr, Set.indicator_of_mem hr, cg_planar_angular_integral ht]
    · simp only [if_neg hr, Set.indicator_of_notMem hr, mul_zero, integral_zero]
  rw [he, cg_squared_radius_integral]
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_indicator hs]
  · exact (cg_positive_density_integrable ht).integrableOn
  · have hpos : ∀ᵐ r ∂(volume.restrict (Ioi 0)), 0 ≤ liClockCriticalPositiveRadialDensity t r :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun r hr => by
        unfold liClockCriticalPositiveRadialDensity
        exact mul_nonneg (by positivity) (liClockCriticalPositiveKernel_nonneg (mul_nonneg ht hr.le))))
    exact (ae_restrict_iff' hs).mpr (hpos.mono (fun r hr _ => hr))

/-- For `t ≥ 0`, the cutoff measure `μ_t` is finite. -/
theorem isFiniteMeasure_liClockCriticalCutoffMeasure {t : ℝ} (ht : 0 ≤ t) :
    IsFiniteMeasure (liClockCriticalCutoffMeasure t) :=
  isFiniteMeasure_withDensity_ofReal (cg_even_density_integrable ht).hasFiniteIntegral

theorem nullSingletonClass_liClockCriticalCutoffMeasure (t : ℝ) :
    NullSingletonClass (liClockCriticalCutoffMeasure t) := by
  unfold liClockCriticalCutoffMeasure
  infer_instance


private theorem cg_even_density_nonneg (t r : ℝ) :
    0 ≤ liClockCriticalEvenRadialDensity t r := by
  unfold liClockCriticalEvenRadialDensity
  exact mul_nonneg (by positivity) (liClockCriticalEvenKernel_nonneg _)

private theorem cg_restricted_density_real {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi 0)) (hpos : 0 ≤ᵐ[volume.restrict (Ioi 0)] f)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ((volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (f r))).real s =
      ∫ r in s ∩ Ioi 0, f r := by
  have hp : 0 ≤ᵐ[(volume.restrict (Ioi 0)).restrict s] f :=
    (ae_restrict_iff' hs).mpr (hpos.mono (fun r hr _ => hr))
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn hp,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hp), Measure.restrict_restrict hs]

private theorem cg_positive_density_nonneg_ae {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ᵐ[volume.restrict (Ioi 0)] liClockCriticalPositiveRadialDensity t :=
  (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun r hr => by
    unfold liClockCriticalPositiveRadialDensity
    exact mul_nonneg (by positivity) (liClockCriticalPositiveKernel_nonneg (mul_nonneg ht hr.le))))

/-- For `t ≥ 0` and measurable `s`, `μ_t(s) = (P(R²_t ∈ s) + ∫_{s ∩ (0,∞)} ½ e^{-2t - r/2} K⁻(t r) dr) / 2`. -/
theorem liClockCriticalCutoffMeasure_real_eq_half {t : ℝ} (ht : 0 ≤ t)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (liClockCriticalCutoffMeasure t).real s =
      ((liClockCriticalRadialGaussian t).real s +
        ∫ r in s ∩ Ioi 0, liClockCriticalOscillatoryRadialDensity t r) / 2 := by
  rw [liClockCriticalCutoffMeasure, cg_restricted_density_real (cg_even_density_integrable ht)
    (ae_of_all _ (cg_even_density_nonneg t)) hs,
    liClockCriticalRadialGaussian_eq_withDensity ht,
    cg_restricted_density_real (cg_positive_density_integrable ht) (cg_positive_density_nonneg_ae ht) hs]
  have hp : IntegrableOn (liClockCriticalPositiveRadialDensity t) (s ∩ Ioi 0) := by
    simpa only [IntegrableOn, Measure.restrict_restrict hs, Real.norm_eq_abs] using (cg_positive_density_integrable ht).integrableOn (s := s)
  have ho : IntegrableOn (liClockCriticalOscillatoryRadialDensity t) (s ∩ Ioi 0) := by
    simpa only [IntegrableOn, Measure.restrict_restrict hs, Real.norm_eq_abs] using
      (liClockCriticalOscillatoryRadialDensity_integrable_bound ht).1.integrableOn (s := s)
  simp_rw [cg_density_half]
  rw [integral_div, integral_add hp ho]

/-- For `t ≥ 0`, the cutoff measure has total mass at most `1`. -/
theorem liClockCriticalCutoffMeasure_mass_le_one {t : ℝ} (ht : 0 ≤ t) :
    (liClockCriticalCutoffMeasure t).real univ ≤ 1 := by
  letI := isProbabilityMeasure_liClockCriticalRadialGaussian t
  have ho := (liClockCriticalOscillatoryRadialDensity_integrable_bound ht).2
  have hn : |∫ r in Ioi 0, liClockCriticalOscillatoryRadialDensity t r| ≤
      ∫ r in Ioi 0, |liClockCriticalOscillatoryRadialDensity t r| := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (μ := volume.restrict (Ioi 0)) (liClockCriticalOscillatoryRadialDensity t))
  have hbound : (∫ r in Ioi 0, liClockCriticalOscillatoryRadialDensity t r) ≤ Real.exp (-2 * t) :=
    (le_abs_self _).trans (hn.trans ho)
  have he : Real.exp (-2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [liClockCriticalCutoffMeasure_real_eq_half ht MeasurableSet.univ, probReal_univ, univ_inter]
  linarith

/-- For `t ≥ 0`, `L > 0`: `μ_t([0, L]) = ∫_{[0,L]} ½ e^{-2t - r/2} E(t r) dr`. -/
theorem liClockCriticalCutoffMeasure_real_Icc {t L : ℝ} (ht : 0 ≤ t) (_hL : 0 < L) :
    (liClockCriticalCutoffMeasure t).real (Icc 0 L) =
      ∫ r in Icc 0 L, liClockCriticalEvenRadialDensity t r := by
  rw [liClockCriticalCutoffMeasure,
    cg_restricted_density_real (cg_even_density_integrable ht) (ae_of_all _ (cg_even_density_nonneg t))
      measurableSet_Icc]
  have he : Icc 0 L ∩ Ioi 0 = Ioc 0 L := by
    ext r
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · intro h; exact ⟨h.2, h.1.2⟩
    · intro h; exact ⟨⟨h.1.le, h.2⟩, h.1⟩
  rw [he, integral_Icc_eq_integral_Ioc]

private theorem cg_oscillatory_setIntegral_abs_le {t : ℝ} (ht : 0 ≤ t)
    {s : Set ℝ} (hs : MeasurableSet s) :
    |∫ r in s ∩ Ioi 0, liClockCriticalOscillatoryRadialDensity t r| ≤ Real.exp (-2 * t) := by
  have ho := (liClockCriticalOscillatoryRadialDensity_integrable_bound ht).1
  calc
    _ ≤ ∫ r in s ∩ Ioi 0, |liClockCriticalOscillatoryRadialDensity t r| := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (μ := volume.restrict (s ∩ Ioi 0)) (liClockCriticalOscillatoryRadialDensity t))
    _ ≤ ∫ r in Ioi 0, |liClockCriticalOscillatoryRadialDensity t r| := by
      simpa only [IntegrableOn, Measure.restrict_restrict hs, Real.norm_eq_abs] using
        (setIntegral_le_integral (s := s) ho.norm (ae_of_all _ (fun r => norm_nonneg _)))
    _ ≤ _ := (liClockCriticalOscillatoryRadialDensity_integrable_bound ht).2

/-- In the critical window (`L → ∞`, `(t - L/4)/√L → u`), `μ_t([0, L]) → Φ(-2u)/2`. -/
theorem tendsto_liClockCriticalCutoffMeasure_cutoff {L t : ℕ → ℝ} {u : ℝ}
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
    Tendsto (fun n => (liClockCriticalCutoffMeasure (t n)).real (Icc 0 (L n)))
      atTop (nhds (liClockCriticalGaussianCDF (-2 * u) / 2)) := by
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  have htp : ∀ᶠ n in atTop, 0 ≤ t n := (ht.eventually (eventually_gt_atTop 0)).mono (fun n h => h.le)
  have he : Tendsto (fun n => Real.exp (-2 * t n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (by norm_num : (-2 : ℝ) < 0) ht)
  have ho : Tendsto (fun n => ∫ r in Icc 0 (L n) ∩ Ioi 0,
      liClockCriticalOscillatoryRadialDensity (t n) r) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [htp] with n hn
    exact cg_oscillatory_setIntegral_abs_le hn measurableSet_Icc
  have hm := ((tendsto_liClockCriticalRadialGaussian_cutoff hL hT).add ho).div_const 2
  simp only [add_zero] at hm
  apply hm.congr'
  filter_upwards [htp] with n hn
  exact (liClockCriticalCutoffMeasure_real_eq_half hn measurableSet_Icc).symm


/-- For a finite measure of mass `≤ 1` and `0 < K < L`, the exponentially weighted cutoff
`∫_{[0,L]} e^{-(L - r)} dμ` lies in `[0, e^{-K} + μ([L - K, L])]`. -/
private theorem cg_cutoff_loss_split {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hmass : μ.real univ ≤ 1) {K L : ℝ} (_hK : 0 < K) (hKL : K < L) :
    0 ≤ (∫ r in Icc 0 L, Real.exp (-(L-r)) ∂μ) ∧
    (∫ r in Icc 0 L, Real.exp (-(L-r)) ∂μ) ≤
      Real.exp (-K) + μ.real (Icc (L-K) L) := by
  have hsub : Icc (L-K) L ⊆ Icc 0 L := by
    intro r hr
    exact ⟨le_trans (sub_pos.mpr hKL).le hr.1, hr.2⟩
  have hf : IntegrableOn (fun r : ℝ => Real.exp (-(L-r))) (Icc 0 L) μ :=
    (show Continuous (fun r : ℝ => Real.exp (-(L-r))) by fun_prop).integrableOn_Icc
  have hc : Integrable (fun _ : ℝ => Real.exp (-K)) (μ.restrict (Icc 0 L)) :=
    integrable_const _
  have hb : Integrable ((Icc (L-K) L).indicator (fun _ : ℝ => (1 : ℝ)))
      (μ.restrict (Icc 0 L)) := (integrable_const _).indicator measurableSet_Icc
  have hbound : ∀ᵐ r ∂μ.restrict (Icc 0 L), Real.exp (-(L-r)) ≤
      Real.exp (-K) + (Icc (L-K) L).indicator (fun _ : ℝ => (1 : ℝ)) r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    by_cases h : L-K ≤ r
    · rw [Set.indicator_of_mem (show r ∈ Icc (L-K) L from ⟨h, hr.2⟩)]
      have he : Real.exp (-(L-r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sub_nonneg.mpr hr.2))
      linarith [Real.exp_pos (-K)]
    · have hrb : r ∉ Icc (L-K) L := fun hrb => h hrb.1
      simp only [Set.indicator_apply, if_neg hrb, add_zero]
      exact Real.exp_le_exp.mpr (by linarith)
  have hband_int : (∫ r in Icc 0 L,
      (Icc (L-K) L).indicator (fun _ : ℝ => (1 : ℝ)) r ∂μ) = μ.real (Icc (L-K) L) := by
    have h := integral_indicator_one (μ := μ.restrict (Icc 0 L))
      (s := Icc (L-K) L) measurableSet_Icc
    rw [measureReal_restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hsub] at h
    simpa only [Set.indicator_apply, Pi.one_apply] using h
  have hmassI : μ.real (Icc 0 L) ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans hmass
  refine ⟨integral_nonneg (fun _ => (Real.exp_pos _).le), ?_⟩
  calc
    _ ≤ ∫ r in Icc 0 L, Real.exp (-K) +
        (Icc (L-K) L).indicator (fun _ : ℝ => (1 : ℝ)) r ∂μ :=
      integral_mono_ae hf (hc.add hb) hbound
    _ = μ.real (Icc 0 L) * Real.exp (-K) + μ.real (Icc (L-K) L) := by
      rw [integral_add hc hb, integral_const, measureReal_restrict_apply_univ,
        hband_int, smul_eq_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hmassI (Real.exp_pos (-K)).le
      linarith


private theorem cg_window_sub_const {L t : ℕ → ℝ} {u K : ℝ}
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
    Tendsto (fun n => L n - K) atTop atTop ∧
    Tendsto (fun n => (t n - (L n - K) / 4) / Real.sqrt (L n - K)) atTop (nhds u) := by
  have hLk : Tendsto (fun n => L n - K) atTop atTop := by
    apply tendsto_atTop_atTop.2
    intro b
    obtain ⟨i, hi⟩ := tendsto_atTop_atTop.1 hL (b + K)
    refine ⟨i, fun n hn => ?_⟩
    have h := hi n hn
    linarith
  have hq : Tendsto (fun n => L n / (L n - K)) atTop (nhds (1 : ℝ)) := by
    have h : Tendsto (fun n => (1 : ℝ) + K / (L n - K)) atTop (nhds 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add (hLk.const_div_atTop K)
    apply h.congr'
    filter_upwards [hLk.eventually (eventually_gt_atTop 0)] with n hn
    field_simp [hn.ne']
    ring
  have hs : Tendsto (fun n => Real.sqrt (L n) / Real.sqrt (L n - K)) atTop (nhds (1 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hq
    simp only [Real.sqrt_one] at h
    apply h.congr'
    filter_upwards [hL.eventually (eventually_gt_atTop 0)] with n hn
    change Real.sqrt (L n / (L n - K)) = Real.sqrt (L n) / Real.sqrt (L n - K)
    rw [Real.sqrt_div hn.le]
  have hc : Tendsto (fun n => K / (4 * Real.sqrt (L n - K))) atTop (nhds (0 : ℝ)) := by
    simpa only [div_mul_eq_div_div, Function.comp_apply] using
      (Real.tendsto_sqrt_atTop.comp hLk).const_div_atTop (K / 4)
  have h := (hT.mul hs).add hc
  refine ⟨hLk, ?_⟩
  simp only [mul_one, add_zero] at h
  apply h.congr'
  filter_upwards [hL.eventually (eventually_gt_atTop 0),
    hLk.eventually (eventually_gt_atTop 0)] with n hn hkn
  have hl : Real.sqrt (L n) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hk : Real.sqrt (L n - K) ≠ 0 := (Real.sqrt_pos.mpr hkn).ne'
  field_simp [hl, hk]
  ring

private theorem cg_band_measure_eq {μ : Measure ℝ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] {K L : ℝ} (hK : 0 < K) (hKL : K < L) :
    μ.real (Icc (L - K) L) = μ.real (Icc 0 L) - μ.real (Icc 0 (L - K)) := by
  have hsub : Icc 0 (L - K) ⊆ Icc 0 L := by
    intro r hr
    exact ⟨hr.1, hr.2.trans (by linarith)⟩
  have he : Icc 0 L \ Icc 0 (L - K) = Ioc (L - K) L := by
    ext r
    simp only [Set.mem_sdiff, mem_Icc, mem_Ioc]
    constructor
    · intro h
      constructor
      · by_contra hn
        exact h.2 ⟨h.1.1, le_of_not_gt hn⟩
      · exact h.1.2
    · intro h
      exact ⟨⟨le_trans (sub_pos.mpr hKL).le h.1.le, h.2⟩, fun hr => (not_le_of_gt h.1) hr.2⟩
  rw [← measureReal_sdiff hsub measurableSet_Icc, he]
  exact measureReal_congr Ioc_ae_eq_Icc.symm

/-- In the critical window, for fixed `K > 0`, the band mass `μ_t([L - K, L])` tends to `0`. -/
theorem tendsto_liClockCriticalCutoffMeasure_band {L t : ℕ → ℝ} {u K : ℝ} (hK : 0 < K)
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
    Tendsto (fun n => (liClockCriticalCutoffMeasure (t n)).real (Icc (L n - K) (L n)))
      atTop (nhds 0) := by
  have hw := cg_window_sub_const (K := K) hL hT
  have h := (tendsto_liClockCriticalCutoffMeasure_cutoff hL hT).sub
    (tendsto_liClockCriticalCutoffMeasure_cutoff hw.1 hw.2)
  simp only [sub_self] at h
  apply h.congr'
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  filter_upwards [ht.eventually (eventually_gt_atTop 0), hL.eventually (eventually_gt_atTop K)]
    with n htn hn
  letI := isFiniteMeasure_liClockCriticalCutoffMeasure htn.le
  letI := nullSingletonClass_liClockCriticalCutoffMeasure (t n)
  exact (cg_band_measure_eq hK hn).symm

/-- For `t ≥ 0` and `0 < K < L`, `0 ≤ loss(t, L) ≤ e^{-K} + μ_t([L - K, L])`. -/
theorem liClockCriticalCutoffLoss_split_bound {t L K : ℝ} (ht : 0 ≤ t)
    (hK : 0 < K) (hKL : K < L) :
    0 ≤ liClockCriticalCutoffLoss t L ∧
    liClockCriticalCutoffLoss t L ≤ Real.exp (-K) +
      (liClockCriticalCutoffMeasure t).real (Icc (L - K) L) := by
  letI := isFiniteMeasure_liClockCriticalCutoffMeasure ht
  exact cg_cutoff_loss_split (liClockCriticalCutoffMeasure_mass_le_one ht) hK hKL

/-- In the critical window (`L → ∞`, `(t - L/4)/√L → u`), the cutoff loss
`∫_{[0,L]} e^{-(L - r)} dμ_t(r)` tends to `0`. -/
theorem tendsto_liClockCriticalCutoffLoss {L t : ℕ → ℝ} {u : ℝ}
    (hL : Tendsto L atTop atTop)
    (hT : Tendsto (fun n => (t n - L n / 4) / Real.sqrt (L n)) atTop (nhds u)) :
    Tendsto (fun n => liClockCriticalCutoffLoss (t n) (L n)) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)
  obtain ⟨K, hK, heK⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  have hb := (tendsto_liClockCriticalCutoffMeasure_band hK hL hT).eventually_lt_const
    (show (0 : ℝ) < ε / 2 by linarith)
  have ht := (liClockCriticalWindow_kinematics hL hT).1
  filter_upwards [ht.eventually (eventually_gt_atTop 0), hL.eventually (eventually_gt_atTop K), hb]
    with n htn hn hbn
  have hs := liClockCriticalCutoffLoss_split_bound htn.le hK hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
  linarith

/-- Raw form of the loss: `e^{-2t} ∫₀ᴸ e^{-L + r/2} E(t r) dr = 2 · loss(t, L)`. -/
theorem liClockCriticalCutoffLoss_raw_integral {t L : ℝ} (_ht : 0 ≤ t) (_hL : 0 < L) :
    Real.exp (-2 * t) *
      (∫ r in Icc 0 L, Real.exp (-L + r / 2) * liClockCriticalEvenKernel (t * r)) =
      2 * liClockCriticalCutoffLoss t L := by
  have hm : Continuous (liClockCriticalEvenRadialDensity t) := by
    unfold liClockCriticalEvenRadialDensity
    exact ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).mul
      (continuous_liClockCriticalEvenKernel.comp (continuous_const.mul continuous_id)))
  have hfinite : ∀ᵐ r ∂(volume.restrict (Ioi 0)).restrict (Icc 0 L),
      ENNReal.ofReal (liClockCriticalEvenRadialDensity t r) < ∞ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  unfold liClockCriticalCutoffLoss liClockCriticalCutoffMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hm.measurable.ennreal_ofReal hfinite _
    measurableSet_Icc]
  simp_rw [ENNReal.toReal_ofReal (cg_even_density_nonneg t _), smul_eq_mul]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have he : Icc 0 L ∩ Ioi 0 = Ioc 0 L := by
    ext r
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · intro h; exact ⟨h.2, h.1.2⟩
    · intro h; exact ⟨⟨h.1.le, h.2⟩, h.1⟩
  rw [he, ← integral_Icc_eq_integral_Ioc]
  have hf : (fun r : ℝ => liClockCriticalEvenRadialDensity t r * Real.exp (-(L - r))) =
      (fun r : ℝ => ((1 / 2 : ℝ) * Real.exp (-2 * t)) *
        (Real.exp (-L + r / 2) * liClockCriticalEvenKernel (t * r))) := by
    funext r
    unfold liClockCriticalEvenRadialDensity
    calc
      _ = (1 / 2 : ℝ) * (Real.exp (-2 * t - r / 2) * Real.exp (-(L - r))) *
          liClockCriticalEvenKernel (t * r) := by ring
      _ = _ := by
        rw [← Real.exp_add,
          show (-2 * t - r / 2) + -(L - r) = -2 * t + (-L + r / 2) by ring, Real.exp_add]
        ring
  rw [hf, integral_const_mul]
  ring

end RHTower
end
