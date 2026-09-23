import GaloisForLFunctions.HTGeometry.DaiYoshikawa.ExponentialIntegralSmall
import GaloisForLFunctions.HTGeometry.EvenPowerCanonicalProductDA
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact FZZ cigar backreaction criticality

For the FZZ-compatible Horowitz--Polchinski reduction of the Euclidean
`SL(2,ℝ)ₖ/U(1)` black-hole cigar, write `x = χ²` and `y = h²`.  At infinite level the
metric equation becomes

`y' = y - 1/x`.

The 2025 analytic solution of Ishibashi--Matsuo--Tanaka is therefore

`y(x) = exp(x) (C + E₁(x))`,

where `E₁(x) = ∫_x^∞ exp(-t) dt/t`.  This file verifies that solution and its exact conserved
puncture charge.  Matching the exterior winding amplitude gives

`C(A) = γ + 2 log A`,

so the puncture chamber `C = 0` selects `A = exp(-γ/2)` without numerical integration.

At finite level, put `a = 1/k`.  The reduced HP critical amplitude and exact worldsheet-SCFT
amplitude have normalized fourth-power bases

`A_HP^(4/k) = Γ(1-a)⁻²`,
`A_string^(4/k) = Γ(1+a) / Γ(1-a)`.

Their ratio is exactly

`Γ(1+a) Γ(1-a) = πa / sin(πa) = sincProduct(a)⁻¹ > 1`

for `0 < a < 1`.  This proves analytically the systematic finite-`k` mismatch observed
numerically by Krishnan--Talukdar and identifies the required positive `α'` correction as the
full Euler sine tower.  No Riemann-hypothesis claim is made here: this is black-hole/string
backreaction input for a later full-winding endpoint.

Physics sources:

* Brustein--Giveon--Itzhaki--Zigdon, *A Puncture in the Euclidean Black Hole*,
  arXiv:2112.03048.
* Krishnan--Talukdar, *A Vestige of FZZ Duality in Higher Dimensions*, arXiv:2411.16669.
* Ishibashi--Matsuo--Tanaka, *Self-gravitating strings and quantum effects in two-dimensional
  gravity*, arXiv:2506.09586.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FZZCigar

private theorem hasDerivAt_integral_Ioi_real
    {f : ℝ → ℝ} {c y : ℝ} (hcy : c < y)
    (hint : IntegrableOn f (Ioi c) volume)
    (hmeas : StronglyMeasurableAtFilter f (nhds y) volume)
    (hcont : ContinuousAt f y) :
    HasDerivAt (fun u : ℝ => ∫ t in Ioi u, f t) (-f y) y := by
  have hII : IntervalIntegrable f volume c y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcy.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt
      (fun u : ℝ => (∫ t in Ioi c, f t) - ∫ t in c..u, f t) (-f y) y := by
    have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas hcont
    simpa using hbase.const_sub (∫ t in Ioi c, f t)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcy] with u hu
  have hcu : c ≤ u := hu.le
  have hsplit : Ioc c u ∪ Ioi u = Ioi c := Ioc_union_Ioi_eq_Ioi hcu
  have hdisj : Disjoint (Ioc c u) (Ioi u) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht2⟩ ht3
    exact absurd ht3 (not_lt.mpr ht2)
  have hunion : (∫ t in Ioi c, f t) =
      (∫ t in Ioc c u, f t) + ∫ t in Ioi u, f t := by
    rw [← hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi hcu))
  rw [intervalIntegral.integral_of_le hcu, hunion]
  ring

/-- Derivative of the literal exponential-integral tail used by the exact FZZ cap solution. -/
theorem hasDerivAt_expIntegralE1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt DaiYoshikawa.expIntegralE1 (-Real.exp (-x) / x) x := by
  let c : ℝ := min 1 (x / 2)
  have hc0 : 0 < c := by
    dsimp [c]
    exact lt_min zero_lt_one (half_pos hx)
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact min_le_left _ _
  have hcx : c < x :=
    lt_of_le_of_lt (by dsimp [c]; exact min_le_right _ _) (half_lt_self hx)
  have hhead : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioc c 1) := by
    have h := RHTower.intervalIntegrable_exp_neg_div hc0 hc1
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hc1] at h
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi c) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc1]
    exact hhead.union RHTower.integrableOn_exp_neg_div_Ioi_one
  have hcont (t : ℝ) (ht : 0 < t) :
      ContinuousAt (fun u : ℝ => Real.exp (-u) / u) t := by
    exact ((Real.continuous_exp.comp continuous_neg).continuousAt).div
      continuousAt_id ht.ne'
  have hsm : StronglyMeasurableAtFilter
      (fun t : ℝ => Real.exp (-t) / t) (nhds x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun t ht => hcont t ht) x hx
  have h := hasDerivAt_integral_Ioi_real hcx hInt hsm (hcont x hx)
  change HasDerivAt (fun u : ℝ => ∫ t in Ioi u, Real.exp (-t) / t)
    (-Real.exp (-x) / x) x
  simpa only [neg_div] using h

/-- Exact squared cigar radius `h²` as a function of squared winding condensate `x = χ²`
at `k = ∞`.  `C` is the nonlinear tip/puncture/hole chamber coordinate. -/
def capMetricSq (C x : ℝ) : ℝ :=
  Real.exp x * (C + DaiYoshikawa.expIntegralE1 x)

/-- The analytic FZZ cap profile solves `y' = y - 1/x` on the physical ray. -/
theorem capMetricSq_ode (C : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (capMetricSq C) (capMetricSq C x - 1 / x) x := by
  have hE := hasDerivAt_expIntegralE1 hx
  have hprod := (Real.hasDerivAt_exp x).mul (hasDerivAt_const x C |>.add hE)
  refine hprod.congr_deriv ?_
  rw [capMetricSq]
  field_simp [hx.ne']
  ring_nf
  rw [show Real.exp x * Real.exp (-x) = 1 by rw [← Real.exp_add]; simp]
  simp only [Pi.add_apply]
  ring

/-- Exact integrating-factor charge of the infinite-level FZZ cap. -/
theorem capMetricSq_charge (C x : ℝ) :
    Real.exp (-x) * capMetricSq C x - DaiYoshikawa.expIntegralE1 x = C := by
  rw [capMetricSq]
  rw [← mul_assoc]
  rw [show Real.exp (-x) * Real.exp x = 1 by rw [← Real.exp_add]; simp]
  ring

/-- Exterior winding amplitude expressed in the conserved infinite-level FZZ chamber coordinate. -/
def capCharge (A : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + 2 * Real.log A

/-- The critical puncture charge vanishes exactly at the string amplitude `exp(-γ/2)`. -/
theorem capCharge_eq_zero_iff {A : ℝ} (hA : 0 < A) :
    capCharge A = 0 ↔ A = Real.exp (-Real.eulerMascheroniConstant / 2) := by
  constructor
  · intro h
    have hlog : Real.log A = -Real.eulerMascheroniConstant / 2 := by
      rw [capCharge] at h
      linarith
    rw [← Real.exp_log hA]
    exact congrArg Real.exp hlog
  · intro h
    rw [h, capCharge, Real.log_exp]
    ring

/-- Fourth-power base of the finite-level critical amplitude predicted by the reduced HP flow.
For `a = 1/k`, this equals `A_HP^(4/k)`. -/
def hpCriticalAmplitudeBase (a : ℝ) : ℝ :=
  (Real.Gamma (1 - a))⁻¹ ^ (2 : ℕ)

/-- Fourth-power base of the exact finite-level worldsheet winding amplitude.
For `a = 1/k`, this equals `A_string^(4/k)`. -/
def stringAmplitudeBase (a : ℝ) : ℝ :=
  Real.Gamma (1 + a) / Real.Gamma (1 - a)

/-- Normalized finite-level string/HP criticality mismatch. -/
def criticalOvershootBase (a : ℝ) : ℝ :=
  stringAmplitudeBase a / hpCriticalAmplitudeBase a

/-- Exact Gamma-reflection form of the finite-level criticality mismatch. -/
theorem criticalOvershootBase_eq_sine {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    criticalOvershootBase a = Real.pi * a / Real.sin (Real.pi * a) := by
  have hgm : Real.Gamma (1 - a) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [criticalOvershootBase, stringAmplitudeBase, hpCriticalAmplitudeBase]
  rw [show 1 + a = a + 1 by ring, Real.Gamma_add_one ha0.ne']
  calc
    a * Real.Gamma a / Real.Gamma (1 - a) /
          (Real.Gamma (1 - a))⁻¹ ^ (2 : ℕ) =
        a * (Real.Gamma a * Real.Gamma (1 - a)) := by
          field_simp [hgm]
    _ = a * (Real.pi / Real.sin (Real.pi * a)) := by
      rw [Real.Gamma_mul_Gamma_one_sub]
    _ = Real.pi * a / Real.sin (Real.pi * a) := by ring

/-- Exact string amplitude is strictly supercritical for every finite physical level `k > 1`. -/
theorem one_lt_criticalOvershootBase {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    1 < criticalOvershootBase a := by
  rw [criticalOvershootBase_eq_sine ha0 ha1]
  have hx0 : 0 < Real.pi * a := mul_pos Real.pi_pos ha0
  have hxpi : Real.pi * a < Real.pi := by nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  exact (lt_div_iff₀ hsin0).2 (by simpa using Real.sin_lt hx0)

/-- The finite-level criticality mismatch is the inverse Euler sine canonical product.  Thus the
required `α'` correction is an entire infinite-mode tower, not a finite perturbative coefficient. -/
theorem criticalOvershootBase_eq_inv_sincProduct
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((criticalOvershootBase a : ℝ) : ℂ) =
      (_root_.HTGeometry.sincProduct (a : ℂ))⁻¹ := by
  have hgm : Real.Gamma (1 - a) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [criticalOvershootBase, stringAmplitudeBase, hpCriticalAmplitudeBase]
  rw [show 1 + a = a + 1 by ring, Real.Gamma_add_one ha0.ne']
  rw [_root_.HTGeometry.sincProduct_eq_reciprocalGamma_pair]
  push_cast
  rw [show (a : ℂ) + 1 = ((a + 1 : ℝ) : ℂ) by push_cast; ring,
    show 1 - (a : ℂ) = ((1 - a : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  rw [Real.Gamma_add_one ha0.ne']
  field_simp [hgm]
  all_goals push_cast
  all_goals ring

/-- Positive normalized counterterm that full finite-level string dynamics must supply to move the
bare reduced HP flow back to the exact worldsheet critical surface. -/
def alphaPrimeCriticalCountertermBase (a : ℝ) : ℝ :=
  criticalOvershootBase a - 1

theorem alphaPrimeCriticalCountertermBase_pos
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < alphaPrimeCriticalCountertermBase a := by
  rw [alphaPrimeCriticalCountertermBase]
  linarith [one_lt_criticalOvershootBase ha0 ha1]

end FZZCigar

end

end GaloisForLFunctions.HTGeometry
