import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.HTGeometry.BlockWindowFubini

/-!
# Laplace transform of a half-line Volterra convolution with an exponential kernel

For a real source `φ` of at most linear growth and a decaying exponential kernel `exp(-b u)`,
the causal convolution

```text
(exp(-b ·) * φ)(t) = ∫_0^t exp(-b(t-h)) φ(h) dh
```

has Laplace transform `(z+b)^(-1) L[φ](z)` on the right half-plane.  This is the exponential case
of the Laplace convolution theorem; it is all that the unit-Riesz completed-source weld needs,
because both the aperture kernel and the completed-error test kernel are finite combinations of
pure decaying exponentials.

The proof is a Fubini interchange over the causal wedge with the product majorant
`exp(-σ t/2) · C(1+h) exp(-σ h/2)`, which dominates the wedge integrand because `h ≤ t` there.

Unconditional; no arithmetic input.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

theorem mul_exp_neg_le_inv {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) :
    h * Real.exp (-(c * h)) ≤ 1 / c := by
  have hexp : c * h + 1 ≤ Real.exp (c * h) := Real.add_one_le_exp _
  have hpos : 0 < Real.exp (c * h) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hpos hc]
  nlinarith

theorem one_add_mul_exp_neg_le {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) :
    (1 + h) * Real.exp (-(c * h)) ≤ 1 + 1 / c := by
  have h1 : Real.exp (-(c * h)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have h2 := mul_exp_neg_le_inv hc hh
  nlinarith [Real.exp_pos (-(c * h))]

/-- Causal exponential-kernel Volterra integrand, extended by zero above the diagonal. -/
def expVolterraIntegrand (b : ℝ) (z : ℂ) (φ : ℝ → ℝ) (t h : ℝ) : ℂ :=
  if h ≤ t then
    Complex.exp (-(z * (t : ℂ))) * Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * (φ h : ℂ)
  else 0

theorem measurable_uncurry_expVolterraIntegrand
    (b : ℝ) (z : ℂ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (Function.uncurry (expVolterraIntegrand b z φ)) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hcont : Measurable fun p : ℝ × ℝ =>
      Complex.exp (-(z * (p.1 : ℂ))) *
        Complex.exp (-((b : ℂ) * ((p.1 : ℂ) - (p.2 : ℂ)))) * ((φ p.2 : ℝ) : ℂ) := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact (Complex.measurable_exp.comp
        (((Complex.measurable_ofReal.comp measurable_fst).const_mul z).neg))
    · exact (Complex.measurable_exp.comp
        ((((Complex.measurable_ofReal.comp measurable_fst).sub
          (Complex.measurable_ofReal.comp measurable_snd)).const_mul (b : ℂ)).neg))
    · exact Complex.measurable_ofReal.comp (hφ.comp measurable_snd)
  have heq : Function.uncurry (expVolterraIntegrand b z φ) =
      fun p : ℝ × ℝ =>
        if p.2 ≤ p.1 then
          Complex.exp (-(z * (p.1 : ℂ))) *
            Complex.exp (-((b : ℂ) * ((p.1 : ℂ) - (p.2 : ℂ)))) * ((φ p.2 : ℝ) : ℂ)
        else 0 := by
    funext p
    rfl
  rw [heq]
  exact Measurable.ite hset hcont measurable_const

/-- Inner slice of the causal wedge: the Volterra convolution at aperture `t`. -/
theorem integral_expVolterraIntegrand_snd
    {b : ℝ} {z : ℂ} {φ : ℝ → ℝ} (hφ : Measurable φ) {t : ℝ} (ht : 0 < t) :
    (∫ h in Ioi (0 : ℝ), expVolterraIntegrand b z φ t h) =
      Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * φ h : ℝ) : ℂ) := by
  have hind : ∀ h : ℝ, expVolterraIntegrand b z φ t h =
      Set.indicator (Iic t)
        (fun h => Complex.exp (-(z * (t : ℂ))) *
          Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * (φ h : ℂ)) h := by
    intro h
    by_cases hle : h ≤ t
    · simp [expVolterraIntegrand, hle, Set.indicator_of_mem]
    · simp [expVolterraIntegrand, hle, Set.indicator_of_notMem]
  simp_rw [hind]
  rw [setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  rw [← integral_complex_ofReal]
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro h _
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring

/-- Outer slice of the causal wedge: the exponential tail integral. -/
theorem integral_expVolterraIntegrand_fst
    {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : 0 < z.re) {φ : ℝ → ℝ} {h : ℝ} (hh : 0 < h) :
    (∫ t in Ioi (0 : ℝ), expVolterraIntegrand b z φ t h) =
      (z + (b : ℂ))⁻¹ * (Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ)) := by
  have hzb : 0 < (z + (b : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hind : ∀ t : ℝ, expVolterraIntegrand b z φ t h =
      Set.indicator (Ici h)
        (fun t => Complex.exp (-(z * (t : ℂ))) *
          Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * (φ h : ℂ)) t := by
    intro t
    by_cases hle : h ≤ t
    · simp [expVolterraIntegrand, hle, Set.indicator_of_mem]
    · simp [expVolterraIntegrand, hle, Set.indicator_of_notMem]
  simp_rw [hind]
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : Ioi (0 : ℝ) ∩ Ici h = Ici h := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun hx => hx.2, fun hx => ⟨lt_of_lt_of_le hh hx, hx⟩⟩
  rw [hset, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hrw : ∀ t : ℝ,
      Complex.exp (-(z * (t : ℂ))) * Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * (φ h : ℂ) =
        (Complex.exp ((b : ℂ) * (h : ℂ)) * (φ h : ℂ)) *
          Complex.exp (-((z + (b : ℂ)) * (t : ℂ))) := by
    intro t
    rw [show Complex.exp (-(z * (t : ℂ))) * Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ))))
        = Complex.exp (-(z * (t : ℂ)) + -((b : ℂ) * ((t : ℂ) - (h : ℂ)))) from
      (Complex.exp_add _ _).symm]
    rw [show Complex.exp ((b : ℂ) * (h : ℂ)) * (φ h : ℂ) *
        Complex.exp (-((z + (b : ℂ)) * (t : ℂ)))
        = (φ h : ℂ) * (Complex.exp ((b : ℂ) * (h : ℂ)) *
          Complex.exp (-((z + (b : ℂ)) * (t : ℂ)))) from by ring]
    rw [← Complex.exp_add]
    rw [show Complex.exp (-(z * (t : ℂ)) + -((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * (φ h : ℂ)
        = (φ h : ℂ) * Complex.exp (-(z * (t : ℂ)) + -((b : ℂ) * ((t : ℂ) - (h : ℂ)))) from by ring]
    congr 2
    ring
  simp_rw [hrw]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_cexp_neg_mul_shift hzb h]
  have hcollapse : Complex.exp ((b : ℂ) * (h : ℂ)) *
      (Complex.exp (-((z + (b : ℂ)) * (h : ℂ))) / (z + (b : ℂ)))
      = (z + (b : ℂ))⁻¹ * Complex.exp (-(z * (h : ℂ))) := by
    rw [div_eq_mul_inv, ← mul_assoc, ← Complex.exp_add]
    rw [show (b : ℂ) * (h : ℂ) + -((z + (b : ℂ)) * (h : ℂ)) = -(z * (h : ℂ)) from by ring]
    ring
  calc Complex.exp ((b : ℂ) * (h : ℂ)) * (φ h : ℂ) *
        (Complex.exp (-((z + (b : ℂ)) * (h : ℂ))) / (z + (b : ℂ)))
      = (Complex.exp ((b : ℂ) * (h : ℂ)) *
          (Complex.exp (-((z + (b : ℂ)) * (h : ℂ))) / (z + (b : ℂ)))) * (φ h : ℂ) := by ring
    _ = ((z + (b : ℂ))⁻¹ * Complex.exp (-(z * (h : ℂ)))) * (φ h : ℂ) := by rw [hcollapse]
    _ = (z + (b : ℂ))⁻¹ * (Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ)) := by ring

theorem integrableOn_Ioi_rexp_neg_mul {c : ℝ} (hc : 0 < c) (a : ℝ) :
    IntegrableOn (fun h : ℝ => Real.exp (-(c * h))) (Ioi a) volume := by
  refine (exp_neg_integrableOn_Ioi a hc).congr_fun ?_ measurableSet_Ioi
  intro x _
  congr 1
  ring

theorem norm_expVolterraIntegrand_le
    {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : 0 < z.re) {φ : ℝ → ℝ} {C : ℝ}
    (hbnd : ∀ h : ℝ, 0 < h → |φ h| ≤ C * (1 + h))
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    ‖expVolterraIntegrand b z φ t h‖ ≤
      Real.exp (-(z.re / 2 * t)) * (|C| * ((1 + h) * Real.exp (-(z.re / 2 * h)))) := by
  have hX0 : (0 : ℝ) < Real.exp (-(z.re / 2 * t)) := Real.exp_pos _
  have hY0 : (0 : ℝ) < Real.exp (-(z.re / 2 * h)) := Real.exp_pos _
  have hC0 : (0 : ℝ) ≤ |C| := abs_nonneg C
  by_cases hle : h ≤ t
  · rw [expVolterraIntegrand, if_pos hle]
    have hnorm : ‖Complex.exp (-(z * (t : ℂ))) *
          Complex.exp (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))) * ((φ h : ℝ) : ℂ)‖ =
        Real.exp (-(z.re * t)) * Real.exp (-(b * (t - h))) * |φ h| := by
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs]
      congr 2 <;> simp [Complex.mul_re]
    rw [hnorm]
    have hXX : Real.exp (-(z.re * t)) =
        Real.exp (-(z.re / 2 * t)) * Real.exp (-(z.re / 2 * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hXY : Real.exp (-(z.re / 2 * t)) ≤ Real.exp (-(z.re / 2 * h)) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hb1 : Real.exp (-(b * (t - h))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hφ' : |φ h| ≤ |C| * (1 + h) :=
      le_trans (hbnd h hh) (by nlinarith [le_abs_self C])
    have h1h : (0 : ℝ) ≤ 1 + h := by linarith
    rw [hXX]
    calc Real.exp (-(z.re / 2 * t)) * Real.exp (-(z.re / 2 * t)) *
            Real.exp (-(b * (t - h))) * |φ h|
        ≤ Real.exp (-(z.re / 2 * t)) * Real.exp (-(z.re / 2 * t)) * 1 * (|C| * (1 + h)) := by
          refine mul_le_mul ?_ hφ' (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = Real.exp (-(z.re / 2 * t)) *
            (Real.exp (-(z.re / 2 * t)) * (|C| * (1 + h))) := by ring
      _ ≤ Real.exp (-(z.re / 2 * t)) *
            (Real.exp (-(z.re / 2 * h)) * (|C| * (1 + h))) := by
          refine mul_le_mul_of_nonneg_left ?_ hX0.le
          exact mul_le_mul_of_nonneg_right hXY (by positivity)
      _ = Real.exp (-(z.re / 2 * t)) *
            (|C| * ((1 + h) * Real.exp (-(z.re / 2 * h)))) := by ring
  · rw [expVolterraIntegrand, if_neg hle, norm_zero]
    positivity

theorem integrableOn_Ioi_linear_exp_majorant {C σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun h : ℝ => |C| * ((1 + h) * Real.exp (-(σ / 2 * h)))) (Ioi (0 : ℝ)) volume := by
  have hσ4 : (0 : ℝ) < σ / 4 := by linarith
  have hmaj : IntegrableOn
      (fun h : ℝ => (|C| * (1 + 1 / (σ / 4))) * Real.exp (-(σ / 4 * h))) (Ioi (0 : ℝ)) volume :=
    (integrableOn_Ioi_rexp_neg_mul hσ4 0).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : (0 : ℝ) ≤ h := le_of_lt hh
    have hsplit : Real.exp (-(σ / 2 * h)) =
        Real.exp (-(σ / 4 * h)) * Real.exp (-(σ / 4 * h)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpoly := one_add_mul_exp_neg_le hσ4 hh0
    have hpos : (0 : ℝ) < Real.exp (-(σ / 4 * h)) := Real.exp_pos _
    have hC0 : (0 : ℝ) ≤ |C| := abs_nonneg C
    have hnn : (0 : ℝ) ≤ |C| * ((1 + h) * Real.exp (-(σ / 2 * h))) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hsplit]
    have step1 : ((1 + h) * Real.exp (-(σ / 4 * h))) * Real.exp (-(σ / 4 * h)) ≤
        (1 + 1 / (σ / 4)) * Real.exp (-(σ / 4 * h)) :=
      mul_le_mul_of_nonneg_right hpoly hpos.le
    calc |C| * ((1 + h) * (Real.exp (-(σ / 4 * h)) * Real.exp (-(σ / 4 * h))))
        = |C| * (((1 + h) * Real.exp (-(σ / 4 * h))) * Real.exp (-(σ / 4 * h))) := by ring
      _ ≤ |C| * ((1 + 1 / (σ / 4)) * Real.exp (-(σ / 4 * h))) :=
          mul_le_mul_of_nonneg_left step1 hC0
      _ = |C| * (1 + 1 / (σ / 4)) * Real.exp (-(σ / 4 * h)) := by ring

/-- **The exponential-kernel Laplace convolution law.**  For a measurable real source of at most
linear growth, the causal convolution with `exp(-b u)` has Laplace transform `(z+b)^(-1) L[φ](z)`
on the right half-plane. -/
theorem integral_Ioi_expVolterra_laplace
    {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : 0 < z.re) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : Measurable φ) (hbnd : ∀ h : ℝ, 0 < h → |φ h| ≤ C * (1 + h)) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * φ h : ℝ) : ℂ))
      = (z + (b : ℂ))⁻¹ * ∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ) := by
  have hw₁ : IntegrableOn (fun t : ℝ => Real.exp (-(z.re / 2 * t))) (Ioi (0 : ℝ)) volume :=
    integrableOn_Ioi_rexp_neg_mul (by linarith) 0
  have hw₂ : IntegrableOn
      (fun h : ℝ => |C| * ((1 + h) * Real.exp (-(z.re / 2 * h)))) (Ioi (0 : ℝ)) volume :=
    integrableOn_Ioi_linear_exp_majorant hz
  have hmeas : AEStronglyMeasurable (Function.uncurry (expVolterraIntegrand b z φ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (measurable_uncurry_expVolterraIntegrand b z hφ).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
      ‖Function.uncurry (expVolterraIntegrand b z φ) p‖ ≤
        Real.exp (-(z.re / 2 * p.1)) * (|C| * ((1 + p.2) * Real.exp (-(z.re / 2 * p.2)))) := by
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr ?_
    filter_upwards with p hp
    exact norm_expVolterraIntegrand_le hb hz hbnd hp.1 hp.2
  have hswap := GaloisForLFunctions.HTGeometry.integral_swap_of_dominated_prod
    hw₁ hw₂ hmeas hbound
  have hL : (∫ t in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), expVolterraIntegrand b z φ t h) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * φ h : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => integral_expVolterraIntegrand_snd hφ ht)
  have hR : (∫ h in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), expVolterraIntegrand b z φ t h) =
      ∫ h in Ioi (0 : ℝ), (z + (b : ℂ))⁻¹ *
        (Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun h hh => integral_expVolterraIntegrand_fst hb hz hh)
  rw [← hL, hswap, hR, MeasureTheory.integral_const_mul]

end GaloisForLFunctions.RHTower
