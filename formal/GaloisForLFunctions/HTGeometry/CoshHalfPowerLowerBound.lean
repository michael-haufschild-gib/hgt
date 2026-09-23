import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An elementary lower bound for the half-power hyperbolic integral

On `[0,∞)` the envelope `cosh t ≤ (e^t + 1)/2` replaces the half-power hyperbolic integrand by an
elementary one whose primitive is `-2 arsinh (e^{-t/2})`:

```text
∫_0^∞ (e^t + 1)^(-1/2) dt = 2 arsinh 1 ,
∫_0^∞ (cosh t)^(-1/2) dt ≥ 2 √2 arsinh 1 .
```

Comparing with the closed Beta value of the same integral bounds the Gamma quotient from below,

```text
4 √2 arsinh 1 ≤ √π Γ(1/4)/Γ(3/4) ,
```

and `arsinh 1 = log (1 + √2) > 7/8` because `e^(7 : ℕ) < 577 + 408 √2 = (1 + √2)^(8 : ℕ)`.
-/

open MeasureTheory Filter Topology

namespace HTGeometry

noncomputable section

/-! ### The elementary primitive -/

/-- The negative half power is the reciprocal square root. -/
theorem rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : x ^ (-(1 / 2) : ℝ) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `√(e^(-t)) = e^(-t/2)`. -/
theorem sqrt_exp_neg (t : ℝ) : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
  have hsq : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- `√(e^t) = e^(t/2)`. -/
theorem sqrt_exp (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  have hsq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- Primitive of `(e^t + 1)^(-1/2)`. -/
def expShiftPrimitive (t : ℝ) : ℝ := -2 * Real.arsinh (Real.exp (-t / 2))

theorem continuous_expShiftPrimitive : Continuous expShiftPrimitive := by
  unfold expShiftPrimitive
  exact continuous_const.mul
    (Real.continuous_arsinh.comp (Real.continuous_exp.comp (by continuity)))

/-- `d/dt [-2 arsinh (e^(-t/2))] = (e^t + 1)^(-1/2)`. -/
theorem hasDerivAt_expShiftPrimitive (t : ℝ) :
    HasDerivAt expShiftPrimitive (Real.sqrt (Real.exp t + 1))⁻¹ t := by
  unfold expShiftPrimitive
  have hlin : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2 : ℝ) t :=
    (hasDerivAt_id t).neg.div_const 2
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
      (Real.exp (-t / 2) * (-1 / 2)) t := hlin.exp
  have hcomp := (Real.hasDerivAt_arsinh (Real.exp (-t / 2))).comp t hexp
  have hfin := hcomp.const_mul (-2 : ℝ)
  have hval : -2 * ((Real.sqrt (1 + Real.exp (-t / 2) ^ 2))⁻¹ *
      (Real.exp (-t / 2) * (-1 / 2))) = (Real.sqrt (Real.exp t + 1))⁻¹ := by
    have hsq : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have h1 : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hfac : (1 : ℝ) + Real.exp (-t) = (Real.exp t + 1) * Real.exp (-t) := by
      rw [add_mul, one_mul, h1]
    have hEpos : (0 : ℝ) < Real.exp (-t / 2) := Real.exp_pos _
    have hSpos : (0 : ℝ) < Real.sqrt (Real.exp t + 1) := by positivity
    rw [hsq, hfac, Real.sqrt_mul (by positivity), sqrt_exp_neg]
    field_simp
  rw [← hval]
  exact hfin

/-! ### The elementary integral -/

/-- `(e^t + 1)^(-1/2)` is integrable on the positive ray. -/
theorem integrableOn_invSqrtExpAddOne :
    IntegrableOn (fun t : ℝ => (Real.sqrt (Real.exp t + 1))⁻¹) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  refine hg.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable (Continuous.inv₀ ?_ ?_)
    · exact Real.continuous_sqrt.comp (Real.continuous_exp.add continuous_const)
    · intro x
      positivity
  · filter_upwards with t
    have hE : Real.sqrt (Real.exp t) ≤ Real.sqrt (Real.exp t + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hst : Real.sqrt (Real.exp t) = Real.exp (t / 2) := sqrt_exp t
    have hpos : (0 : ℝ) < Real.sqrt (Real.exp t + 1) := by positivity
    have hb : Real.exp (-(1 / 2 : ℝ) * t) = (Real.exp (t / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), hb]
    exact inv_anti₀ (Real.exp_pos _) (by rw [← hst]; exact hE)

/-- **The elementary half-power integral.** `∫_0^∞ (e^t + 1)^(-1/2) dt = 2 arsinh 1`. -/
theorem integral_Ioi_invSqrtExpAddOne :
    ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt (Real.exp t + 1))⁻¹ = 2 * Real.arsinh 1 := by
  have hcont : ContinuousWithinAt expShiftPrimitive (Set.Ici 0) 0 :=
    continuous_expShiftPrimitive.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt expShiftPrimitive ((Real.sqrt (Real.exp x + 1))⁻¹) x :=
    fun x _ => hasDerivAt_expShiftPrimitive x
  have htend : Tendsto expShiftPrimitive atTop (nhds 0) := by
    unfold expShiftPrimitive
    have h2 : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (nhds 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
      refine this.congr fun t => ?_
      simp [Function.comp, neg_div]
    have harc := (Real.continuous_arsinh.tendsto 0).comp h1
    rw [Real.arsinh_zero] at harc
    have := harc.const_mul (-2 : ℝ)
    simpa [Function.comp] using this
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    integrableOn_invSqrtExpAddOne htend
  rw [hmain]
  simp only [expShiftPrimitive, neg_zero, zero_div, Real.exp_zero]
  ring

/-! ### The comparison with the hyperbolic integrand -/

/-- On the positive ray, `√2 (e^t + 1)^(-1/2) ≤ (cosh t)^(-1/2)`. -/
theorem sqrt_two_mul_inv_sqrt_le_cosh_rpow {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt 2 * (Real.sqrt (Real.exp t + 1))⁻¹ ≤ (Real.cosh t) ^ (-(1 / 2) : ℝ) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hexp : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h2c : 2 * Real.cosh t ≤ Real.exp t + 1 := by
    rw [Real.cosh_eq]
    linarith
  have hsq : Real.sqrt 2 * Real.sqrt (Real.cosh t) ≤ Real.sqrt (Real.exp t + 1) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h2c
  have hA : (0 : ℝ) < Real.sqrt (Real.exp t + 1) := by positivity
  have hB : (0 : ℝ) < Real.sqrt (Real.cosh t) := Real.sqrt_pos.mpr hc
  rw [rpow_neg_half hc.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ hA hB]
  linarith

/-- **The Gamma quotient bound.** `4 √2 arsinh 1 ≤ √π Γ(1/4)/Γ(3/4)`. -/
theorem four_sqrt_two_mul_arsinh_one_le_gammaQuotient :
    4 * Real.sqrt 2 * Real.arsinh 1
      ≤ Real.sqrt Real.pi * Real.Gamma (1 / 4) / Real.Gamma (3 / 4) := by
  have hint1 : IntegrableOn (fun t : ℝ => Real.sqrt 2 * (Real.sqrt (Real.exp t + 1))⁻¹)
      (Set.Ioi 0) := integrableOn_invSqrtExpAddOne.const_mul _
  have hint2 : IntegrableOn (fun t : ℝ => (Real.cosh t) ^ (-(1 / 2) : ℝ)) (Set.Ioi 0) :=
    (integrable_cosh_rpow_neg (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hmono : (∫ t in Set.Ioi (0 : ℝ), Real.sqrt 2 * (Real.sqrt (Real.exp t + 1))⁻¹)
      ≤ ∫ t in Set.Ioi (0 : ℝ), (Real.cosh t) ^ (-(1 / 2) : ℝ) :=
    MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioi
      fun t ht => sqrt_two_mul_inv_sqrt_le_cosh_rpow (le_of_lt ht)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_invSqrtExpAddOne] at hmono
  have hval := integral_cosh_rpow_neg_Ioi_eq (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num at hval
  rw [hval] at hmono
  have hG : (0 : ℝ) < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  rw [le_div_iff₀ hG]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.Gamma (3 / 4))] at hmono
  linarith

/-! ### The numerical lower bound for `arsinh 1` -/

/-- `arsinh 1 = log (1 + √2) > 7/8`. -/
theorem seven_div_eight_lt_arsinh_one : (7 : ℝ) / 8 < Real.arsinh 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (1.414 : ℝ) < Real.sqrt 2 := by
    nlinarith [hs, Real.sqrt_nonneg 2]
  have hexp : Real.exp (Real.arsinh 1) = 1 + Real.sqrt 2 := by
    rw [Real.exp_arsinh]
    norm_num
  have he7 : Real.exp 7 < 1097 := by
    have h1 : Real.exp 7 = Real.exp 1 ^ (7 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h1]
    calc Real.exp 1 ^ (7 : ℕ) ≤ (2.7182818286 : ℝ) ^ (7 : ℕ) := by
          gcongr
          exact le_of_lt Real.exp_one_lt_d9
      _ < 1097 := by norm_num
  have e2 : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by linear_combination hs
  have e4 : (1 + Real.sqrt 2) ^ 4 = 17 + 12 * Real.sqrt 2 := by
    have h : (1 + Real.sqrt 2) ^ 4 = ((1 + Real.sqrt 2) ^ 2) ^ 2 := by ring
    rw [h, e2]
    linear_combination 4 * hs
  have e8 : (1 + Real.sqrt 2) ^ (8 : ℕ) = 577 + 408 * Real.sqrt 2 := by
    have h : (1 + Real.sqrt 2) ^ (8 : ℕ) = ((1 + Real.sqrt 2) ^ 4) ^ 2 := by ring
    rw [h, e4]
    linear_combination 144 * hs
  have hlt : Real.exp (7 / 8) ^ (8 : ℕ) < (1 + Real.sqrt 2) ^ (8 : ℕ) := by
    have h8 : Real.exp (7 / 8) ^ (8 : ℕ) = Real.exp 7 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h8, e8]
    linarith
  have hbase : Real.exp (7 / 8) < 1 + Real.sqrt 2 :=
    lt_of_pow_lt_pow_left₀ 8 (by positivity) hlt
  rw [← hexp] at hbase
  exact Real.exp_lt_exp.mp hbase

end

end HTGeometry
