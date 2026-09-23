import GaloisForLFunctions.HTGeometry.HillChartSecond
import GaloisForLFunctions.HTGeometry.HillFieldEquation

/-!
# The wave equation of a time-dependent speed, on the chart

The field equation of the evolution says that the second time derivative of the synthesis is the
speed squared times the spatial Laplacian, minus the mass term. On the chart the spatial directions
are rescaled by `2π`, and that rescaling is exactly the one the equation carries, so the equation
becomes the literal coordinate identity

`∂₀²u = c(t)² ∑ᵢ ∂ᵢ²u - m²u`.

Written with the wave operator of a speed, `□u + (-m²)u = 0`: the field is a clock probe for the
constant potential `-m²`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section TwoSidedEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- **The field equation at every time.** -/
theorem hillSynthesisSecond_eq_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) (volume : Measure E))
    (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    hillSynthesisSecond m c G₀ (kgChar x) (volume : Measure E) t =
      ((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ *
            hillDensity m c G₀ t ξ)) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * hillEvolutionField m c G₀ t x := by
  have hmeas := aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t (volume : Measure E)
  have hdint : Integrable (hillDensity m c G₀ t) (volume : Measure E) :=
    integrable_hillDensity_all (C := C) hm hc hcd hcpos hK hC hG hint t
  have hw2 := integrable_kgFreq_sq_mul_hillDensity_all (C := C) hm hc hcd hcpos hK hC hG h2 t
  have hlap := sum_integral_dirSq hmeas hw2 b x
  have hintLap : Integrable (fun ξ : E =>
      ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ)
      (volume : Measure E) := by
    have hmeasF : AEStronglyMeasurable (fun ξ : E =>
        ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ)
        (volume : Measure E) :=
      (((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_norm.pow 2))).mul
          (continuous_kgChar' x)).aestronglyMeasurable).mul hmeas
    refine Integrable.mono' (hw2.const_mul (4 * Real.pi ^ (2 : ℕ))) hmeasF ?_
    filter_upwards with ξ
    have hchar : ‖kgChar x ξ‖ = 1 := norm_kgChar x ξ
    have hnormle : ‖ξ‖ ^ (2 : ℕ) ≤ kgFreq ξ ^ (2 : ℕ) := by
      rw [kgFreq_sq]
      linarith
    have hDnn : (0 : ℝ) ≤ ‖hillDensity m c G₀ t ξ‖ := norm_nonneg _
    have hpi : (0 : ℝ) ≤ 4 * Real.pi ^ (2 : ℕ) := by positivity
    calc ‖((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ‖
        = (4 * Real.pi ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖hillDensity m c G₀ t ξ‖ := by
          rw [norm_mul, norm_mul, hchar, Complex.norm_real, Real.norm_eq_abs, mul_one]
          rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])]
          ring
      _ ≤ (4 * Real.pi ^ (2 : ℕ) * kgFreq ξ ^ (2 : ℕ)) * ‖hillDensity m c G₀ t ξ‖ := by
          have := mul_le_mul_of_nonneg_left hnormle hpi
          exact mul_le_mul_of_nonneg_right this hDnn
      _ = 4 * Real.pi ^ (2 : ℕ) * (kgFreq ξ ^ (2 : ℕ) * ‖hillDensity m c G₀ t ξ‖) := by ring
  have hintMass : Integrable (fun ξ : E => kgChar x ξ * hillDensity m c G₀ t ξ)
      (volume : Measure E) := by
    refine Integrable.mono' hdint.norm
      (((continuous_kgChar' x).aestronglyMeasurable).mul hmeas) ?_
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul]
  rw [hillSynthesisSecond, hillEvolutionField, kgSynthesis, hlap]
  have hsplit : ∀ ξ : E, kgChar x ξ * hillDensitySecond m c G₀ t ξ
      = ((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * (kgChar x ξ * hillDensity m c G₀ t ξ) := by
    intro ξ
    rw [hillDensitySecond_symbol hm t ξ]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_sub ((hintLap.const_mul _)) ((hintMass.const_mul _)), integral_const_mul,
    integral_const_mul]

/-! ## Rescaling a direction -/

/-- Scaling a direction scales the derived density. -/
theorem kgSynthesis_dirSq_smul (a : ℝ) (v : E) (f : E → ℂ) (x : E) :
    kgSynthesis (kgDirDensity (a • v) (kgDirDensity (a • v) f)) x
      = ((a ^ (2 : ℕ) : ℝ) : ℂ) *
        ∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ := by
  rw [kgSynthesis, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgChar x ξ * kgDirDensity (a • v) (kgDirDensity (a • v) f) ξ
    = ((a ^ (2 : ℕ) : ℝ) : ℂ) *
      ((2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ)
  rw [kgDirDensity, kgDirDensity, real_inner_smul_right]
  push_cast
  ring

end TwoSidedEquation

section ChartEquation

variable {d : ℕ} {m K C cmin : ℝ} {c dc : ℝ → ℝ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

/-- **The field equation in the chart directions.** -/
theorem hillSynthesisSecond_eq_chart (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume))
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    hillSynthesisSecond m c G (kgChar x) (volume) t =
      ((c t ^ (2 : ℕ) : ℝ) : ℂ) * (∑ i : Fin d,
          kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
            (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G t))) x) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * hillEvolutionField m c G t x := by
  rw [hillSynthesisSecond_eq_all (C := C) hm hc hcd hcpos hK hC hG hint h2
    (EuclideanSpace.basisFun (Fin d) ℝ) t x]
  have hterm : ∀ i : Fin d,
      kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G t))) x
        = ((((2 * Real.pi)⁻¹ : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) *
          ∫ ξ, (2 * Real.pi * Complex.I *
            ((⟪ξ, EuclideanSpace.basisFun (Fin d) ℝ i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ *
            hillDensity m c G t ξ := by
    intro i
    rw [kgDir_eq_basisFun]
    exact kgSynthesis_dirSq_smul ((2 * Real.pi)⁻¹) _ _ x
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, ← Finset.mul_sum]
  congr 1
  push_cast
  ring

/-! ## The coordinate second derivatives -/

theorem coordPartial_coordPartial_hillChartField_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) :
    coordPartial 0 (coordPartial 0 (hillChartField m c G)) y = hillChartTimeSecond m c G 0 y := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hwA := integrable_massWeight (c := c) hm (hcpos 0) hG h1
  have hcp : coordPartial 0 (hillChartField m c G) = hillChartTimePartial m c G := by
    funext z
    rw [coordPartial_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h0 hwA h1 0 z,
      hillChartPartial_zero]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (hillChartTimePartial m c G)
    (hillChartTimeSecond m c G) Set.univ
    (isC1OnPi_hillChartTimePartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2) y
    (Set.mem_univ y)).fderiv, piToCLM_single]

theorem coordPartial_coordPartial_hillChartField_succ (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    coordPartial i.succ (coordPartial i.succ (hillChartField m c G)) y
      = hillChartSpaceSecond m c G i i.succ y := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have hwA := integrable_massWeight (c := c) hm (hcpos 0) hG h1
  have hcp : coordPartial i.succ (hillChartField m c G) = hillChartSpacePartial m c G i := by
    funext z
    rw [coordPartial_hillChartField (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h0 hwA h1
      i.succ z, hillChartPartial_succ]
  rw [hcp, coordPartial, (hasFDerivAt_of_isC1OnPi (d + 1) (hillChartSpacePartial m c G i)
    (hillChartSpaceSecond m c G i) Set.univ
    (isC1OnPi_hillChartSpacePartial (C := C) hm hc hcd hcpos hK hC hcmin hclow hG h2 i) y
    (Set.mem_univ y)).fderiv, piToCLM_single]

/-! ## The wave equation on the chart -/

/-- **The chart field of the evolution satisfies the wave equation of a time-dependent speed.** -/
theorem hillChartField_wave_identity (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G)
    (h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ ^ (2 : ℕ) * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) :
    coordPartial 0 (coordPartial 0 (hillChartField m c G)) y
      = c (y 0) ^ (2 : ℕ) *
          (∑ i : Fin d, coordPartial i.succ (coordPartial i.succ (hillChartField m c G)) y) -
        m ^ (2 : ℕ) * hillChartField m c G y := by
  have h1 := integrable_kgFreq_mul_of_sq hG h2
  have h0 := integrable_of_kgFreq_mul hG h1
  have heq := hillSynthesisSecond_eq_chart (C := C) hm hc hcd hcpos hK hC hG h0 h2 (y 0)
    (kgSpatial d y)
  have hzero := coordPartial_coordPartial_hillChartField_zero (C := C) hm hc hcd hcpos hK hC
    hcmin hclow hG h2 y
  have hsucc : ∀ i : Fin d,
      coordPartial i.succ (coordPartial i.succ (hillChartField m c G)) y
        = (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
            (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G (y 0))))
              (kgSpatial d y)).re := by
    intro i
    rw [coordPartial_coordPartial_hillChartField_succ (C := C) hm hc hcd hcpos hK hC hcmin hclow
      hG h2 y i, hillChartSpaceSecond_succ]
  rw [hzero, hillChartTimeSecond_zero]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsucc i]
  show (hillSynthesisSecond m c G (kgChar (kgSpatial d y)) (volume) (y 0)).re = _
  rw [heq, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_sum]
  rfl

end ChartEquation

end GaloisForLFunctions.HTGeometry
