import GaloisForLFunctions.HTGeometry.HillChartField
import GaloisForLFunctions.HTGeometry.HillSynthesisTwoSided
import GaloisForLFunctions.HTGeometry.WienerSynthesisMixed

/-!
# The coordinate derivatives of the chart field

Along the time axis the chart field moves only its time argument, and along a spatial axis only its
point, by the rescaled direction. So the derivative along each coordinate axis is one of the
derivatives already proved — a time derivative in the first case, a spatial directional derivative in
the second, and each is the real part of a synthesis: of the velocity density for the time axis, of
the derived density for a spatial axis.

Both are stated at an arbitrary event, which is why the time derivative had to be freed of its
interval restriction first.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section Partials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- Weighted integrability of the density at every time. -/
theorem integrable_weight_mul_hillDensity_all {w : E → ℝ} (hw : ∀ ξ, 0 ≤ w ξ)
    {t : ℝ}
    (hmw : AEStronglyMeasurable (fun ξ : E => w ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E))
    (hm : 0 < m) (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r)
    (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (hint : Integrable (fun ξ : E => w ξ * ‖G₀ ξ‖) (volume : Measure E)) :
    Integrable (fun ξ : E => w ξ * ‖hillDensity m c G₀ t ξ‖) (volume : Measure E) := by
  refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * |t|))) hmw ?_
  filter_upwards with ξ
  have hbase := norm_hillDensity_le_abs (G₀ := G₀) hm hc hcd hcpos hK hC t ξ
  have hwξ := hw ξ
  have hnorm : ‖w ξ * ‖hillDensity m c G₀ t ξ‖‖ = w ξ * ‖hillDensity m c G₀ t ξ‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwξ (norm_nonneg _))]
  rw [hnorm]
  calc w ξ * ‖hillDensity m c G₀ t ξ‖
      ≤ w ξ * ((max 1 (c 0 / c t) * Real.exp (K * |t|)) * ‖G₀ ξ‖) :=
        mul_le_mul_of_nonneg_left hbase hwξ
    _ = (max 1 (c 0 / c t) * Real.exp (K * |t|)) * (w ξ * ‖G₀ ξ‖) := by ring

/-- **The spatial derivative of the field, at every time**, as the synthesis of the derived
density. -/
theorem hasDerivAt_hillEvolutionField_dir_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E))
    (t : ℝ) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => hillEvolutionField m c G₀ t (x + s • v))
      (kgSynthesis (kgDirDensity v (hillDensity m c G₀ t)) (x + r • v)) r := by
  have hmeas := aestronglyMeasurable_hillDensity_all (C := C) hm hc hC hG t (volume : Measure E)
  have hdint : Integrable (hillDensity m c G₀ t) (volume : Measure E) :=
    integrable_hillDensity_all (C := C) hm hc hcd hcpos hK hC hG hint t
  have hmw : AEStronglyMeasurable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    (continuous_kgFreq.aestronglyMeasurable).mul hmeas.norm
  have hw1 : Integrable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    integrable_weight_mul_hillDensity_all (fun ξ => le_of_lt (kgFreq_pos ξ)) hmw hm hc hcd hcpos
      hK hC h1
  exact hasDerivAt_kgSynthesis_dir_synthesis hmeas hdint hw1 x v r

/-- **The real field has spatial directional derivatives at every time.** -/
theorem hasDerivAt_hillRealField_dir_all (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E))
    (t : ℝ) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => hillRealField m c G₀ t (x + s • v))
      ((kgSynthesis (kgDirDensity v (hillDensity m c G₀ t)) (x + r • v)).re) r :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_hillEvolutionField_dir_all (C := C) hm hc hcd hcpos hK hC hG hint h1 t x v r)

/-! ## The chart directions -/

section Chart

variable {d : ℕ} {G : EuclideanSpace ℝ (Fin d) → ℂ}

/-- Moving the time coordinate moves only the time argument. -/
theorem hillChartField_update_zero (m : ℝ) (c : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) (r : ℝ) :
    hillChartField m c G (Function.update y 0 r) = hillRealField m c G r (kgSpatial d y) := by
  rw [hillChartField, kgSpatial_update_zero, Function.update_self]

/-- Moving a spatial coordinate moves the point along the rescaled direction. -/
theorem hillChartField_update_succ (m : ℝ) (c : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) (i : Fin d) (r : ℝ) :
    hillChartField m c G (Function.update y i.succ r)
      = hillRealField m c G (y 0)
        (kgSpatial d y + (r - y i.succ) • ((2 * Real.pi)⁻¹ • kgDir d i)) := by
  rw [hillChartField, kgSpatial_update_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]

/-- The time partial of the chart field. -/
noncomputable def hillChartTimePartial (m : ℝ) (c : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (y : Fin (d + 1) → ℝ) : ℝ :=
  (hillSynthesisDeriv m c G (kgChar (kgSpatial d y)) (volume) (y 0)).re

/-- The `i`-th spatial partial of the chart field. -/
noncomputable def hillChartSpacePartial (m : ℝ) (c : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (i : Fin d) (y : Fin (d + 1) → ℝ) : ℝ :=
  (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDensity m c G (y 0)))
    (kgSpatial d y)).re

/-- The partial derivatives of the chart field, indexed by the chart coordinates. -/
noncomputable def hillChartPartial (m : ℝ) (c : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (j : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (hillChartTimePartial m c G) (fun i => hillChartSpacePartial m c G i) j

theorem hillChartPartial_zero (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ) :
    hillChartPartial m c G 0 = hillChartTimePartial m c G := rfl

theorem hillChartPartial_succ (m : ℝ) (c : ℝ → ℝ) (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (i : Fin d) : hillChartPartial m c G i.succ = hillChartSpacePartial m c G i := by
  rw [hillChartPartial, Fin.cases_succ]

/-- **The derivative of the chart field along the time axis.** -/
theorem hasDerivAt_hillChartField_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => hillChartField m c G (Function.update y 0 r))
      (hillChartTimePartial m c G y) (y 0) := by
  have hfun : (fun r : ℝ => hillChartField m c G (Function.update y 0 r))
      = fun r : ℝ => hillRealField m c G r (kgSpatial d y) :=
    funext fun r => hillChartField_update_zero m c G y r
  rw [hfun, hillChartTimePartial]
  exact hasDerivAt_hillRealField_time_all (C := C) hm hc hcd hcpos hK hC hG hint hweight
    (kgSpatial d y) (y 0)

/-- **The derivative of the chart field along a spatial axis.** -/
theorem hasDerivAt_hillChartField_succ (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => hillChartField m c G (Function.update y i.succ r))
      (hillChartSpacePartial m c G i y) (y i.succ) := by
  have hfun : (fun r : ℝ => hillChartField m c G (Function.update y i.succ r))
      = fun r : ℝ => hillRealField m c G (y 0)
        (kgSpatial d y + (r - y i.succ) • ((2 * Real.pi)⁻¹ • kgDir d i)) :=
    funext fun r => hillChartField_update_succ m c G y i r
  have hbase : HasDerivAt (fun s : ℝ => hillRealField m c G (y 0)
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i)))
      (hillChartSpacePartial m c G i y) 0 := by
    have h := hasDerivAt_hillRealField_dir_all (C := C) hm hc hcd hcpos hK hC hG hint h1
      (y 0) (kgSpatial d y) ((2 * Real.pi)⁻¹ • kgDir d i) 0
    have hzero : kgSpatial d y + (0 : ℝ) • ((2 * Real.pi)⁻¹ • kgDir d i) = kgSpatial d y := by
      rw [zero_smul, add_zero]
    rw [hzero] at h
    rw [hillChartSpacePartial]
    exact h
  have hbase' : HasDerivAt (fun s : ℝ => hillRealField m c G (y 0)
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i)))
      (hillChartSpacePartial m c G i y) (y i.succ - y i.succ) := by
    rw [sub_self]
    exact hbase
  have hcomp := HasDerivAt.comp_sub_const (f := fun s : ℝ => hillRealField m c G (y 0)
    (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))) (y i.succ) (y i.succ) hbase'
  rw [hfun]
  exact hcomp

/-- **The chart field has all coordinate derivatives.** -/
theorem hasDerivAt_hillChartField_update (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G)
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖G ξ‖) (volume))
    (hweight : Integrable
      (fun ξ : EuclideanSpace ℝ (Fin d) => (m + c 0 * ‖ξ‖) * ‖G ξ‖) (volume))
    (h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => kgFreq ξ * ‖G ξ‖) (volume))
    (y : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    HasDerivAt (fun r : ℝ => hillChartField m c G (Function.update y j r))
      (hillChartPartial m c G j y) (y j) := by
  refine Fin.cases ?_ ?_ j
  · rw [hillChartPartial_zero]
    exact hasDerivAt_hillChartField_zero (C := C) hm hc hcd hcpos hK hC hG hint hweight y
  · intro i
    rw [hillChartPartial_succ]
    exact hasDerivAt_hillChartField_succ (C := C) hm hc hcd hcpos hK hC hG hint h1 y i

end Chart

end Partials

end GaloisForLFunctions.HTGeometry
