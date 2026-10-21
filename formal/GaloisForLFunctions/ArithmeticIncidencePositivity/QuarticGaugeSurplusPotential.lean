import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential

/-!
# The surplus potential of a quartic gauge

The closed form of `CubicGaugeSurplusPotential` extends to the quartic gauge
`h(y) = a₀ + a₁ y + a₂ y² + a₃ y³ + a₄ y⁴`: the quartic term is even, so it never meets the reflected
pole `1/(x + y)` and contributes the polynomial `a₄ (25x⁴/12 − r x³ − r³ x/3)`
(`integral_principalSurplus_quarticGauge`). On `(0, x)` the principal integrand is
`a₁ + a₂ y + a₃(x² + y²) + a₄(x² y + y³) − (a₁ x + a₃ x³)/(x + y)`, on `(x, r)` it is
`−a₂ x − a₃ x y − a₄(x³ + x y²) − (a₁ x + a₃ x³)/(x + y)`. With the remainder of the Lévy density as in
the cubic case (`mul_surplusPotential_quarticGauge_ge`):

    h(x) U_h(x) ≥ quarticSurplusMain − L · surplusRemainder.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The quartic gauge `h(y) = a₀ + a₁ y + a₂ y² + a₃ y³ + a₄ y⁴`. -/
def quarticGauge (a₀ a₁ a₂ a₃ a₄ y : ℝ) : ℝ := a₀ + a₁ * y + a₂ * y ^ 2 + a₃ * y ^ 3 + a₄ * y ^ 4

/-- The principal surplus of a quartic gauge: the cubic closed form plus
`a₄ (25x⁴/12 − r x³ − r³ x/3)`. -/
def quarticSurplusMain (a₁ a₂ a₃ a₄ r x : ℝ) : ℝ :=
  cubicSurplusMain a₁ a₂ a₃ r x + a₄ * (25 / 12 * x ^ 4 - r * x ^ 3 - r ^ 3 * x / 3)

theorem quarticGauge_sub (a₀ a₁ a₂ a₃ a₄ x y : ℝ) :
    quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y =
      (x - y) * (a₁ + a₂ * (x + y) + a₃ * (x ^ 2 + x * y + y ^ 2) +
        a₄ * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) := by
  unfold quarticGauge; ring

theorem continuous_quarticGauge (a₀ a₁ a₂ a₃ a₄ : ℝ) : Continuous (quarticGauge a₀ a₁ a₂ a₃ a₄) := by
  unfold quarticGauge; fun_prop

/-- **The principal surplus of a quartic gauge in closed form.** -/
theorem integral_principalSurplus_quarticGauge (a₀ a₁ a₂ a₃ a₄ : ℝ) {r x : ℝ} (hx : 0 < x)
    (hxr : x ≤ r) :
    IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) (Ioc 0 r) ∧
      (∫ y in Ioc 0 r, (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) =
        quarticSurplusMain a₁ a₂ a₃ a₄ r x := by
  set g := fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
    (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) with hg
  have hg1 : ∀ y ∈ Ioo 0 x, g y = (a₁ + a₃ * x ^ 2) + 2 * ((a₂ + a₄ * x ^ 2) / 2) * y +
      3 * (a₃ / 3) * y ^ 2 + 4 * (a₄ / 4) * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y) := by
    intro y hy
    have h1 : |x - y| = x - y := abs_of_pos (by linarith [hy.2])
    have h2 : x - y ≠ 0 := by linarith [hy.2]
    have h3 : x + y ≠ 0 := by linarith [hy.1]
    simp only [hg, quarticGauge, h1]
    field_simp
    ring
  have hg2 : ∀ y ∈ Ioo x r, g y = (-a₂ * x - a₄ * x ^ 3) + 2 * (-a₃ * x / 2) * y +
      3 * (-a₄ * x / 3) * y ^ 2 + 4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y) := by
    intro y hy
    have h1 : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith [hy.1])
    have h2 : y - x ≠ 0 := by linarith [hy.1]
    have h3 : x + y ≠ 0 := by linarith [hy.1]
    simp only [hg, quarticGauge, h1]
    field_simp
    ring
  have hc1 : ContinuousOn (fun y => (a₁ + a₃ * x ^ 2) + 2 * ((a₂ + a₄ * x ^ 2) / 2) * y +
      3 * (a₃ / 3) * y ^ 2 + 4 * (a₄ / 4) * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y)) (Icc 0 x) :=
    ContinuousOn.sub (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
      fun y hy => by linarith [hy.1])
  have hc2 : ContinuousOn (fun y => (-a₂ * x - a₄ * x ^ 3) + 2 * (-a₃ * x / 2) * y +
      3 * (-a₄ * x / 3) * y ^ 2 + 4 * 0 * y ^ 3 - (a₁ * x + a₃ * x ^ 3) / (x + y)) (Icc x r) :=
    ContinuousOn.sub (by fun_prop) (ContinuousOn.div continuousOn_const (by fun_prop)
      fun y hy => by linarith [hy.1])
  have hI1 : IntegrableOn g (Ioc 0 x) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hc1.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun y hy => (hg1 y hy).symm) measurableSet_Ioo
  have hI2 : IntegrableOn g (Ioc x r) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun y hy => (hg2 y hy).symm) measurableSet_Ioo
  have hd : Disjoint (Ioc (0 : ℝ) x) (Ioc x r) :=
    Set.disjoint_left.mpr fun y h1 h2 => by linarith [h1.2, h2.1]
  refine ⟨by rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr]; exact hI1.union hI2, ?_⟩
  rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union hd measurableSet_Ioc hI1 hI2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo (x := x),
    setIntegral_congr_fun measurableSet_Ioo hg1, setIntegral_congr_fun measurableSet_Ioo hg2,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hx.le, ← intervalIntegral.integral_of_le hxr,
    integral_quartic_sub_log (c₀ := 0) hx.le (by linarith),
    integral_quartic_sub_log (c₀ := 0) hxr (by linarith)]
  unfold quarticSurplusMain cubicSurplusMain
  rw [add_zero]
  ring

/-- **The surplus potential of a quartic gauge.** For `0 < x ≤ r ≤ 1/2` and a quartic gauge positive
at `x` whose divided differences are bounded by `L` on `[0, r]`,
`h(x) U_h(x) ≥ quarticSurplusMain a₁ a₂ a₃ a₄ r x − L · surplusRemainder r x`. -/
theorem mul_surplusPotential_quarticGauge_ge (a₀ a₁ a₂ a₃ a₄ : ℝ) {r x L : ℝ} (hx : 0 < x)
    (hxr : x ≤ r) (hr1 : r ≤ 1 / 2) (hhx : 0 < quarticGauge a₀ a₁ a₂ a₃ a₄ x)
    (hL : ∀ u v, 0 ≤ u → u ≤ r → 0 ≤ v → v ≤ r →
      |a₁ + a₂ * (u + v) + a₃ * (u ^ 2 + u * v + v ^ 2) +
        a₄ * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ L) :
    quarticSurplusMain a₁ a₂ a₃ a₄ r x - L * surplusRemainder r x ≤
      quarticGauge a₀ a₁ a₂ a₃ a₄ x * surplusPotential (quarticGauge a₀ a₁ a₂ a₃ a₄) r x := by
  have hlip : ∀ y, 0 ≤ y → y ≤ r →
      |quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y| ≤ L * |x - y| :=
    fun y hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hL x y hx.le hxr hy0 hyr) (abs_nonneg _)
  obtain ⟨hP, hPeq⟩ := integral_principalSurplus_quarticGauge a₀ a₁ a₂ a₃ a₄ hx hxr
  obtain ⟨hE, hEeq⟩ := integral_surplusRemainder hx hxr
  have hU : quarticGauge a₀ a₁ a₂ a₃ a₄ x * surplusPotential (quarticGauge a₀ a₁ a₂ a₃ a₄) r x =
      ∫ y in Ioc 0 r, surplusKernel x y *
        (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) := by
    unfold surplusPotential
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    have e : quarticGauge a₀ a₁ a₂ a₃ a₄ x *
        (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x) =
        quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y := by
      field_simp
    calc quarticGauge a₀ a₁ a₂ a₃ a₄ x * (surplusKernel x y *
          (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x)) =
        surplusKernel x y * (quarticGauge a₀ a₁ a₂ a₃ a₄ x *
          (1 - quarticGauge a₀ a₁ a₂ a₃ a₄ y / quarticGauge a₀ a₁ a₂ a₃ a₄ x)) := by ring
      _ = _ := by rw [e]
  have hmk : Measurable fun y => surplusKernel x y := by
    unfold surplusKernel
    exact (measurable_archLevyDensity.comp (by fun_prop)).sub
      (measurable_archLevyDensity.comp (by fun_prop))
  have hmh : Measurable fun y => quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y :=
    measurable_const.sub (continuous_quarticGauge a₀ a₁ a₂ a₃ a₄).measurable
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0 0 le_rfl (by linarith) le_rfl (by linarith))
  have hK : IntegrableOn (fun y => surplusKernel x y *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y)) (Ioc 0 r) := by
    refine Measure.integrableOn_of_bounded (M := 3 / 2 * L) (by simp)
      (hmk.mul hmh).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    by_cases hxy : x = y
    · rw [hxy, sub_self, mul_zero, abs_zero]; positivity
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hk0 := surplusKernel_nonneg hx hy.1 hxy
    have hk1 := (surplusKernel_le hx hy.1).trans (archLevyDensity_le_of_le_one hd
      (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]))
    rw [abs_mul, abs_of_nonneg hk0]
    calc surplusKernel x y * |quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y| ≤
          3 / 2 / |x - y| * (L * |x - y|) :=
          mul_le_mul hk1 (hlip y hy.1.le hy.2) (abs_nonneg _) (by positivity)
      _ = 3 / 2 * L := by field_simp
  have hpt : ∀ y ∈ Ioc 0 r, (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) -
      L * (((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|) ≤
        surplusKernel x y * (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) := by
    intro y hy
    by_cases hxy : x = y
    · rw [hxy, sub_self, sub_self, abs_zero]; simp
    set A := surplusKernel x y - (1 / (2 * |x - y|) - 1 / (2 * (x + y))) with hA
    set D := quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y with hD
    have hdiff : |A| ≤ (x + y) / 16 + (x + y) ^ 2 / 32 :=
      abs_surplusKernel_sub_principal_le hx hy.1 hxy
    have hl : |D| ≤ L * |x - y| := hlip y hy.1.le hy.2
    have hab : |A * D| = |A| * |D| := abs_mul A D
    have hlow := neg_abs_le (A * D)
    have hxy0 : 0 < x + y := by linarith [hy.1]
    have hprod : |A| * |D| ≤ ((x + y) / 16 + (x + y) ^ 2 / 32) * (L * |x - y|) :=
      mul_le_mul hdiff hl (abs_nonneg _) (by positivity)
    have e : surplusKernel x y * D = (1 / (2 * |x - y|) - 1 / (2 * (x + y))) * D + A * D := by
      rw [hA]; ring
    rw [e]
    nlinarith
  have hPE : IntegrableOn (fun y => (1 / (2 * |x - y|) - 1 / (2 * (x + y))) *
      (quarticGauge a₀ a₁ a₂ a₃ a₄ x - quarticGauge a₀ a₁ a₂ a₃ a₄ y) -
      L * (((x + y) / 16 + (x + y) ^ 2 / 32) * |x - y|)) (Ioc 0 r) := hP.sub (hE.const_mul L)
  have hmono := setIntegral_mono_on hPE hK measurableSet_Ioc hpt
  rw [MeasureTheory.integral_sub hP (hE.const_mul L), MeasureTheory.integral_const_mul, hPeq,
    hEeq] at hmono
  rw [hU]
  exact hmono

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
