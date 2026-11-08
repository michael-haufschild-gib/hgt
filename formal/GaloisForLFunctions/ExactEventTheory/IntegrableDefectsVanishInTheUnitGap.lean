import GaloisForLFunctions.ExactEventTheory.TentRecurrenceOfIntegrableDefects

/-!
# Atomic recurrence removes the boundary defect from the unit gap

Small tents inside `(0,1)` contain no generalized integer. The outer boundary error
tends to zero with its width, so the recurrence threshold forces the inner error to
vanish. Normalized tent averages recover the continuous boundary value at their centre.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

theorem measureSeries_conj (ν : Measure ℝ) (z : ℂ) :
    measureSeries ν (starRingEnd ℂ z) = starRingEnd ℂ (measureSeries ν z) := by
  unfold measureSeries
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by simp

theorem measureDual_conj (ν : Measure ℝ) (z : ℂ) :
    measureDual ν (starRingEnd ℂ z) = starRingEnd ℂ (measureDual ν z) := by
  unfold measureDual
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    simp only [← Complex.exp_conj, map_neg, map_mul, map_ofNat, Complex.conj_ofReal]

/-- Reality of the atomic measure and pole forces conjugation symmetry of the Laplace defect. -/
theorem defectLaplace_conj_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {z : ℂ} (hz : 0 < z.re) :
    defectLaplace g (starRingEnd ℂ z) = starRingEnd ℂ (defectLaplace g z) := by
  have hf := measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ
    (show 0 < (starRingEnd ℂ z).re by simpa using hz)
  rw [measureSeries_conj, measureDual_conj] at hf
  have ho := congrArg (starRingEnd ℂ) (measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ hz)
  simp at ho
  linear_combination ho - hf

theorem defectLaplace_re_neg_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    (defectLaplace g ((ε : ℂ) + ((-y : ℝ) : ℂ) * I)).re =
      (defectLaplace g ((ε : ℂ) + (y : ℂ) * I)).re := by
  have he : (ε : ℂ) + ((-y : ℝ) : ℂ) * I = starRingEnd ℂ ((ε : ℂ) + (y : ℂ) * I) := by simp
  rw [he, defectLaplace_conj_of_theta_defect hsupp hmom hgm hgb hθ (by simpa using hε)]
  simp

/-- The real right-hand boundary defect is even. -/
theorem defectBoundary_re_even_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    (y : ℝ) : (defectBoundary g (-y)).re = (defectBoundary g y).re := by
  by_cases hy : y = 0
  · simp [hy]
  have hn := (Complex.continuous_re.tendsto _).comp
    (tendsto_defectLaplace_boundary hgi (neg_ne_zero.mpr hy))
  have hp := (Complex.continuous_re.tendsto _).comp (tendsto_defectLaplace_boundary hgi hy)
  apply tendsto_nhds_unique hn
  apply hp.congr'
  exact eventually_nhdsWithin_of_forall fun ε hε =>
    (defectLaplace_re_neg_of_theta_defect hsupp hmom hgm hgb hθ hε y).symm

/-- The boundary average against a tent of total mass one. -/
def normalizedTentBoundary (g : ℝ → ℂ) (h y : ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, (1 - |s|) * (defectBoundary g (y + h * s)).re

theorem tentBoundaryError_eq_normalized (g : ℝ → ℂ) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    tentBoundaryError g h (y / h) = h * normalizedTentBoundary g h y := by
  have he (s : ℝ) : h * (y / h + s) = y + h * s := by field_simp
  simp only [tentBoundaryError, normalizedTentBoundary, he, mul_assoc,
    intervalIntegral.integral_const_mul]

/-- Shrinking positive-width tents recover every positive boundary value. -/
theorem tendsto_normalizedTentBoundary {g : ℝ → ℂ} (hg : Integrable g)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun h : ℝ => normalizedTentBoundary g h y) (𝓝[>] 0)
      (𝓝 (defectBoundary g y).re) := by
  let C : ℝ := 3 / (2 * Real.pi) * ∫ t, ‖g t‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (y / 2) := Ioo_mem_nhdsGT (by positivity)
  have hpos {h s : ℝ} (hh : h ∈ Ioo 0 (y / 2)) (hs : s ∈ uIoc (-1 : ℝ) 1) :
      y / 2 ≤ y + h * s := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hb := mul_le_mul_of_nonneg_left hs.1.le hh.1.le
    linarith only [hb, hh.2]
  have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ᵐ s : ℝ,
      s ∈ uIoc (-1 : ℝ) 1 →
        ‖(1 - |s|) * (defectBoundary g (y + h * s)).re‖ ≤ C * (y / 2) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [hev] with h hh
    apply Eventually.of_forall
    intro s hs
    have hp := hpos hh hs
    have hs1 : |s| ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
      exact abs_le.mpr ⟨hs.1.le, hs.2⟩
    have hj : ‖defectBoundary g (y + h * s)‖ ≤ C * (y / 2) ^ (-(1 / 2 : ℝ)) := by
      have hb := norm_defectBoundary_le hg (y + h * s)
      rw [abs_of_pos (by linarith only [hp, hy])] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hp (by norm_num)) hC)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1)]
    calc (1 - |s|) * |(defectBoundary g (y + h * s)).re| ≤
        1 * ‖defectBoundary g (y + h * s)‖ :=
          mul_le_mul (by linarith only [abs_nonneg s]) (Complex.abs_re_le_norm _)
            (abs_nonneg _) zero_le_one
      _ ≤ _ := by simpa only [one_mul] using hj
  have hlim : ∀ᵐ s : ℝ, s ∈ uIoc (-1 : ℝ) 1 →
      Tendsto (fun h : ℝ => (1 - |s|) * (defectBoundary g (y + h * s)).re)
        (𝓝[>] 0) (𝓝 ((1 - |s|) * (defectBoundary g y).re)) := by
    apply Eventually.of_forall
    intro s hs
    have ht : Tendsto (fun h : ℝ => y + h * s) (𝓝[>] 0) (𝓝[{x : ℝ | x ≠ 0}] y) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, hev.mono fun h hh => ?_⟩
      · simpa using ((by fun_prop : Continuous fun h : ℝ => y + h * s).tendsto 0
          ).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      · exact (lt_of_lt_of_le (by positivity : 0 < y / 2) (hpos hh hs)).ne'
    exact ((Complex.continuous_re.tendsto _).comp
      (((continuousOn_defectBoundary hg) y hy.ne').tendsto.comp ht)).const_mul (1 - |s|)
  have hl := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun h s : ℝ => (1 - |s|) * (defectBoundary g (y + h * s)).re)
    (f := fun s : ℝ => (1 - |s|) * (defectBoundary g y).re)
    (fun _ : ℝ => C * (y / 2) ^ (-(1 / 2 : ℝ)))
    (hev.mono fun h _ => (show Measurable (fun s : ℝ =>
      (1 - |s|) * (defectBoundary g (y + h * s)).re) from by
        exact (show Measurable (fun s : ℝ => 1 - |s|) from by fun_prop).mul
          (Complex.continuous_re.measurable.comp
            ((measurable_defectBoundary hg).comp (by fun_prop)))).aestronglyMeasurable)
    hbound (show IntervalIntegrable (fun _ : ℝ => C * (y / 2) ^ (-(1 / 2 : ℝ))) volume (-1) 1
      from intervalIntegrable_const) hlim
  simpa only [normalizedTentBoundary, intervalIntegral.integral_mul_const,
    fejer_triangle_integral_one, one_mul] using hl

theorem tendsto_tentBoundaryError_width_zero {g : ℝ → ℂ} (hg : Integrable g)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun h : ℝ => tentBoundaryError g h (y / h)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).mul
    (tendsto_normalizedTentBoundary hg hy)
  simp only [zero_mul] at ht
  apply ht.congr'
  exact eventually_nhdsWithin_of_forall fun h hh => (tentBoundaryError_eq_normalized g hh y).symm

/-- Atomic recurrence forces the real boundary defect to vanish throughout the positive unit gap. -/
theorem beurling_defectBoundary_re_eq_zero_on_unit_gap
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : (defectBoundary g y).re = 0 := by
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), |tentBoundaryError g h (y / h)| < 1 / 4 := by
    simpa only [Real.norm_eq_abs] using
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_tentBoundaryError_width_zero hgi hy0)
        ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hw : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (min y (min (1 - y) 1)) :=
    Ioo_mem_nhdsGT (lt_min hy0 (lt_min (sub_pos.mpr hy1) zero_lt_one))
  have hz : ∀ᶠ h in 𝓝[>] (0 : ℝ), normalizedTentBoundary g (h / 2) y = 0 := by
    filter_upwards [hw, hsmall] with h hh he
    have hhy : h < y := (lt_min_iff.mp hh.2).1
    have hh1 : h ≤ 1 := (lt_min_iff.mp (lt_min_iff.mp hh.2).2).2.le
    have hgap : y + h ≤ 1 := by
      have hhgap := (lt_min_iff.mp (lt_min_iff.mp hh.2).2).1
      linarith only [hhgap]
    have hid := beurling_tent_identity B hBsum hgm hgb hgi hθ hh.1 hh1 hhy
    rw [tentAtomMass_eq_zero_in_unit_gap B.one_le_intNorm hh.1 hgap] at hid
    have hP : tentRecurrentPart B.intNorm β h y < 1 / 4 := by
      have hb := (abs_lt.mp he).1
      linarith only [hid, hb]
    have hQ := beurling_tentRecurrentPart_half_eq_zero B hBsum hgm hgb hgi hθ hh.1 hh1 hP
    have hh2 : 0 < h / 2 := half_pos hh.1
    have hid2 := beurling_tent_identity B hBsum hgm hgb hgi hθ (y := y) hh2
      (by linarith only [hh1, hh.1]) (by linarith only [hhy, hh.1])
    rw [tentAtomMass_eq_zero_in_unit_gap B.one_le_intNorm hh2 (by linarith only [hgap, hh.1]),
      hQ, zero_add, tentBoundaryError_eq_normalized g hh2] at hid2
    exact (mul_eq_zero.mp hid2.symm).resolve_left hh2.ne'
  have ht : Tendsto (fun h : ℝ => h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((by fun_prop : Continuous fun h : ℝ => h / 2).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact half_pos (show (0 : ℝ) < h from hh)
  have hl := (tendsto_normalizedTentBoundary hgi hy0).comp ht
  have hzero : Tendsto (fun h : ℝ => normalizedTentBoundary g (h / 2) y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hl hzero

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.beurling_defectBoundary_re_eq_zero_on_unit_gap
#print axioms GaloisForLFunctions.ExactEventTheory.defectBoundary_re_even_of_theta_defect
