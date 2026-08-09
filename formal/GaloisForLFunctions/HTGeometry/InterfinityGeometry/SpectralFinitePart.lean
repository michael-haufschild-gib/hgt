import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralHorizonCocycle

/-!
# Finite-part primitives of the singular Laplace source

In the chart `f = s^ρ h` the pairing of the source cochain with a test vector is

`⟨b_V, f⟩ = c ∫₀¹ (e^{-Vs} − 1) h(s) s^{a-1} ds`,  `a = ρ + β`,

which converges for every `a > −1`.  Its primitive is the finite part

* `a > 0`:      `η_a(h) = c ∫₀¹ h(s) s^{a-1} ds`;
* `−1 < a < 0`: `η_a(h) = c (∫₀¹ (h(s) − h(0)) s^{a-1} ds + h(0)/a)`;
* `a = 0`:      `η_a(h) = c ∫₀¹ (h(s) − h(0)) s^{-1} ds`.

This file constructs chart functions, proves the three integrals convergent, and prepares the
primitive identity by exhibiting the transported chart `e^{-V·}h` as a chart function with the same
value at the origin.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## Chart functions -/

/-- A chart function of the test space: continuous on `[0,1]`, bounded there, and with a linear
modulus of continuity at the origin. -/
structure ChartFun where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- Continuity on the closed unit interval. -/
  continuousOn' : ContinuousOn toFun (Icc 0 1)
  /-- A common bound for the size and for the modulus of continuity at the origin. -/
  exists_bound : ∃ B : ℝ, 0 ≤ B ∧ (∀ s ∈ Icc (0 : ℝ) 1, |toFun s| ≤ B) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, |toFun s - toFun 0| ≤ B * s

namespace ChartFun

/-- Every continuously differentiable function is a chart function. -/
def ofContDiff (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) : ChartFun where
  toFun := h
  continuousOn' := hh.continuous.continuousOn
  exists_bound := by
    obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hh.continuous.continuousOn
    obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hh.continuous_deriv le_rfl).continuousOn
    refine ⟨max (max C₁ C₂) 0, le_max_right _ _, ?_, ?_⟩
    · exact fun s hs => le_trans (hC₁ s hs) (le_trans (le_max_left _ _) (le_max_left _ _))
    · intro s hs
      have hderiv : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv h x‖ ≤ max (max C₁ C₂) 0 := fun x hx =>
        le_trans (hC₂ x hx) (le_trans (le_max_right _ _) (le_max_left _ _))
      have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
        (fun x _ => hh.differentiable (by norm_num) x) hderiv (left_mem_Icc.2 zero_le_one) hs
      simpa [Real.norm_eq_abs, abs_of_nonneg hs.1] using hmvt

@[simp] theorem ofContDiff_toFun (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) :
    (ofContDiff h hh).toFun = h := rfl

/-- The transported chart `s ↦ e^{-Vs} h(s)`. -/
def transport (V : ℝ) (hV : 0 ≤ V) (h : ChartFun) : ChartFun where
  toFun := fun s => Real.exp (-(V * s)) * h.toFun s
  continuousOn' :=
    (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul h.continuousOn'
  exists_bound := by
    obtain ⟨B, hB0, hBsize, hBmod⟩ := h.exists_bound
    refine ⟨(V + 1) * B, mul_nonneg (by linarith) hB0, ?_, ?_⟩
    · intro s hs
      have hexp : Real.exp (-(V * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hs.1])
      have hexp0 : (0 : ℝ) < Real.exp (-(V * s)) := Real.exp_pos _
      rw [abs_mul, abs_of_pos hexp0]
      nlinarith [hBsize s hs, abs_nonneg (h.toFun s)]
    · intro s hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have hcoc : |laplaceCochain V s| ≤ V * s := abs_laplaceCochain_le hV hs0
      have hb := hBsize s hs
      have hm := hBmod s hs
      have hzero : Real.exp (-(V * 0)) * h.toFun 0 = h.toFun 0 := by simp
      rw [hzero]
      have hsplit : Real.exp (-(V * s)) * h.toFun s - h.toFun 0 =
          laplaceCochain V s * h.toFun s + (h.toFun s - h.toFun 0) := by
        simp only [laplaceCochain]
        ring
      rw [hsplit]
      calc |laplaceCochain V s * h.toFun s + (h.toFun s - h.toFun 0)|
          ≤ |laplaceCochain V s * h.toFun s| + |h.toFun s - h.toFun 0| := abs_add_le _ _
        _ ≤ V * s * B + B * s := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul hcoc hb (abs_nonneg _) (mul_nonneg hV hs0)) hm
        _ = (V + 1) * B * s := by ring

@[simp] theorem transport_toFun (V : ℝ) (hV : 0 ≤ V) (h : ChartFun) (s : ℝ) :
    (transport V hV h).toFun s = Real.exp (-(V * s)) * h.toFun s := rfl

@[simp] theorem transport_zero (V : ℝ) (hV : 0 ≤ V) (h : ChartFun) :
    (transport V hV h).toFun 0 = h.toFun 0 := by
  simp [transport]

end ChartFun

/-! ## Convergence of the three finite-part integrals -/

theorem integrableOn_rpow_of_neg_one_lt {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun s : ℝ => s ^ a) (Ioo 0 1) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 ha

theorem rpow_succ_split {s : ℝ} (hs : 0 < s) (a : ℝ) : s * s ^ (a - 1) = s ^ a := by
  nth_rewrite 1 [← Real.rpow_one s]
  rw [← Real.rpow_add hs]
  congr 1
  ring

/-- The size integral converges for a positive exponent. -/
theorem integrableOn_chart_mul_rpow (h : ChartFun) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => h.toFun s * s ^ (a - 1)) (Ioo 0 1) := by
  obtain ⟨B, hB0, hBsize, -⟩ := h.exists_bound
  refine Integrable.mono' (g := fun s : ℝ => B * s ^ (a - 1))
    ((integrableOn_rpow_of_neg_one_lt (by linarith)).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact (h.continuousOn'.mono Ioo_subset_Icc_self).mul
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
    exact mul_le_mul_of_nonneg_right (hBsize s ⟨hs0.le, hs.2.le⟩) hw.le

/-- The finite-part integral converges for every exponent above `−1`. -/
theorem integrableOn_chart_sub_mul_rpow (h : ChartFun) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun s : ℝ => (h.toFun s - h.toFun 0) * s ^ (a - 1)) (Ioo 0 1) := by
  obtain ⟨B, hB0, -, hBmod⟩ := h.exists_bound
  refine Integrable.mono' (g := fun s : ℝ => B * s ^ a)
    ((integrableOn_rpow_of_neg_one_lt ha).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ((h.continuousOn'.mono Ioo_subset_Icc_self).sub continuousOn_const).mul
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw, ← rpow_succ_split hs0 a]
    calc |h.toFun s - h.toFun 0| * s ^ (a - 1) ≤ B * s * s ^ (a - 1) :=
          mul_le_mul_of_nonneg_right (hBmod s ⟨hs0.le, hs.2.le⟩) hw.le
      _ = B * (s * s ^ (a - 1)) := by ring

/-- The pairing integral converges for every exponent above `−1`. -/
theorem integrableOn_source_pairing (h : ChartFun) {a V : ℝ} (ha : -1 < a) (hV : 0 ≤ V) :
    IntegrableOn (fun s : ℝ => laplaceCochain V s * h.toFun s * s ^ (a - 1)) (Ioo 0 1) := by
  obtain ⟨B, hB0, hBsize, -⟩ := h.exists_bound
  refine Integrable.mono' (g := fun s : ℝ => V * B * s ^ a)
    ((integrableOn_rpow_of_neg_one_lt ha).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (h.continuousOn'.mono Ioo_subset_Icc_self)) ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).sub continuous_const).continuousOn
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
    have hcoc : |laplaceCochain V s| ≤ V * s := abs_laplaceCochain_le hV hs0.le
    have hb := hBsize s ⟨hs0.le, hs.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, ← rpow_succ_split hs0 a]
    calc |laplaceCochain V s| * |h.toFun s| * s ^ (a - 1)
        ≤ V * s * B * s ^ (a - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hw.le
          exact mul_le_mul hcoc hb (abs_nonneg _) (mul_nonneg hV hs0.le)
      _ = V * B * (s * s ^ (a - 1)) := by ring

end

end GaloisForLFunctions.HTGeometry.Interfinity
