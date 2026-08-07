import GaloisForLFunctions.HTGeometry.PrimeNormalFlowResolvent

/-!
# The prime normal flow solves the boundary normal equation

The flow `F(L) = (L I - T/2)^{-1/2}` satisfies the differentiated prime-only boundary normal
equation `(2L I - T) F' + F = 0`, has half-log trace the identity, and is bounded by
`(L - ‖T‖/2)^{-1/2}`.  Each statement is the functional calculus of a scalar identity that holds
uniformly on the spectrum.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The symbol of the derivative of the prime normal flow. -/
noncomputable def flowDerivSymbol (L t : ℝ) : ℝ := -(1 / 2) * flowSymbol L t ^ 3

theorem continuousOn_flowDerivSymbol {T : A} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ContinuousOn (flowDerivSymbol L) (spectrum ℝ T) :=
  continuousOn_const.mul ((continuousOn_flowSymbol hL).pow 3)

/-- **The prime normal flow solves the differentiated boundary normal equation `(1)`.** -/
theorem primeNormalFlow_equation {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ((2 * L) • (1 : A) - T) * cfc (flowDerivSymbol L) T + primeNormalFlow T L = 0 := by
  show ((2 * L) • (1 : A) - T) * cfc (flowDerivSymbol L) T + cfc (flowSymbol L) T = 0
  have hshift : cfc (fun t : ℝ => 2 * L - t) T = (2 * L) • (1 : A) - T := by
    rw [cfc_sub _ _ T (by fun_prop) (by fun_prop), cfc_const (2 * L) T, cfc_id' ℝ T hT,
      Algebra.algebraMap_eq_smul_one]
  have hprod : cfc (fun t : ℝ => (2 * L - t) * flowDerivSymbol L t) T
      = ((2 * L) • (1 : A) - T) * cfc (flowDerivSymbol L) T := by
    rw [cfc_mul _ _ T (by fun_prop) (continuousOn_flowDerivSymbol hL), hshift]
  have hsym : ∀ t ∈ spectrum ℝ T, (2 * L - t) * flowDerivSymbol L t + flowSymbol L t = 0 := by
    intro t ht
    have hu : 0 < L - t / 2 := flow_shift_pos hL ht
    have hp : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr hu
    have hp2 : Real.sqrt (L - t / 2) ^ 2 = L - t / 2 := Real.sq_sqrt hu.le
    have hkey : 2 * (L - t / 2) * (-(1 / 2) * (Real.sqrt (L - t / 2))⁻¹ ^ 3)
        + (Real.sqrt (L - t / 2))⁻¹ = 0 := by
      set p := Real.sqrt (L - t / 2) with hpdef
      rw [← hp2]
      field_simp
      ring
    rw [flowDerivSymbol, flowSymbol, show 2 * L - t = 2 * (L - t / 2) by ring]
    exact hkey
  have hzero : cfc (fun t : ℝ => (2 * L - t) * flowDerivSymbol L t + flowSymbol L t) T = 0 := by
    rw [cfc_congr (f := fun t : ℝ => (2 * L - t) * flowDerivSymbol L t + flowSymbol L t)
      (g := fun _ : ℝ => (0 : ℝ)) hsym, cfc_const 0 T, map_zero]
  have hc1 : ContinuousOn (fun t : ℝ => (2 * L - t) * flowDerivSymbol L t) (spectrum ℝ T) :=
    (continuousOn_const.sub continuousOn_id).mul (continuousOn_flowDerivSymbol hL)
  rw [← hprod]
  rw [show cfc (fun t : ℝ => (2 * L - t) * flowDerivSymbol L t) T + cfc (flowSymbol L) T
      = cfc (fun t : ℝ => (2 * L - t) * flowDerivSymbol L t + flowSymbol L t) T from
    (cfc_add T _ (flowSymbol L) hc1 (continuousOn_flowSymbol hL)).symm]
  exact hzero

/-- **The resolvent bound `(7)`:** `‖F(L)‖ ≤ (L − ‖T‖/2)^{-1/2}`. -/
theorem norm_primeNormalFlow_le {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ‖primeNormalFlow T L‖ ≤ (Real.sqrt (L - ‖T‖ / 2))⁻¹ := by
  refine norm_cfc_le_of_forall_le (𝕜 := ℝ) _ T (continuousOn_flowSymbol hL) hT ?_
  intro t ht
  have hu : 0 < L - t / 2 := flow_shift_pos hL ht
  have hd : (0 : ℝ) < L - ‖T‖ / 2 := by linarith
  have htn : t ≤ ‖T‖ := le_trans (le_abs_self t) (abs_le_norm_of_mem_spectrum ht)
  have hle : Real.sqrt (L - ‖T‖ / 2) ≤ Real.sqrt (L - t / 2) := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (L - ‖T‖ / 2) := Real.sqrt_pos.mpr hd
  rw [Real.norm_eq_abs, flowSymbol, abs_of_pos (by positivity)]
  exact inv_anti₀ hpos hle

/-- The half-log trace symbol defect, in closed form. -/
theorem abs_traceSymbol_le {T : A} {L t : ℝ} (hL : ‖T‖ / 2 < L) (ht : t ∈ spectrum ℝ T) :
    |Real.sqrt L * flowSymbol L t - 1| ≤ ‖T‖ / 2 / (Real.sqrt (L - ‖T‖ / 2) * Real.sqrt L) := by
  have hTn : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have hL0 : 0 < L := by linarith
  have hd : (0 : ℝ) < L - ‖T‖ / 2 := by linarith
  have habs := abs_le_norm_of_mem_spectrum ht
  have hu : 0 < L - t / 2 := flow_shift_pos hL ht
  have hp : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr hu
  have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hp2 : Real.sqrt (L - t / 2) ^ 2 = L - t / 2 := Real.sq_sqrt hu.le
  have hr2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hid : Real.sqrt L * flowSymbol L t - 1
      = t / 2 / (Real.sqrt (L - t / 2) * (Real.sqrt L + Real.sqrt (L - t / 2))) := by
    have hkey : ∀ p r : ℝ, 0 < p → 0 < r → r ^ 2 - p ^ 2 = t / 2 →
        r * p⁻¹ - 1 = t / 2 / (p * (r + p)) := by
      intro p r hp' hr' hrp
      rw [eq_div_iff (by positivity)]
      have hfac : (r * p⁻¹ - 1) * (p * (r + p)) = (r - p) * (r + p) := by
        field_simp
      rw [hfac]
      linear_combination hrp
    rw [flowSymbol]
    exact hkey _ _ hp hr (by rw [hp2, hr2]; ring)
  have hnum : |t / 2| ≤ ‖T‖ / 2 := by
    rw [abs_div, abs_two]
    linarith
  have hden : Real.sqrt (L - ‖T‖ / 2) * Real.sqrt L
      ≤ Real.sqrt (L - t / 2) * (Real.sqrt L + Real.sqrt (L - t / 2)) := by
    have h1 : Real.sqrt (L - ‖T‖ / 2) ≤ Real.sqrt (L - t / 2) :=
      Real.sqrt_le_sqrt (by linarith [le_trans (le_abs_self t) habs])
    have h2 : Real.sqrt L ≤ Real.sqrt L + Real.sqrt (L - t / 2) := by linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hdpos : 0 < Real.sqrt (L - t / 2) * (Real.sqrt L + Real.sqrt (L - t / 2)) :=
    mul_pos hp (by linarith)
  rw [hid, abs_div, abs_of_pos hdpos]
  rw [div_le_div_iff₀ hdpos (by positivity)]
  have hstep : |t / 2| * (Real.sqrt (L - ‖T‖ / 2) * Real.sqrt L)
      ≤ (‖T‖ / 2) * (Real.sqrt (L - t / 2) * (Real.sqrt L + Real.sqrt (L - t / 2))) :=
    mul_le_mul hnum hden (by positivity) (by linarith)
  exact hstep

omit [Nontrivial A] in
/-- The trace bound vanishes at infinity. -/
theorem tendsto_traceBound (T : A) :
    Tendsto (fun L : ℝ => ‖T‖ / 2 / (Real.sqrt (L - ‖T‖ / 2) * Real.sqrt L)) atTop (𝓝 0) := by
  refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
  refine Filter.Tendsto.atTop_mul_atTop₀ ?_ Real.tendsto_sqrt_atTop
  refine Real.tendsto_sqrt_atTop.comp ?_
  simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(‖T‖ / 2)) tendsto_id

/-- **The half-log trace `(3)`:** `sqrt(L) F(L)` converges in norm to the identity. -/
theorem tendsto_sqrt_smul_primeNormalFlow {T : A} (hT : IsSelfAdjoint T) :
    Tendsto (fun L => Real.sqrt L • primeNormalFlow T L) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun L => norm_nonneg _) ?_ (tendsto_traceBound T)
  filter_upwards [eventually_gt_atTop (‖T‖ / 2)] with L hL
  have hcf := continuousOn_flowSymbol (T := T) hL
  have hcs : ContinuousOn (fun t : ℝ => Real.sqrt L * flowSymbol L t - 1) (spectrum ℝ T) :=
    (continuousOn_const.mul hcf).sub continuousOn_const
  have hone : cfc (fun _ : ℝ => (1 : ℝ)) T = 1 := by rw [cfc_const 1 T, map_one]
  have hrepr : cfc (fun t : ℝ => Real.sqrt L * flowSymbol L t - 1) T
      = Real.sqrt L • primeNormalFlow T L - 1 := by
    have h1 := cfc_sub (fun t : ℝ => Real.sqrt L * flowSymbol L t) (fun _ : ℝ => (1 : ℝ)) T
      (continuousOn_const.mul hcf) continuousOn_const
    rw [h1, cfc_const_mul _ _ T hcf, hone]
    rfl
  rw [← hrepr]
  exact norm_cfc_le_of_forall_le (𝕜 := ℝ) _ T hcs hT
    (fun t ht => by rw [Real.norm_eq_abs]; exact abs_traceSymbol_le hL ht)


end GaloisForLFunctions.HTGeometry
