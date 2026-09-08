import GaloisForLFunctions.RHTower.FokasLenellsHardyOrientation
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Strong L² limits of the damped Hardy projections

Damping the Fourier datum by exp(-2π |h| |s|) gives contractions on both
half-rays. Dominated multiplier convergence gives their strong boundary limits.
The signed transforms recover exactly the C⁺ and C⁻ conventions used by the
Fokas–Lenells RH inverse. Identification with horizontal Cauchy-integral slices
is supplied separately by the Fourier–Laplace kernel formula.
-/

open MeasureTheory Complex Set Filter Topology
namespace RHTower.FokasLenells
noncomputable section

def cauchyRay (upper : Bool) : Set ℝ := if upper then Iio 0 else Ioi 0

theorem measurableSet_cauchyRay (upper : Bool) : MeasurableSet (cauchyRay upper) := by
  cases upper <;> simp only [cauchyRay,Bool.false_eq_true,↓reduceIte]
  · exact measurableSet_Ioi
  · exact measurableSet_Iio

/-- A bounded Fourier datum multiplier at every real height, including the boundary. -/
def cauchyDamping (upper : Bool) (h s : ℝ) : ℂ :=
  (cauchyRay upper).indicator (fun s => ((Real.exp (-2*Real.pi*|h| *|s|):ℝ):ℂ)) s

theorem measurable_cauchyDamping (upper : Bool) (h : ℝ) : Measurable (cauchyDamping upper h) := by
  exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul continuous_abs))).measurable).indicator (measurableSet_cauchyRay upper)

theorem norm_cauchyDamping_le_one (upper : Bool) (h s : ℝ) : ‖cauchyDamping upper h s‖ ≤ 1 := by
  by_cases hs : s ∈ cauchyRay upper
  · rw [cauchyDamping,Set.indicator_of_mem hs,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (abs_nonneg h)) (abs_nonneg s)]
  · rw [cauchyDamping,Set.indicator_of_notMem hs,norm_zero]
    exact zero_le_one

theorem continuous_cauchyDamping_height (upper : Bool) (s : ℝ) :
    Continuous (fun h => cauchyDamping upper h s) := by
  by_cases hs : s ∈ cauchyRay upper
  · simp only [cauchyDamping,Set.indicator_of_mem hs]
    fun_prop
  · simp only [cauchyDamping,Set.indicator_of_notMem hs]
    exact continuous_const

/-- Damping and cutting the datum is a contraction, including at height zero. -/
def dampedCauchyDatum (upper : Bool) (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_cauchyDamping upper h) zero_le_one (norm_cauchyDamping_le_one upper h)

theorem dampedCauchyDatum_ae (upper : Bool) (h : ℝ) (u : SoninL2) :
    (dampedCauchyDatum upper h u : ℝ → ℂ) =ᵐ[volume]
      (fun s => cauchyDamping upper h s*(u : ℝ → ℂ) s) :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (measurable_cauchyDamping upper h) zero_le_one (norm_cauchyDamping_le_one upper h) u

theorem dampedCauchyDatum_bound (upper : Bool) (h : ℝ) (u : SoninL2) :
    ‖dampedCauchyDatum upper h u‖ ≤ ‖u‖ := by
  have hb : ‖dampedCauchyDatum upper h‖ ≤ 1 :=
    norm_lpBoundedMulCLM_le (measurable_cauchyDamping upper h) zero_le_one
      (norm_cauchyDamping_le_one upper h)
  exact ((dampedCauchyDatum upper h).le_opNorm u).trans
    (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg u))

theorem dampedCauchyDatum_zero (upper : Bool) (u : SoninL2) :
    dampedCauchyDatum upper 0 u = indicatorCutoff (cauchyRay upper) (measurableSet_cauchyRay upper) u := by
  apply Lp.ext
  filter_upwards [dampedCauchyDatum_ae upper 0 u,
    indicatorCutoff_ae (cauchyRay upper) (measurableSet_cauchyRay upper) u] with s h1 h2
  rw [h1,h2]
  by_cases hs : s ∈ cauchyRay upper <;> simp [cauchyDamping,hs]

/-- Strong continuity follows from the corpus's dominated multiplier convergence theorem. -/
theorem continuous_dampedCauchyDatum (upper : Bool) (u : SoninL2) :
    Continuous (fun h => dampedCauchyDatum upper h u) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact tendsto_lpBoundedMulCLM_apply (measurable_cauchyDamping upper)
    (measurable_cauchyDamping upper a) zero_le_one (norm_cauchyDamping_le_one upper)
    (norm_cauchyDamping_le_one upper a)
    (fun s => (continuous_cauchyDamping_height upper s).tendsto a) u

/-- The two datum cutoffs sum to the identity because their omitted common endpoint is null. -/
theorem cauchyRayCutoff_sum (u : SoninL2) :
    indicatorCutoff (Iio 0) measurableSet_Iio u+indicatorCutoff (Ioi 0) measurableSet_Ioi u = u := by
  have hn : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Iio 0) measurableSet_Iio u,
    indicatorCutoff_ae (Ioi 0) measurableSet_Ioi u,
    Lp.coeFn_add (indicatorCutoff (Iio 0) measurableSet_Iio u)
      (indicatorCutoff (Ioi 0) measurableSet_Ioi u),hn] with s h1 h2 h3 hn
  rw [h3,Pi.add_apply,h1,h2]
  rcases lt_or_gt_of_ne hn with hs | hs
  · simp [hs,not_lt.mpr hs.le]
  · simp [hs,not_lt.mpr hs.le]

/-- The sign is positive above and negative below the real contour. -/
def cauchyTrace (u : SoninL2) (upper : Bool) (h : ℝ) : SoninL2 :=
  (if upper then (1:ℂ) else -1) • fourierUnitary (dampedCauchyDatum upper h (fourierUnitary.symm u))

theorem cauchyTrace_bound (u : SoninL2) (upper : Bool) (h : ℝ) : ‖cauchyTrace u upper h‖ ≤ ‖u‖ := by
  cases upper <;> simpa [cauchyTrace,fourierUnitary.norm_map] using
    dampedCauchyDatum_bound _ h (fourierUnitary.symm u)

theorem continuous_cauchyTrace (u : SoninL2) (upper : Bool) :
    Continuous (cauchyTrace u upper) := by
  exact (fourierUnitary.continuous.comp
    (continuous_dampedCauchyDatum upper (fourierUnitary.symm u))).const_smul (if upper then (1:ℂ) else -1)

theorem cauchyTrace_lower_zero (u : SoninL2) : cauchyTrace u false 0 = negativeCauchy u := by
  simp only [cauchyTrace,dampedCauchyDatum_zero,Bool.false_eq_true,↓reduceIte,neg_smul,one_smul]
  rfl

theorem cauchyTrace_upper_zero (u : SoninL2) : cauchyTrace u true 0 = u+negativeCauchy u := by
  have he := congrArg fourierUnitary (cauchyRayCutoff_sum (fourierUnitary.symm u))
  rw [map_add,fourierUnitary.apply_symm_apply] at he
  simp only [cauchyTrace,dampedCauchyDatum_zero,↓reduceIte,one_smul,cauchyRay] at ⊢
  change fourierUnitary (indicatorCutoff (Iio 0) measurableSet_Iio (fourierUnitary.symm u)) =
    u+(-fourierUnitary (indicatorCutoff (Ioi 0) measurableSet_Ioi (fourierUnitary.symm u)))
  exact eq_add_neg_iff_add_eq.mpr he

/-- The strong lower boundary limit is exactly the signed negative Cauchy projection. -/
theorem cauchyTrace_lower_tendsto (u : SoninL2) :
    Tendsto (cauchyTrace u false) (𝓝 0) (𝓝 (negativeCauchy u)) := by
  simpa only [cauchyTrace_lower_zero] using (continuous_cauchyTrace u false).tendsto 0

/-- The strong upper boundary limit differs from C⁻ by the identity, the Plemelj split. -/
theorem cauchyTrace_upper_tendsto (u : SoninL2) :
    Tendsto (cauchyTrace u true) (𝓝 0) (𝓝 (u+negativeCauchy u)) := by
  simpa only [cauchyTrace_upper_zero] using (continuous_cauchyTrace u true).tendsto 0

end
end RHTower.FokasLenells
