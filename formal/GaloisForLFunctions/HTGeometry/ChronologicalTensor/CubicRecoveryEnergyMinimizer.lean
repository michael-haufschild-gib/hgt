import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryEquilibriumMeasure
import GaloisForLFunctions.HTGeometry.GaussianFrullaniLogKernel

/-!
# The recovery measure minimizes the weighted logarithmic energy

With the kernel `K(x,y) = log(2/|x - y|)` (`= ∞` on the diagonal) and the field
`Q(x) = -½ log(1 - |x|)` (`= ∞` at `|x| = 1`), the weighted energy of a probability measure `ν` on
`[-1, 1]` is

  `I_Q(ν) = ∫∫ K dν dν + 2 ∫ Q dν ∈ [0, ∞]`

(the classical weighted energy plus `log 2`).  The mixture `μ = ∫_0^b ν_a h(a) da` has finite
weighted energy and

  `I_Q(μ) ≤ I_Q(ν)`  for every probability measure `ν` on `[-1, 1]`:

`μ` is atomless and supported on `[-b, b]`; its potential `U(x) = ∫ K(x,y) dμ(y)` satisfies
`U + Q ≥ log 2 - log C` on `[-1, 1]` with equality on `[-b, b]`; and the logarithmic energy is
positive definite, `2 E(ν, μ) ≤ E(ν, ν) + E(μ, μ)`.  The minimizer is unique: equality forces equal
Gaussian moments `∫ x^n e^{-s x²}` at some `s > 0`, and these determine a measure on `[-1, 1]`.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

open GaloisForLFunctions.HTGeometry

/-- The field `Q(x) = -½ log(1 - |x|)` on `(-1, 1)`, infinite elsewhere. -/
def recoveryField (x : ℝ) : ℝ≥0∞ :=
  if |x| < 1 then ENNReal.ofReal (-Real.log (1 - |x|) / 2) else ⊤

/-- The weighted energy `I_Q(ν) = ∫∫ K dν dν + 2 ∫ Q dν`. -/
def recoveryWeightedEnergy (ν : Measure ℝ) : ℝ≥0∞ :=
  frullaniEnergy ν ν + 2 * ∫⁻ x, recoveryField x ∂ν

theorem measurable_recoveryField : Measurable recoveryField :=
  Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (Measurable.ennreal_ofReal (by fun_prop)) measurable_const

/-! ### Support and atoms of `μ` -/

theorem ae_recoveryMixingLaw_mem : ∀ᵐ a ∂recoveryMixingLaw, a ∈ Ioc 0 recoveryEdge :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

/-- `μ` lives on `[-b, b]`. -/
theorem ae_recoveryEquilibriumMeasure_abs_le :
    ∀ᵐ y ∂recoveryEquilibriumMeasure, |y| ≤ recoveryEdge := by
  rw [recoveryEquilibriumMeasure, ae_map_iff measurable_mul_cos.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  refine (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => |p.1 * Real.cos p.2| ≤ recoveryEdge)
    (measurableSet_le (by fun_prop) measurable_const)).mpr ?_
  filter_upwards [ae_recoveryMixingLaw_mem] with a ha
  refine Eventually.of_forall fun θ => ?_
  rw [abs_mul, abs_of_pos ha.1]
  calc a * |Real.cos θ| ≤ a * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) ha.1.le
    _ ≤ recoveryEdge := by linarith [ha.2]

theorem ae_recoveryEquilibriumMeasure_abs_le_one :
    ∀ᵐ y ∂recoveryEquilibriumMeasure, |y| ≤ 1 :=
  ae_recoveryEquilibriumMeasure_abs_le.mono fun _ h => h.trans recoveryEdge_mem.2.le

/-- **`μ` has no atoms.** -/
theorem recoveryEquilibriumMeasure_singleton (x : ℝ) : recoveryEquilibriumMeasure {x} = 0 := by
  rw [recoveryEquilibriumMeasure, Measure.map_apply measurable_mul_cos (measurableSet_singleton x),
    Measure.prod_apply (measurable_mul_cos (measurableSet_singleton x))]
  refine (lintegral_congr_ae ?_).trans (lintegral_zero)
  filter_upwards [ae_recoveryMixingLaw_mem] with a ha
  have hsub : Prod.mk a ⁻¹' ((fun p : ℝ × ℝ => p.1 * Real.cos p.2) ⁻¹' {x}) ⊆
      {θ | Real.cos θ = x / a} := fun θ hθ => by
    simp only [mem_preimage, mem_singleton_iff] at hθ
    simp only [mem_setOf_eq]
    rw [← hθ]; field_simp [ha.1.ne']
  exact measure_mono_null hsub ((countable_cos_eq _).measure_zero _)

/-! ### The potential in kernel form -/

theorem integrable_log_abs_sub_recoveryEquilibriumMeasure {x : ℝ} (hx : |x| ≤ 1) :
    Integrable (fun y => Real.log |x - y|) recoveryEquilibriumMeasure := by
  rw [recoveryEquilibriumMeasure, integrable_map_measure
    (measurable_log_abs_sub x).aestronglyMeasurable measurable_mul_cos.aemeasurable]
  exact integrable_log_abs_sub_recoveryMixture hx

/-- The kernel potential `U(x) = ∫ K(x,y) dμ(y)`. -/
def recoveryKernelPotential (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, frullaniLogKernel x y ∂recoveryEquilibriumMeasure

theorem measurable_recoveryKernelPotential : Measurable recoveryKernelPotential :=
  measurable_frullaniLogKernel.lintegral_prod_right'

/-- `U(x) = log 2 - ∫ log|x - y| dμ(y)` for `|x| ≤ 1`. -/
theorem recoveryKernelPotential_eq {x : ℝ} (hx : |x| ≤ 1) :
    recoveryKernelPotential x =
      ENNReal.ofReal (Real.log 2 - ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure) := by
  have hint := integrable_log_abs_sub_recoveryEquilibriumMeasure hx
  have hne : ∀ᵐ y ∂recoveryEquilibriumMeasure, y ≠ x :=
    measure_eq_zero_iff_ae_notMem.mp (recoveryEquilibriumMeasure_singleton x) |>.mono
      fun y hy h => hy (h ▸ mem_singleton y)
  have h2 : ∀ᵐ y ∂recoveryEquilibriumMeasure, |x - y| ≤ 2 :=
    ae_recoveryEquilibriumMeasure_abs_le_one.mono fun y hy =>
      (abs_sub x y).trans (by linarith)
  have hle : ∀ᵐ y ∂recoveryEquilibriumMeasure, 0 ≤ Real.log 2 - Real.log |x - y| := by
    filter_upwards [h2] with y hy
    rcases eq_or_lt_of_le (abs_nonneg (x - y)) with h0 | hpos
    · rw [← h0, Real.log_zero, sub_zero]; exact (Real.log_pos (by norm_num)).le
    · linarith [Real.log_le_log hpos hy]
  have hint2 : Integrable (fun y => Real.log 2 - Real.log |x - y|) recoveryEquilibriumMeasure :=
    (integrable_const _).sub hint
  rw [recoveryKernelPotential, lintegral_congr_ae (g := fun y =>
      ENNReal.ofReal (Real.log 2 - Real.log |x - y|)) ?_,
    ← ofReal_integral_eq_lintegral_ofReal hint2 hle,
    integral_sub (integrable_const _) hint, MeasureTheory.integral_const, probReal_univ,
    one_smul]
  filter_upwards [hne, h2] with y hy1 hy2
  exact frullaniLogKernel_eq (Ne.symm hy1) hy2

/-- The equilibrium constant `c₀ = log 2 - log C`. -/
def recoveryEquilibriumConstant : ℝ := Real.log 2 - Real.log (recoveryCapacity recoveryEdge)

theorem log_abs_sub_le_log_two {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.log |x - y| ≤ Real.log 2 := by
  rcases eq_or_lt_of_le (abs_nonneg (x - y)) with h0 | hpos
  · rw [← h0, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
  · exact Real.log_le_log hpos ((abs_sub x y).trans (by linarith))

theorem integral_log_abs_sub_le_log_two {x : ℝ} (hx : |x| ≤ 1) :
    ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure ≤ Real.log 2 := by
  have h := integral_mono_ae (integrable_log_abs_sub_recoveryEquilibriumMeasure hx)
    (integrable_const (Real.log 2)) (ae_recoveryEquilibriumMeasure_abs_le_one.mono
      fun y hy => log_abs_sub_le_log_two hx hy)
  rwa [MeasureTheory.integral_const, probReal_univ, one_smul] at h

/-- **`U + Q ≥ c₀` on `[-1, 1]`.** -/
theorem recoveryEquilibriumConstant_le {x : ℝ} (hx : |x| ≤ 1) :
    ENNReal.ofReal recoveryEquilibriumConstant ≤
      recoveryKernelPotential x + recoveryField x := by
  rcases eq_or_lt_of_le hx with h1 | h1
  · simp [recoveryField, h1]
  rw [recoveryKernelPotential_eq hx, recoveryField, if_pos h1,
    ← ENNReal.ofReal_add (by linarith [integral_log_abs_sub_le_log_two hx])
      (by have := Real.log_nonpos (by linarith [abs_nonneg x]) (by linarith [abs_nonneg x] :
        1 - |x| ≤ 1); linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [recoveryEquilibriumConstant]
  have hpot : ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure ≤
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - |x|) / 2 := by
    rcases le_or_gt |x| recoveryEdge with hb | hb
    · exact (recoveryEquilibrium_potential_eq hb).le
    · exact (recoveryEquilibrium_potential_lt hb h1).le
  linarith

/-- **`U + Q = c₀` on `[-b, b]`.** -/
theorem recoveryKernelPotential_add_field_eq {x : ℝ} (hx : |x| ≤ recoveryEdge) :
    recoveryKernelPotential x + recoveryField x = ENNReal.ofReal recoveryEquilibriumConstant := by
  have hx1 : |x| < 1 := hx.trans_lt recoveryEdge_mem.2
  rw [recoveryKernelPotential_eq hx1.le, recoveryField, if_pos hx1,
    ← ENNReal.ofReal_add (by linarith [integral_log_abs_sub_le_log_two hx1.le])
      (by have := Real.log_nonpos (by linarith [abs_nonneg x]) (by linarith [abs_nonneg x] :
        1 - |x| ≤ 1); linarith), recoveryEquilibrium_potential_eq hx, recoveryEquilibriumConstant]
  congr 1; ring

/-! ### Minimality -/

theorem frullaniEnergy_recovery_add_field :
    frullaniEnergy recoveryEquilibriumMeasure recoveryEquilibriumMeasure +
      ∫⁻ x, recoveryField x ∂recoveryEquilibriumMeasure =
      ENNReal.ofReal recoveryEquilibriumConstant := by
  rw [frullaniEnergy]
  change ∫⁻ x, recoveryKernelPotential x ∂recoveryEquilibriumMeasure + _ = _
  rw [← lintegral_add_left measurable_recoveryKernelPotential]
  · rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal recoveryEquilibriumConstant),
      lintegral_const, measure_univ, mul_one]
    filter_upwards [ae_recoveryEquilibriumMeasure_abs_le] with x hx
    exact recoveryKernelPotential_add_field_eq hx

/-- **The recovery measure minimizes the weighted energy**: `I_Q(μ) ≤ I_Q(ν)` for every
probability measure `ν` on `[-1, 1]`, and `I_Q(μ) < ∞`. -/
theorem recoveryWeightedEnergy_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, |x| ≤ 1) :
    recoveryWeightedEnergy recoveryEquilibriumMeasure ≤ recoveryWeightedEnergy ν := by
  set μ := recoveryEquilibriumMeasure with hμdef
  set A := frullaniEnergy μ μ with hA
  set qμ := ∫⁻ x, recoveryField x ∂μ with hqμ
  set B := frullaniEnergy ν ν with hB
  set qν := ∫⁻ x, recoveryField x ∂ν with hqν
  set M := frullaniEnergy ν μ with hM
  set c := ENNReal.ofReal recoveryEquilibriumConstant with hc
  have hAq : A + qμ = c := frullaniEnergy_recovery_add_field
  have hMq : c ≤ M + qν := by
    rw [hM, frullaniEnergy]
    change c ≤ ∫⁻ x, recoveryKernelPotential x ∂ν + qν
    rw [← lintegral_add_left measurable_recoveryKernelPotential]
    calc c = ∫⁻ _x, c ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, recoveryKernelPotential x + recoveryField x ∂ν :=
        lintegral_mono_ae (hν.mono fun x hx => recoveryEquilibriumConstant_le hx)
  have hpd : 2 * M ≤ B + A := two_mul_frullaniEnergy_le hν ae_recoveryEquilibriumMeasure_abs_le_one
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAq ▸ le_self_add)
  rw [recoveryWeightedEnergy, recoveryWeightedEnergy]
  refine ENNReal.le_of_add_le_add_right hAtop ?_
  calc A + 2 * qμ + A = 2 * (A + qμ) := by ring
    _ = 2 * c := by rw [hAq]
    _ ≤ 2 * (M + qν) := by gcongr
    _ = 2 * M + 2 * qν := by ring
    _ ≤ B + A + 2 * qν := by gcongr
    _ = B + 2 * qν + A := by ring

theorem recoveryWeightedEnergy_lt_top :
    recoveryWeightedEnergy recoveryEquilibriumMeasure < ⊤ := by
  have hAq := frullaniEnergy_recovery_add_field
  rw [recoveryWeightedEnergy, two_mul, ← add_assoc, hAq]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
  exact lt_of_le_of_lt (hAq ▸ le_add_self) ENNReal.ofReal_lt_top

/-- **Uniqueness of the minimizer**: a probability measure `ν` on `[-1, 1]` with
`I_Q(ν) ≤ I_Q(μ)` is `μ`. -/
theorem eq_recoveryEquilibriumMeasure_of_weightedEnergy_le (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, |x| ≤ 1)
    (hle : recoveryWeightedEnergy ν ≤ recoveryWeightedEnergy recoveryEquilibriumMeasure) :
    ν = recoveryEquilibriumMeasure := by
  set μ := recoveryEquilibriumMeasure with hμdef
  set A := frullaniEnergy μ μ with hA
  set qμ := ∫⁻ x, recoveryField x ∂μ with hqμ
  set B := frullaniEnergy ν ν with hB
  set qν := ∫⁻ x, recoveryField x ∂ν with hqν
  set M := frullaniEnergy ν μ with hM
  set c := ENNReal.ofReal recoveryEquilibriumConstant with hc
  have hAq : A + qμ = c := frullaniEnergy_recovery_add_field
  have hMq : c ≤ M + qν := by
    rw [hM, frullaniEnergy]
    change c ≤ ∫⁻ x, recoveryKernelPotential x ∂ν + qν
    rw [← lintegral_add_left measurable_recoveryKernelPotential]
    calc c = ∫⁻ _x, c ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ x, recoveryKernelPotential x + recoveryField x ∂ν :=
        lintegral_mono_ae (hν.mono fun x hx => recoveryEquilibriumConstant_le hx)
  have hμfin : A + 2 * qμ ≠ ⊤ := (recoveryWeightedEnergy_lt_top).ne
  rw [recoveryWeightedEnergy, recoveryWeightedEnergy] at hle
  have hνfin : B + 2 * qν ≠ ⊤ := ne_top_of_le_ne_top hμfin hle
  have hqνfin : 2 * qν ≠ ⊤ := ne_top_of_le_ne_top hνfin le_add_self
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top hμfin le_self_add
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top hνfin le_self_add
  -- `E(ν,ν) + E(μ,μ) ≤ 2 E(ν,μ)`
  have hBA : B + A ≤ 2 * M := by
    refine (ENNReal.add_le_add_iff_right hqνfin).mp ?_
    calc B + A + 2 * qν = (B + 2 * qν) + A := by ring
      _ ≤ (A + 2 * qμ) + A := by gcongr
      _ = 2 * (A + qμ) := by ring
      _ = 2 * c := by rw [hAq]
      _ ≤ 2 * (M + qν) := by gcongr
      _ = 2 * M + 2 * qν := by ring
  obtain ⟨s, hs, hmom⟩ := exists_gaussianMoment_eq_of_energy_le hν
    ae_recoveryEquilibriumMeasure_abs_le_one (ENNReal.add_ne_top.mpr ⟨hBtop, hAtop⟩) hBA
  exact eq_of_gaussianMoment_eq hs.le hν ae_recoveryEquilibriumMeasure_abs_le_one hmom

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
