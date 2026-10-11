import GaloisForLFunctions.HTGeometry.PaperModulationCalkin
import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication
import GaloisForLFunctions.HTGeometry.ResolventCompactness

/-!
# Actual maximal-multiplication resolvents in the compact quotient

The native self-adjoint resolvent is pointwise inverse multiplication. This identifies the
actual operator, including its maximal domain, with an element of the modulation commutant.
Consequently every resolvent norm and pairwise distance survives quotienting by compacts.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open MeasureTheory
open scoped ENNReal LinearPMap

/-- A real energy never meets a nonreal resolvent parameter. -/
theorem realEnergy_sub_nonreal_ne_zero (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (r : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im (sub_eq_zero.mp h)
  exact hz (by simpa using hi.symm)

/-- The inverse symbol has the standard nonreal resolvent bound. -/
theorem norm_realEnergy_resolventSymbol_le (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖((r : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  apply (inv_le_inv₀ (norm_pos_iff.mpr (realEnergy_sub_nonreal_ne_zero r hz))
    (abs_pos.mpr hz)).mpr
  simpa using Complex.abs_im_le_norm ((r : ℂ) - z)

/-- The resolvent already constructed from self-adjointness acts by the inverse symbol. -/
theorem maximalRealL2Mul_resolvent_apply_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {energy : α → ℝ} (henergy : Measurable energy)
    {z : ℂ} (hz : z.im ≠ 0) (f : Lp ℂ 2 μ) :
    (resolventCLM (maximalRealL2Mul_isSelfAdjoint μ henergy) hz f : α → ℂ) =ᵐ[μ]
      fun x => ((energy x : ℂ) - z)⁻¹ * f x := by
  let hA := maximalRealL2Mul_isSelfAdjoint μ henergy
  let u := resolventLinear hA hz f
  let v : (maximalRealL2Mul μ energy).domain := ⟨u, resolventLinear_mem hA hz f⟩
  have heq : maximalRealL2Mul μ energy v - z • u = f :=
    shiftedMap_resolventLinear hA hz f
  have hs := Lp.coeFn_sub (maximalRealL2Mul μ energy v) (z • u)
  rw [heq] at hs
  filter_upwards [hs, maximalRealL2Mul_apply_ae μ energy v, Lp.coeFn_smul z u]
    with x hx hmul hsmul
  change u x = _
  have hx' : ((energy x : ℂ) - z) * u x = f x := by
    simpa only [Pi.sub_apply, hmul, hsmul, Pi.smul_apply, smul_eq_mul, sub_mul] using hx.symm
  calc
    u x = ((energy x : ℂ) - z)⁻¹ * (((energy x : ℂ) - z) * u x) := by
      rw [← mul_assoc, inv_mul_cancel₀ (realEnergy_sub_nonreal_ne_zero (energy x) hz), one_mul]
    _ = ((energy x : ℂ) - z)⁻¹ * f x := by rw [hx']

/-- The abstract native resolvent equals the standard bounded multiplier, with no domain change. -/
theorem maximalRealL2Mul_resolvent_eq_multiplier {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {energy : α → ℝ} (henergy : Measurable energy)
    {z : ℂ} (hz : z.im ≠ 0) :
    resolventCLM (maximalRealL2Mul_isSelfAdjoint μ henergy) hz =
      lpBoundedMulCLM (p := 2) (μ := μ)
        (((Complex.measurable_ofReal.comp henergy).sub measurable_const).inv)
        (inv_nonneg.mpr (abs_nonneg z.im))
        (fun x => norm_realEnergy_resolventSymbol_le (energy x) hz) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (maximalRealL2Mul_resolvent_apply_ae μ henergy hz f).trans
    (lpBoundedMulCLM_coeFn _ _ _ f).symm

/-- The actual maximal-domain resolvent belongs to the full modulation commutant. -/
theorem maximalRealL2Mul_resolvent_mem_commutant
    {energy : ℝ → ℝ} (henergy : Measurable energy) {z : ℂ} (hz : z.im ≠ 0) :
    resolventCLM (maximalRealL2Mul_isSelfAdjoint volume henergy) hz ∈
      paperModulationCommutant :=
  mem_paperModulationCommutant_of_mul _ _
    (maximalRealL2Mul_resolvent_apply_ae volume henergy hz)

/-- No compact perturbation reduces a maximal-multiplication resolvent's norm. -/
theorem maximalRealL2Mul_resolvent_compactIdealDistance
    {energy : ℝ → ℝ} (henergy : Measurable energy) {z : ℂ} (hz : z.im ≠ 0) :
    compactIdealDistance (resolventCLM (maximalRealL2Mul_isSelfAdjoint volume henergy) hz) =
      ‖resolventCLM (maximalRealL2Mul_isSelfAdjoint volume henergy) hz‖ :=
  paperModulationCommutant_compactIdealDistance
    ⟨_, maximalRealL2Mul_resolvent_mem_commutant henergy hz⟩

/-- Two arbitrary real-energy resolvents retain their entire distance modulo compacts. -/
theorem maximalRealL2Mul_resolvent_compactIdealDistance_sub
    {energy₁ energy₂ : ℝ → ℝ} (h₁ : Measurable energy₁) (h₂ : Measurable energy₂)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    compactIdealDistance (resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₁) hz -
      resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₂) hw) =
    ‖resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₁) hz -
      resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₂) hw‖ := by
  let A : paperModulationCommutant :=
    ⟨_, maximalRealL2Mul_resolvent_mem_commutant h₁ hz⟩
  let B : paperModulationCommutant :=
    ⟨_, maximalRealL2Mul_resolvent_mem_commutant h₂ hw⟩
  exact paperModulationCommutant_compactIdealDistance (A - B)

/-- Compact equivalence of real-energy resolvents is exact operator equality. -/
theorem maximalRealL2Mul_resolvent_compact_sub_iff_eq
    {energy₁ energy₂ : ℝ → ℝ} (h₁ : Measurable energy₁) (h₂ : Measurable energy₂)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    IsCompactOperator (resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₁) hz -
      resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₂) hw) ↔
    resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₁) hz =
      resolventCLM (maximalRealL2Mul_isSelfAdjoint volume h₂) hw := by
  rw [paperModulationCommutant_compact_sub_iff_eq
    ⟨_, maximalRealL2Mul_resolvent_mem_commutant h₁ hz⟩
    ⟨_, maximalRealL2Mul_resolvent_mem_commutant h₂ hw⟩]
  exact Subtype.ext_iff

end
end GaloisForLFunctions.HTGeometry
