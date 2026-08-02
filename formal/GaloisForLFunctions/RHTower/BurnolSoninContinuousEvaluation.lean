import GaloisForLFunctions.RHTower.BurnolSoninRieszVector
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Continuous completed-Mellin evaluation on Burnol's extended Sonine space

For `1/2 < Re w < 1`, constant aperture head and `L²` tail make the concrete completed Mellin
integral absolutely convergent.  Its integral is proved linear on the actual extended Sonine
subspace, the sharp aperture estimate makes that linear map continuous, and Fréchet–Riesz supplies
its canonical evaluation vector.  No evaluator or continuity hypothesis is postulated.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem integrableOn_extendedSonin_mul_mellinKernel
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a : ℝ} (ha : 0 < a) (f : soninExtendedSpace a) :
    IntegrableOn
      (fun t : ℝ => ((f : evenSubspace) : SoninL2) t * soninMellinKernel w t)
      (Ioi (0 : ℝ)) := by
  obtain ⟨c, hc⟩ := (mem_soninExtendedSpace.mp f.property).1
  rw [← Ioc_union_Ioi_eq_Ioi ha.le]
  apply IntegrableOn.union
  · exact integrableOn_head_mul_kernel hhi ha hc
  · exact integrableOn_tail_mul_kernel hlo ha
      (memLp_restrict_Ioi ((f : evenSubspace) : SoninL2))

theorem soninMellinEvaluation_add_extendedSonin
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a : ℝ} (ha : 0 < a) (f g : soninExtendedSpace a) :
    soninMellinEvaluation w (((f + g : soninExtendedSpace a) : evenSubspace) : SoninL2) =
      soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) +
        soninMellinEvaluation w (((g : soninExtendedSpace a) : evenSubspace) : SoninL2) := by
  have hfg :
      (((((f + g : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
        (((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)) +
          (((((g : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)) := by
    simpa using Lp.coeFn_add
      (((f : soninExtendedSpace a) : evenSubspace) : SoninL2)
      (((g : soninExtendedSpace a) : evenSubspace) : SoninL2)
  unfold soninMellinEvaluation
  rw [← mul_add, ← integral_add
    (integrableOn_extendedSonin_mul_mellinKernel hlo hhi ha f)
    (integrableOn_extendedSonin_mul_mellinKernel hlo hhi ha g)]
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [hfg] with t ht
  intro _
  rw [ht, Pi.add_apply]
  ring

theorem soninMellinEvaluation_smul_extendedSonin
    {w : ℂ} {a : ℝ} (c : ℂ) (f : soninExtendedSpace a) :
    soninMellinEvaluation w (((c • f : soninExtendedSpace a) : evenSubspace) : SoninL2) =
      c * soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) := by
  have hcf :
      (((((c • f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
        c • (((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)) := by
    simpa using Lp.coeFn_smul c
      (((f : soninExtendedSpace a) : evenSubspace) : SoninL2)
  unfold soninMellinEvaluation
  have hInt :
      (∫ t in Ioi (0 : ℝ),
          ((((c • f : soninExtendedSpace a) : evenSubspace) : SoninL2) t) *
            soninMellinKernel w t) =
        c * ∫ t in Ioi (0 : ℝ),
          ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) t) *
            soninMellinKernel w t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [hcf] with t ht
    intro _
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hInt]
  ring

/-- Completed Mellin evaluation as a linear functional on the actual extended Sonine space. -/
def burnolExtendedSoninEvaluationLinearMap
    (w : ℂ) (a : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (ha : 0 < a) :
    soninExtendedSpace a →ₗ[ℂ] ℂ where
  toFun f := soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2)
  map_add' := soninMellinEvaluation_add_extendedSonin hlo hhi ha
  map_smul' c f := by
    rw [soninMellinEvaluation_smul_extendedSonin]
    exact (smul_eq_mul c _).symm

/-- Exact operator bound inherited from the head/tail aperture split. -/
def burnolExtendedSoninEvaluationBound (w : ℂ) (a : ℝ) : ℝ :=
  soninApertureConstant w * a ^ (1 / 2 - w.re) / Real.sqrt 2

theorem norm_burnolExtendedSoninEvaluationLinearMap_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a : ℝ} (ha : 0 < a) (f : soninExtendedSpace a) :
    ‖burnolExtendedSoninEvaluationLinearMap w a hlo hhi ha f‖ ≤
      burnolExtendedSoninEvaluationBound w a * ‖f‖ := by
  have h := norm_soninMellinEvaluation_le_aperture_even hlo hhi ha
    (((f : soninExtendedSpace a) : evenSubspace).property)
    (mem_soninExtendedSpace.mp f.property).1
  have hnorm :
      ‖(((f : soninExtendedSpace a) : evenSubspace) : SoninL2)‖ = ‖f‖ := rfl
  rw [burnolExtendedSoninEvaluationLinearMap, burnolExtendedSoninEvaluationBound]
  calc
    ‖soninMellinEvaluation w
        ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ)‖ ≤
        soninApertureConstant w * a ^ (1 / 2 - w.re) *
          (‖(((f : soninExtendedSpace a) : evenSubspace) : SoninL2)‖ /
            Real.sqrt 2) := h
    _ = (soninApertureConstant w * a ^ (1 / 2 - w.re) / Real.sqrt 2) * ‖f‖ := by
      rw [hnorm]
      ring

/-- Continuous completed-Mellin evaluation on Burnol's extended Sonine Hilbert space. -/
def burnolExtendedSoninEvaluation
    (w : ℂ) (a : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (ha : 0 < a) :
    soninExtendedSpace a →L[ℂ] ℂ :=
  (burnolExtendedSoninEvaluationLinearMap w a hlo hhi ha).mkContinuous
    (burnolExtendedSoninEvaluationBound w a)
    (norm_burnolExtendedSoninEvaluationLinearMap_le hlo hhi ha)

@[simp] theorem burnolExtendedSoninEvaluation_apply
    (w : ℂ) (a : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (ha : 0 < a)
    (f : soninExtendedSpace a) :
    burnolExtendedSoninEvaluation w a hlo hhi ha f =
      soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) :=
  rfl

/-- Canonical Riesz vector for completed Mellin evaluation in the extended Sonine space. -/
def burnolExtendedSoninEvaluationVector
    (w : ℂ) (a : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (ha : 0 < a) :
    soninExtendedSpace a := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact (InnerProductSpace.toDual ℂ (soninExtendedSpace a)).symm
    (burnolExtendedSoninEvaluation w a hlo hhi ha)

theorem inner_burnolExtendedSoninEvaluationVector
    (w : ℂ) (a : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (ha : 0 < a)
    (f : soninExtendedSpace a) :
    ⟪burnolExtendedSoninEvaluationVector w a hlo hhi ha, f⟫_ℂ =
      soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) := by
  letI : Fact (0 < a) := ⟨ha⟩
  rw [burnolExtendedSoninEvaluationVector, InnerProductSpace.toDual_symm_apply]
  rfl

end RHTower
