import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise operator-family isometries on L²
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem aeStronglyMeasurable_operatorFamily_apply
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (f : Lp E 2 μ) :
    AEStronglyMeasurable (fun x => U x ((f : α → E) x)) μ := by
  have hpair := hU.prodMk (Lp.aestronglyMeasurable f)
  exact (show Continuous (fun p : (E →L[𝕜] E) × E => p.1 p.2) by fun_prop).comp_aestronglyMeasurable
    hpair

theorem memLp_operatorFamily_apply
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (hnorm : ∀ x y, ‖U x y‖ = ‖y‖) (f : Lp E 2 μ) :
    MemLp (fun x => U x ((f : α → E) x)) 2 μ :=
  (Lp.memLp f).congr_norm (aeStronglyMeasurable_operatorFamily_apply hU f)
    (Filter.Eventually.of_forall fun x => (hnorm x _).symm)

def lpOperatorFamilyLM
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (hnorm : ∀ x y, ‖U x y‖ = ‖y‖) :
    Lp E 2 μ →ₗ[𝕜] Lp E 2 μ where
  toFun f := (memLp_operatorFamily_apply hU hnorm f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm (f + g)),
      Lp.coeFn_add ((memLp_operatorFamily_apply hU hnorm f).toLp _)
        ((memLp_operatorFamily_apply hU hnorm g).toLp _),
      MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm f),
      MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm (c • f)),
      Lp.coeFn_smul c ((memLp_operatorFamily_apply hU hnorm f).toLp _),
      MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm f),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, map_smul]

theorem norm_lpOperatorFamilyLM
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (hnorm : ∀ x y, ‖U x y‖ = ‖y‖) (f : Lp E 2 μ) :
    ‖lpOperatorFamilyLM hU hnorm f‖ = ‖f‖ := by
  change ‖(memLp_operatorFamily_apply hU hnorm f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => hnorm x _)]

def lpOperatorFamilyIsometry
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (hnorm : ∀ x y, ‖U x y‖ = ‖y‖) :
    Lp E 2 μ →ₗᵢ[𝕜] Lp E 2 μ :=
  LinearIsometry.mk (lpOperatorFamilyLM hU hnorm) (norm_lpOperatorFamilyLM hU hnorm)

theorem lpOperatorFamilyIsometry_coeFn
    {U : α → E →L[𝕜] E} (hU : AEStronglyMeasurable U μ)
    (hnorm : ∀ x y, ‖U x y‖ = ‖y‖) (f : Lp E 2 μ) :
    ((lpOperatorFamilyIsometry hU hnorm f : Lp E 2 μ) : α → E) =ᵐ[μ]
      fun x => U x ((f : α → E) x) :=
  MemLp.coeFn_toLp (memLp_operatorFamily_apply hU hnorm f)

theorem lpOperatorFamilyIsometry_surjective
    {U W : α → E →L[𝕜] E}
    (hU : AEStronglyMeasurable U μ) (hW : AEStronglyMeasurable W μ)
    (hnormU : ∀ x y, ‖U x y‖ = ‖y‖) (hnormW : ∀ x y, ‖W x y‖ = ‖y‖)
    (hleft : ∀ x y, U x (W x y) = y) :
    Function.Surjective (lpOperatorFamilyIsometry hU hnormU) := by
  intro f
  let g : Lp E 2 μ := lpOperatorFamilyIsometry hW hnormW f
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [lpOperatorFamilyIsometry_coeFn hU hnormU g,
    lpOperatorFamilyIsometry_coeFn hW hnormW f] with x hUg hWf
  rw [hUg, hWf, hleft]

noncomputable def lpOperatorFamilyIsometryEquiv
    {U W : α → E →L[𝕜] E}
    (hU : AEStronglyMeasurable U μ) (hW : AEStronglyMeasurable W μ)
    (hnormU : ∀ x y, ‖U x y‖ = ‖y‖) (hnormW : ∀ x y, ‖W x y‖ = ‖y‖)
    (hleft : ∀ x y, U x (W x y) = y) :
    Lp E 2 μ ≃ₗᵢ[𝕜] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (lpOperatorFamilyIsometry hU hnormU)
    (lpOperatorFamilyIsometry_surjective hU hW hnormU hnormW hleft)

@[simp]
theorem lpOperatorFamilyIsometryEquiv_apply
    {U W : α → E →L[𝕜] E}
    (hU : AEStronglyMeasurable U μ) (hW : AEStronglyMeasurable W μ)
    (hnormU : ∀ x y, ‖U x y‖ = ‖y‖) (hnormW : ∀ x y, ‖W x y‖ = ‖y‖)
    (hleft : ∀ x y, U x (W x y) = y) (f : Lp E 2 μ) :
    lpOperatorFamilyIsometryEquiv hU hW hnormU hnormW hleft f =
      lpOperatorFamilyIsometry hU hnormU f := rfl

end GaloisForLFunctions.HTGeometry
