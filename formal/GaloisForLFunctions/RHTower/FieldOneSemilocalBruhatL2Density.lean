import GaloisForLFunctions.RHTower.L2SeparatedProductDensity
import GaloisForLFunctions.RHTower.FieldOneFiniteBruhatL2Density
import GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatHilbertCompletion
import GaloisForLFunctions.RHTower.FieldOneSemilocalFullFaithfulness

/-!
# Semilocal Bruhat density and full `L²` completion

Finite-adele sigma-finiteness identifies the swap-transported semilocal Haar measure with
the direct product of real and finite-adele Haar measures.  Density of real Schwartz functions,
density of finite-adele Bruhat--Schwartz functions, and generic separated-product density then
show that the existing algebraic semilocal Bruhat realization is dense in product-Haar `L²`.
Consequently its abstract Hilbert completion is canonically isometrically equivalent to the full
semilocal `L²` space.

All statements are unconditional and contain no trace formula, Hodge package, positivity premise,
spectral assertion, or Riemann-hypothesis premise.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped TensorProduct

theorem fieldOneSemilocalAddHaar_eq_prod :
    fieldOneSemilocalAddHaar =
      (volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar := by
  exact Measure.prod_swap


def fieldOneArchimedeanSchwartzToL2 :
    FieldOneArchimedeanSchwartz →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem fieldOneArchimedeanSchwartzToL2_denseRange :
    DenseRange fieldOneArchimedeanSchwartzToL2 := by
  change
    DenseRange
      (fun f : FieldOneArchimedeanSchwartz =>
        f.toLp 2 (volume : Measure ℝ))
  simpa only [SchwartzMap.toLpCLM_apply] using!
    (SchwartzMap.denseRange_toLpCLM
      (F := ℂ) (E := ℝ) (p := 2) ENNReal.ofNat_ne_top)

def fieldOneSemilocalProductBruhatToL2 :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar) :=
  denseFactorTensorToProduct
    fieldOneArchimedeanSchwartzToL2
    fieldOneFiniteBruhatToL2Linear

theorem fieldOneSemilocalProductBruhatToL2_denseRange :
    DenseRange fieldOneSemilocalProductBruhatToL2 := by
  exact denseFactorTensorToProduct_denseRange
    fieldOneArchimedeanSchwartzToL2
    fieldOneFiniteBruhatToL2Linear
    fieldOneArchimedeanSchwartzToL2_denseRange
    fieldOneFiniteBruhatToL2Linear_denseRange

def fieldOneSemilocalProductToExistingL2 :
    Lp ℂ 2 ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar) →ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  Lp.compMeasurePreservingₗᵢ ℂ id
    { measurable := measurable_id
      map_eq := by
        simpa using fieldOneSemilocalAddHaar_eq_prod }

theorem fieldOneSemilocalProductToExistingL2_surjective :
    Function.Surjective fieldOneSemilocalProductToExistingL2 := by
  intro y
  let R :
      Lp ℂ 2 fieldOneSemilocalAddHaar →ₗᵢ[ℂ]
        Lp ℂ 2 ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar) :=
    Lp.compMeasurePreservingₗᵢ ℂ id
      { measurable := measurable_id
        map_eq := by
          simpa using fieldOneSemilocalAddHaar_eq_prod.symm }
  refine ⟨R y, ?_⟩
  have hright :
      R y =ᵐ[fieldOneSemilocalAddHaar] y := by
    rw [congrArg ae fieldOneSemilocalAddHaar_eq_prod]
    simpa only [R, Function.comp_apply, id_eq] using!
      Lp.coeFn_compMeasurePreserving y
        ({ measurable := measurable_id
           map_eq := by
             simpa using fieldOneSemilocalAddHaar_eq_prod.symm } :
          MeasurePreserving id
            ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar)
            fieldOneSemilocalAddHaar)
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (R y)
      ({ measurable := measurable_id
         map_eq := by
           simpa using fieldOneSemilocalAddHaar_eq_prod } :
        MeasurePreserving id fieldOneSemilocalAddHaar
          ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar)),
    hright]
      with x hleft hright
  simpa only [fieldOneSemilocalProductToExistingL2, R,
    Function.comp_apply, id_eq] using! hleft.trans hright

def fieldOneSemilocalTransportedBruhatToL2 :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  fieldOneSemilocalProductToExistingL2.toLinearMap.comp
    fieldOneSemilocalProductBruhatToL2

theorem fieldOneSemilocalTransportedBruhatToL2_denseRange :
    DenseRange fieldOneSemilocalTransportedBruhatToL2 := by
  have h :=
    (fieldOneSemilocalProductToExistingL2_surjective.denseRange.comp
      fieldOneSemilocalProductBruhatToL2_denseRange
      fieldOneSemilocalProductToExistingL2.continuous)
  simpa only [fieldOneSemilocalTransportedBruhatToL2,
    LinearMap.coe_comp, LinearIsometry.coe_toLinearMap,
    Function.comp_def] using h

theorem fieldOneSemilocalBruhatToL2_eq_transported :
    fieldOneSemilocalBruhatToL2 =
      fieldOneSemilocalTransportedBruhatToL2 := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      have hsep :
          l2SeparatedProduct
              (fieldOneArchimedeanSchwartzToL2 f)
              (fieldOneFiniteBruhatToL2Linear g)
            =ᵐ[fieldOneSemilocalAddHaar]
          l2SeparatedFun
              (fieldOneArchimedeanSchwartzToL2 f)
              (fieldOneFiniteBruhatToL2Linear g) := by
        rw [fieldOneSemilocalAddHaar_eq_prod]
        exact l2SeparatedProduct_ae
          (fieldOneArchimedeanSchwartzToL2 f)
          (fieldOneFiniteBruhatToL2Linear g)
      have hf :
          (fun x : ℝ × FieldOneFiniteAdele =>
              fieldOneArchimedeanSchwartzToL2 f x.1)
            =ᵐ[fieldOneSemilocalAddHaar]
          fun x => f x.1 := by
        rw [fieldOneSemilocalAddHaar_eq_prod]
        exact
          Measure.quasiMeasurePreserving_fst.ae_eq_comp
            (f.coeFn_toLp (p := 2) (μ := volume))
      have hg :
          (fun x : ℝ × FieldOneFiniteAdele =>
              fieldOneFiniteBruhatToL2Linear g x.2)
            =ᵐ[fieldOneSemilocalAddHaar]
          fun x => g.1 x.2 := by
        rw [fieldOneSemilocalAddHaar_eq_prod]
        exact
          Measure.quasiMeasurePreserving_snd.ae_eq_comp
            (fieldOneFiniteBruhatToL2_ae g)
      apply Lp.ext
      filter_upwards [
        fieldOneSemilocalPureTensorToL2_ae f g,
        Lp.coeFn_compMeasurePreserving
          (fieldOneSemilocalProductBruhatToL2 (f ⊗ₜ[ℂ] g))
          ({ measurable := measurable_id
             map_eq := by
               simpa using fieldOneSemilocalAddHaar_eq_prod } :
            MeasurePreserving id fieldOneSemilocalAddHaar
              ((volume : Measure ℝ).prod fieldOneFiniteAdeleAddHaar)),
        hsep, hf, hg]
          with x hexisting htransport hsep hf hg
      rw [fieldOneSemilocalBruhatToL2_tmul]
      rw [hexisting]
      rw [show
        fieldOneSemilocalTransportedBruhatToL2
            (f ⊗ₜ[ℂ] g) x =
          fieldOneSemilocalProductBruhatToL2
            (f ⊗ₜ[ℂ] g) x by
        simpa only [fieldOneSemilocalTransportedBruhatToL2,
          LinearMap.comp_apply,
          fieldOneSemilocalProductToExistingL2,
          LinearIsometry.coe_toLinearMap,
          Function.comp_apply, id_eq] using! htransport]
      rw [show
        fieldOneSemilocalProductBruhatToL2
            (f ⊗ₜ[ℂ] g) x =
          l2SeparatedFun
            (fieldOneArchimedeanSchwartzToL2 f)
            (fieldOneFiniteBruhatToL2Linear g) x by
        rw [fieldOneSemilocalProductBruhatToL2,
          denseFactorTensorToProduct_tmul]
        exact hsep]
      simp only [fieldOneSemilocalPureTensorFun,
        l2SeparatedFun]
      rw [hf, hg]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

theorem fieldOneSemilocalBruhatToL2_denseRange :
    DenseRange fieldOneSemilocalBruhatToL2 := by
  rw [fieldOneSemilocalBruhatToL2_eq_transported]
  exact fieldOneSemilocalTransportedBruhatToL2_denseRange

theorem fieldOneSemilocalBruhatL2ClosedImage_eq_top :
    fieldOneSemilocalBruhatL2ClosedImage = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  simpa only [fieldOneSemilocalBruhatL2ClosedImage,
    fieldOneSemilocalBruhatL2Range, DenseRange] using!
    fieldOneSemilocalBruhatToL2_denseRange

theorem fieldOneSemilocalBruhatCompletionToL2_surjective :
    Function.Surjective fieldOneSemilocalBruhatCompletionToL2 := by
  change
    Function.Surjective
      fieldOneSemilocalBruhatCompletionToL2.toLinearMap
  rw [← LinearMap.range_eq_top]
  rw [fieldOneSemilocalBruhatCompletionToL2_range]
  exact fieldOneSemilocalBruhatL2ClosedImage_eq_top

def fieldOneSemilocalBruhatCompletionEquivL2 :
    FieldOneSemilocalBruhatHilbertCompletion ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneSemilocalAddHaar :=
  LinearIsometryEquiv.ofSurjective
    fieldOneSemilocalBruhatCompletionToL2
    fieldOneSemilocalBruhatCompletionToL2_surjective

@[simp]
theorem fieldOneSemilocalBruhatCompletionEquivL2_coe
    (t : FieldOneSemilocalBruhatSchwartz) :
    fieldOneSemilocalBruhatCompletionEquivL2
        (t : FieldOneSemilocalBruhatHilbertCompletion) =
      fieldOneSemilocalBruhatToL2 t := by
  rw [fieldOneSemilocalBruhatCompletionEquivL2,
    LinearIsometryEquiv.coe_ofSurjective]
  exact fieldOneSemilocalBruhatCompletionToL2_coe t

/-- The completed semilocal Weyl representation remains faithful. -/
theorem fieldOneSemilocalBruhatCompletionWeylUnitary_injective :
    Function.Injective fieldOneSemilocalBruhatCompletionWeylUnitary := by
  intro a b hab
  apply fieldOneSemilocalBruhatWeylMultiplier_injective
  apply LinearMap.ext
  intro t
  apply UniformSpace.Completion.coe_injective
  have h :=
    congrFun
      (congrArg
        (fun U :
            FieldOneSemilocalBruhatHilbertCompletion ≃ₗᵢ[ℂ]
              FieldOneSemilocalBruhatHilbertCompletion =>
          (U : FieldOneSemilocalBruhatHilbertCompletion →
            FieldOneSemilocalBruhatHilbertCompletion))
        hab)
      (t : FieldOneSemilocalBruhatHilbertCompletion)
  simpa only [
    fieldOneSemilocalBruhatCompletionWeylUnitary_coe] using h

/-- The ambient product-Haar `L²` Weyl representation is faithful. -/
theorem fieldOneSemilocalL2WeylUnitary_injective :
    Function.Injective fieldOneSemilocalL2WeylUnitary := by
  intro a b hab
  apply fieldOneSemilocalBruhatCompletionWeylUnitary_injective
  apply LinearIsometryEquiv.ext
  intro x
  apply fieldOneSemilocalBruhatCompletionToL2.injective
  rw [← fieldOneSemilocalBruhatCompletionToL2_weyl,
    ← fieldOneSemilocalBruhatCompletionToL2_weyl]
  exact
    congrFun
      (congrArg
        (fun U :
            Lp ℂ 2 fieldOneSemilocalAddHaar ≃ₗᵢ[ℂ]
              Lp ℂ 2 fieldOneSemilocalAddHaar =>
          (U : Lp ℂ 2 fieldOneSemilocalAddHaar →
            Lp ℂ 2 fieldOneSemilocalAddHaar))
        hab)
      (fieldOneSemilocalBruhatCompletionToL2 x)

end

end GaloisForLFunctions.RHTower
