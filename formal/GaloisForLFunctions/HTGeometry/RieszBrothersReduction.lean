import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Exact measure-theoretic reduction of the Riesz-brothers graph input

This module separates the genuinely classical Fourier theorem from the measure-theoretic
conclusion used by the cofinal Cholesky paper.  If the complex density measure `y · μ` is forced
to be absolutely continuous with respect to a reference circle measure whenever its analytic
Fourier half-line is square summable, then mutual singularity of `μ` and the reference measure
forces `y = 0`.  Thus the sole remaining analytic theorem is an absolute-continuity statement for
complex measures; no graph or operator closure is hidden in the interface.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Normalized Lebesgue (Haar probability) measure on the multiplicative unit circle, transported
from the unit additive circle. -/
noncomputable def circleLebesgue : Measure Circle :=
  Measure.map (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
    AddCircle.haarAddCircle

noncomputable instance : IsProbabilityMeasure circleLebesgue :=
  Measure.isProbabilityMeasure_map
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vector measure obtained by integrating a Bochner-integrable density is absolutely
continuous with respect to its underlying positive measure. -/
theorem withDensityV_absolutelyContinuous_toENNReal
    (mu : Measure X) (f : X → E) (hf : Integrable f mu) :
    mu.withDensityᵥ f ≪ᵥ mu.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  rw [withDensityᵥ_apply hf hs, Measure.restrict_zero_set hzero, integral_zero_measure]

omit [NormedSpace ℝ E] in
/-- A vector measure absolutely continuous with respect to two mutually singular positive
measures is zero. -/
theorem vectorMeasure_eq_zero_of_ac_of_mutuallySingular
    (mu nu : Measure X) (v : VectorMeasure X E) (hmunu : mu ⟂ₘ nu)
    (hvmu : v ≪ᵥ mu.toENNRealVectorMeasure)
    (hvnu : v ≪ᵥ nu.toENNRealVectorMeasure) :
    v = 0 := by
  apply VectorMeasure.ext
  intro s hs
  let t := hmunu.nullSet
  have ht : MeasurableSet t := hmunu.measurableSet_nullSet
  have hleft : v (s ∩ t) = 0 := by
    apply hvmu
    rw [Measure.toENNRealVectorMeasure_apply_measurable (hs.inter ht)]
    exact measure_mono_null Set.inter_subset_right hmunu.measure_nullSet
  have hright : v (s ∩ tᶜ) = 0 := by
    apply hvnu
    rw [Measure.toENNRealVectorMeasure_apply_measurable (hs.inter ht.compl)]
    exact measure_mono_null Set.inter_subset_right hmunu.measure_compl_nullSet
  have hsplit : s = (s ∩ t) ∪ (s ∩ tᶜ) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  rw [hsplit, VectorMeasure.of_union]
  · rw [hleft, hright, zero_add, _root_.zero_apply]
  · exact Set.disjoint_left.2 (fun x hx hy => hy.2 hx.2)
  · exact hs.inter ht
  · exact hs.inter ht.compl

/-- The exact Riesz-brothers absolute-continuity assertion needed for a fixed pair `(μ,m)`:
square summability of the analytic monomial coefficients of `y ∈ L²(μ)` makes the complex
density measure `y · μ` absolutely continuous with respect to `m`. -/
def HasRieszBrothersDensityConclusion
    (mu m : Measure Circle) [IsFiniteMeasure mu] : Prop :=
  ∀ y : Lp ℂ 2 mu,
    Memℓp (fun n : ℕ => inner ℂ (circleMonomialLp mu n) y) 2 →
      mu.withDensityᵥ (⇑y) ≪ᵥ m.toENNRealVectorMeasure

/-- For a measure singular to `m`, the Riesz-brothers density conclusion implies the exact
one-sided Fourier rigidity property used by polynomial graph saturation. -/
theorem oneSidedFourierRigid_of_mutuallySingular_of_rieszBrothers
    (mu m : Measure Circle) [IsFiniteMeasure mu]
    (hmut : mu ⟂ₘ m) (hriesz : HasRieszBrothersDensityConclusion mu m) :
    IsOneSidedFourierRigid mu := by
  intro y hy
  have hyint : Integrable (⇑y) mu := (Lp.memLp y).integrable (by norm_num)
  have hvmu : mu.withDensityᵥ (⇑y) ≪ᵥ mu.toENNRealVectorMeasure :=
    withDensityV_absolutelyContinuous_toENNReal mu (⇑y) hyint
  have hvzero : mu.withDensityᵥ (⇑y) = 0 :=
    vectorMeasure_eq_zero_of_ac_of_mutuallySingular mu m _ hmut hvmu (hriesz y hy)
  have hae : (⇑y) =ᵐ[mu] (0 : Circle → ℂ) :=
    hyint.ae_eq_of_withDensityᵥ_eq (integrable_zero Circle ℂ mu) (by
      simpa only [withDensityᵥ_zero] using hvzero)
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℂ 2 mu).symm

/-- Pure-singular graph saturation follows mechanically once the classical Riesz-brothers
absolute-continuity theorem is supplied at the density-measure interface. -/
theorem polynomialGraph_closure_eq_top_of_mutuallySingular_of_rieszBrothers
    (mu m : Measure Circle) [IsFiniteMeasure mu]
    (hmut : mu ⟂ₘ m) (hriesz : HasRieszBrothersDensityConclusion mu m) :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
      ⊤ :=
  polynomialGraph_closure_eq_top_of_oneSidedFourierRigid mu
    (oneSidedFourierRigid_of_mutuallySingular_of_rieszBrothers mu m hmut hriesz)

/-- Paper-facing pure-singular specialization with normalized circle Lebesgue measure. -/
theorem polynomialGraph_closure_eq_top_of_pureSingular_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
      ⊤ :=
  polynomialGraph_closure_eq_top_of_mutuallySingular_of_rieszBrothers
    mu circleLebesgue hsing hriesz

end

end GaloisForLFunctions.HTGeometry
