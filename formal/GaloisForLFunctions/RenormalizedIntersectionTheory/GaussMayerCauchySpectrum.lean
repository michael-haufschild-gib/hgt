import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyL2
import GaloisForLFunctions.HTGeometry.CircleSymbolGroupCStar
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.ContinuousMap.Units

/-!
# Spectrum of actual logarithmic Cauchy averaging

The Fourier symbol vanishes at infinity and extends to the Cayley circle.
The faithful circle multiplier representation identifies the operator spectrum
with the Gamma curve together with its limiting value zero.
-/

open Complex Set Filter MeasureTheory FourierTransform
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open GaloisForLFunctions.HTGeometry
open MayerCauchyL2 MayerCauchyMellinSymbol
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySpectrum

private theorem circle_spectrum (U : C(UnitCircle,ℂ)) :
    spectrum ℂ (circleMultiplier U)=Set.range U := by
  let S := circleMultiplierHom.range
  haveI : IsClosed (S : Set (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) := by
    change IsClosed (Set.range circleMultiplier)
    exact isometry_circleMultiplier.isClosedEmbedding.isClosed_range
  have hb : Function.Bijective circleMultiplierHom.rangeRestrict := by
    constructor
    · intro U V h
      exact circleMultiplier_injective (congrArg Subtype.val h)
    · intro T
      obtain ⟨U,hU⟩ := T.property
      exact ⟨U,Subtype.ext hU⟩
  let e := StarAlgEquiv.ofBijective circleMultiplierHom.rangeRestrict hb
  calc
    spectrum ℂ (circleMultiplier U) = spectrum ℂ (e U) :=
      (StarSubalgebra.spectrum_eq S (a := e U)).symm
    _ = spectrum ℂ U := AlgEquiv.spectrum_eq e U
    _ = Set.range U := ContinuousMap.spectrum_eq_range U

/-- The actual Fourier symbol, continuously completed by zero at infinite frequency. -/
def compactSymbol {w : ℂ} (hw : 0 < w.re) : C(UnitCircle,ℂ) :=
  circleOfC0 (𝓕 (logKernel w)) (continuous_fourier_of_integrable' (logKernel_integrable hw))
    (Real.zero_at_infty_fourier _)

/-- The circle representation retains the actual Cauchy operator. -/
theorem operator_eq_circle {w : ℂ} (hw : 0 < w.re) :
    operator hw=circleMultiplier (compactSymbol hw) := by
  rw [operator_eq_multiplier,circleMultiplier]
  apply fourierMulCLM_congr_ae
  exact Eventually.of_forall (fun ξ => (circleOfC0_cayleyCirclePoint _ _ _ ξ).symm)

private theorem compactSymbol_range {w : ℂ} (hw : 0 < w.re) :
    Set.range (compactSymbol hw)=insert 0 (Set.range (𝓕 (logKernel w))) := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    by_cases hp : (p : ℂ)=1
    · left
      have he : p=circleOne := Subtype.ext hp
      rw [he]
      exact circleOfC0_one _ _ _
    · right
      refine ⟨cayleyInv p,?_⟩
      change 𝓕 (logKernel w) (cayleyInv p)=(if (p : ℂ)=1 then 0 else 𝓕 (logKernel w) (cayleyInv p))
      rw [if_neg hp]
  · rintro (rfl|⟨ξ,rfl⟩)
    · exact ⟨circleOne,circleOfC0_one _ _ _⟩
    · exact ⟨cayleyCirclePoint ξ,circleOfC0_cayleyCirclePoint _ _ _ ξ⟩

/-- The exact actual spectrum is the Gamma multiplier curve together with its limiting value zero. -/
theorem operator_spectrum_eq_insert {w : ℂ} (hw : 0 < w.re) :
    spectrum ℂ (operator hw)=insert 0
      (Set.range (fun ξ : ℝ => symbol w (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I))) := by
  rw [operator_eq_circle,circle_spectrum,compactSymbol_range]
  have he : 𝓕 (logKernel w)=(fun ξ : ℝ => symbol w (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I)) :=
    funext (fourier_logKernel_symbol hw)
  rw [he]

/-- Zero is always spectral, even though the Cauchy operator is injective. -/
theorem zero_mem_operator_spectrum {w : ℂ} (hw : 0 < w.re) : 0 ∈ spectrum ℂ (operator hw) := by
  rw [operator_spectrum_eq_insert hw]
  exact Set.mem_insert _ _

/-- The actual Cauchy operator has no bounded two-sided inverse on logarithmic `L²`. -/
theorem operator_not_isUnit {w : ℂ} (hw : 0 < w.re) : ¬ IsUnit (operator hw) := by
  intro h
  exact ((spectrum.zero_notMem_iff ℂ).mpr h) (zero_mem_operator_spectrum hw)

/-- The completed Gamma curve is exactly the closure of its finite-frequency values. -/
theorem operator_spectrum_eq_closure {w : ℂ} (hw : 0 < w.re) :
    spectrum ℂ (operator hw)=closure
      (Set.range (fun ξ : ℝ => symbol w (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I))) := by
  have hdec : Tendsto (𝓕 (logKernel w)) atTop (𝓝 0) :=
    (Real.zero_at_infty_fourier _).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  have hzero : (0 : ℂ) ∈ closure (Set.range (𝓕 (logKernel w))) :=
    mem_closure_of_tendsto hdec (Eventually.of_forall (fun ξ => Set.mem_range_self ξ))
  have hclosed : IsClosed (insert 0 (Set.range (𝓕 (logKernel w)))) := by
    rw [← compactSymbol_range hw]
    exact (isCompact_range (compactSymbol hw).continuous).isClosed
  have he : insert (0 : ℂ) (Set.range (𝓕 (logKernel w)))=closure (Set.range (𝓕 (logKernel w))) := by
    apply le_antisymm
    · exact insert_subset hzero subset_closure
    · exact closure_minimal (subset_insert _ _) hclosed
  rw [operator_eq_circle,circle_spectrum,compactSymbol_range,he]
  congr 1
  congr 1
  exact funext (fourier_logKernel_symbol hw)

#print axioms operator_eq_circle
#print axioms operator_spectrum_eq_insert
#print axioms zero_mem_operator_spectrum
#print axioms operator_not_isUnit
#print axioms operator_spectrum_eq_closure

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchySpectrum
