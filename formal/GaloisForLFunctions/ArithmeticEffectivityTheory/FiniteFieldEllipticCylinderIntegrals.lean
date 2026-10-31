import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCylinderHaar
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalSpectralIntegrals
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact spectral integrals on actual adelic cylinders

Open cylinder assembly transports the local product to restricted ambient
Haar. Finite-product Fubini evaluates the radial kernel, while the compact
integral tail contributes probability one.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory
open HTGeometry.DiscreteValuationHaar HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt
noncomputable section

local instance (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance (v : FinitePlace) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsNontrivial := inferInstance
local instance (v : FinitePlace) : IsTopologicalAddGroup (v.adicCompletionIntegers K) :=
  Topology.IsInducing.subtypeVal.topologicalAddGroup
    (v.adicCompletionIntegers K).subtype.toAddMonoidHom
local instance (S : Finset FinitePlace) : IsTopologicalAddGroup (FiniteCylinderTail S) :=
  Pi.topologicalAddGroup
private abbrev cylinderIntegerAddGroup (v : FinitePlace) :
    AddCommGroup (v.adicCompletionIntegers K) := inferInstance
private abbrev cylinderIntegerAdd (v : FinitePlace) :
    Add (v.adicCompletionIntegers K) := inferInstance
attribute [local instance] cylinderIntegerAddGroup cylinderIntegerAdd

local instance (v : FinitePlace) : SigmaCompactSpace (v.adicCompletion K) := by
  letI := finiteCompletion_secondCountable v
  letI := finiteCompletion_locallyCompact v
  exact sigmaCompactSpace_of_locallyCompact_secondCountable
local instance (v : FinitePlace) : (normalizedHaar (v.adicCompletion K)).IsAddHaarMeasure :=
  normalizedHaar_isAddHaar (v.adicCompletion K)
local instance (v : FinitePlace) : SigmaFinite (normalizedHaar (v.adicCompletion K)) := inferInstance
local instance : MeasurableSpace InfinityCompletion := borel _
local instance : BorelSpace InfinityCompletion := ⟨rfl⟩

/-- The actual adelic cylinder, with unrestricted infinity coordinate. -/
def ellipticAdeleCylinder (S : Finset FinitePlace) : Set Adeles :=
  {a | a.1 ∈ finiteAdeleCylinder S}

theorem ellipticCylinderAssembly_range (S : Finset FinitePlace) :
    Set.range (ellipticCylinderAssembly S) = ellipticAdeleCylinder S := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact (finiteCylinderAssembly S x.1).property
  · intro ha
    refine ⟨((finiteAdeleCylinderEquiv S).symm ⟨a.1, ha⟩, a.2), ?_⟩
    apply Prod.ext
    · exact congrArg (Subtype.val : finiteAdeleCylinder S → FiniteAdeles)
        ((finiteAdeleCylinderEquiv S).apply_symm_apply ⟨a.1, ha⟩)
    · rfl

/-- Cylinder assembly preserves the exact restricted ambient Haar measure. -/
theorem ellipticCylinderAssembly_measurePreserving (S : Finset FinitePlace) :
    MeasurePreserving (ellipticCylinderAssembly S) (ellipticCylinderProductHaar S)
      (adeleHaar.restrict (ellipticAdeleCylinder S)) := by
  refine ⟨(ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding.measurable, ?_⟩
  rw [← ellipticCylinderAmbientHaar_eq_product, ellipticCylinderAmbientHaar,
    (ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding.map_comap,
    ellipticCylinderAssembly_range]

/-- Integration in coordinates is integration over the actual ambient cylinder. -/
theorem integral_ellipticCylinderAssembly (S : Finset FinitePlace) (f : Adeles → ℂ) :
    (∫ x, f (ellipticCylinderAssembly S x) ∂ellipticCylinderProductHaar S) =
      ∫ a in ellipticAdeleCylinder S, f a ∂adeleHaar :=
  (ellipticCylinderAssembly_measurePreserving S).integral_comp
    (ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding f

/-- The finite-field part of the radial spectral kernel. -/
def finiteCylinderSpectralKernel (S : Finset FinitePlace) (s : ℂ)
    (x : FiniteCylinderFields S) : ℂ :=
  ∏ v : S, finiteCompletionSpectralKernel v.1 s (x v)

/-- The finite local spectral product, independent of the compact integral tail. -/
def ellipticCylinderSpectralKernel (S : Finset FinitePlace) (s : ℂ)
    (x : EllipticCylinderCoordinates S) : ℂ :=
  finiteCylinderSpectralKernel S s x.1.1 * infinityCompletionSpectralKernel s x.2

private theorem integral_ignore_probability {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [SigmaFinite μ] [SigmaFinite ν] [IsProbabilityMeasure ν] (f : A → ℂ) :
    (∫ x : A × B, f x.1 ∂μ.prod ν) = ∫ a, f a ∂μ := by
  have h := integral_prod_mul f (fun _ : B => (1 : ℂ)) (μ := μ) (ν := ν)
  simpa only [mul_one, integral_const, probReal_univ, one_smul] using h

private theorem integrable_ignore_probability {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν] (f : A → ℂ) (hf : Integrable f μ) :
    Integrable (fun x : A × B => f x.1) (μ.prod ν) := by
  simpa only [mul_one] using hf.mul_prod (integrable_const (1 : ℂ) (μ := ν))

/-- Every finite-cylinder spectral kernel is absolutely integrable on the local half-plane. -/
theorem ellipticCylinderSpectralKernel_integrable (S : Finset FinitePlace)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (ellipticCylinderSpectralKernel S s) (ellipticCylinderProductHaar S) := by
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  have hf : Integrable (finiteCylinderSpectralKernel S s)
      (Measure.pi fun v : S => normalizedHaar (v.1.adicCompletion K)) :=
    Integrable.fintype_prod_dep (f := fun v : S => finiteCompletionSpectralKernel v.1 s)
      (fun v => finiteCompletionSpectralKernel_integrable v.1 s hs)
  exact (integrable_ignore_probability _ (CompactAbelian.haarProb (FiniteCylinderTail S))
    _ hf).mul_prod (infinityCompletionSpectralKernel_integrable s hs)

/-- The exact finite local factors, including infinity and the probability-one integral tail. -/
theorem integral_ellipticCylinderSpectralKernel (S : Finset FinitePlace)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ x, ellipticCylinderSpectralKernel S s x ∂ellipticCylinderProductHaar S) =
      (∏ v : S,
        (1 - (Nat.card (RingOfIntegers ⧸ v.1.asIdeal) : ℂ)⁻¹ *
          localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.1.asIdeal)) s) /
        (1 - localSpectralParameter (Nat.card (RingOfIntegers ⧸ v.1.asIdeal)) s)) *
      ((1 - (3 : ℂ)⁻¹ * localSpectralParameter 3 s) / (1 - localSpectralParameter 3 s)) := by
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  unfold ellipticCylinderSpectralKernel ellipticCylinderProductHaar
  rw [integral_prod_mul, integral_ignore_probability,
    integral_infinityCompletionSpectralKernel s hs]
  congr 1
  unfold finiteCylinderSpectralKernel
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl fun v _ => integral_finiteCompletionSpectralKernel v.1 s hs

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticCylinderAssembly_measurePreserving
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_ellipticCylinderAssembly
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticCylinderSpectralKernel_integrable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_ellipticCylinderSpectralKernel
