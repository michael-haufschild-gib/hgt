import GaloisForLFunctions.HTGeometry.EventComplementaryRecord
import GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression

/-!
# Independent composition requires a complementary record

Let `V` be a finite-dimensional carrier.  Two independently variable copies have tensor carrier
`V ⊗ V`.  If a public event compresses this carrier back into `V`, while a complementary map into
`E` makes the combined event faithful, then `E` has dimension at least

`(finrank V)² - finrank V`.

At this minimal dimension, faithfulness forces the public compression to be surjective, the
record restricted to the compression kernel to be an equivalence, and the combined event to give
an equivalence

`V ⊗ V ≃ V × E`.

This is unconditional finite-dimensional linear algebra.  It does not select the record, prove
that a physical composite is a full tensor product, identify `E` with a spatial or holographic
boundary, or derive any gravitational dynamics.
-/

namespace GaloisForLFunctions.HTGeometry

open Module
open scoped TensorProduct

noncomputable section

variable {K V E : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/--
A faithful public compression together with a complementary record needs record dimension at
least the finite independent-composition debt `(dim V)² - dim V`.
-/
theorem independentCompositionBoundaryRecord_finrank_lower_bound
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R)) :
    finrank K V * finrank K V - finrank K V ≤ finrank K E :=
  le_trans
    (finiteCarrierTensorCompression_kernel_lower_bound μ)
    (eventRecord_finrank_lower_bound μ R hμR)

/--
A record of the minimal possible debt dimension makes the tensor carrier and the
public-carrier--record product equal in dimension.
-/
theorem minimalIndependentCompositionBoundary_finrank
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    finrank K (V ⊗[K] V) = finrank K (V × E) := by
  rw [Module.finrank_tensorProduct, Module.finrank_prod, hE]
  by_cases hd : finrank K V = 0
  · simp [hd]
  · have hOne : 1 ≤ finrank K V := Nat.one_le_iff_ne_zero.mpr hd
    have hle :
        finrank K V ≤ finrank K V * finrank K V := by
      calc
        finrank K V = finrank K V * 1 := by simp
        _ ≤ finrank K V * finrank K V :=
          Nat.mul_le_mul_left (finrank K V) hOne
    exact (Nat.add_sub_of_le hle).symm

/--
At minimal record dimension, a faithful compression--record pair is automatically bijective.
-/
theorem independentCompositionBoundary_bijective_of_minimal_record
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R))
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    Function.Bijective (μ.prod R) := by
  have hdim := minimalIndependentCompositionBoundary_finrank (V := V) hE
  exact
    ⟨hμR,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hμR⟩

/--
Minimal faithful recording leaves no unused public direction: the public compression is
surjective.
-/
theorem independentCompositionCompression_surjective_of_minimal_record
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R))
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    Function.Surjective μ := by
  have hsurj :=
    (independentCompositionBoundary_bijective_of_minimal_record μ R hμR hE).2
  intro v
  obtain ⟨x, hx⟩ := hsurj (v, 0)
  exact ⟨x, congrArg Prod.fst hx⟩

/--
At minimal faithful record dimension, the directions erased by public compression are exactly
the complementary record.
-/
theorem independentCompositionKernelRecord_bijective_of_minimal_record
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R))
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    Function.Bijective (eventRecordOnKernel μ R) := by
  have hμ :=
    independentCompositionCompression_surjective_of_minimal_record μ R hμR hE
  have hker :=
    finiteCarrierTensorCompression_kernel_eq_of_surjective μ hμ
  have hdim :
      finrank K (LinearMap.ker μ) = finrank K E :=
    hker.trans hE.symm
  have hinj := eventRecordOnKernel_injective μ R hμR
  exact
    ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- The exact equivalence between erased independent-composition directions and minimal record. -/
def independentCompositionKernelRecordEquiv
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R))
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    LinearMap.ker μ ≃ₗ[K] E :=
  LinearEquiv.ofBijective (eventRecordOnKernel μ R)
    (independentCompositionKernelRecord_bijective_of_minimal_record μ R hμR hE)

/--
Minimal faithful public compression plus record reconstructs the full independent tensor carrier.
-/
def independentCompositionBoundaryEquiv
    (μ : (V ⊗[K] V) →ₗ[K] V)
    (R : (V ⊗[K] V) →ₗ[K] E)
    (hμR : Function.Injective (μ.prod R))
    (hE :
      finrank K E =
        finrank K V * finrank K V - finrank K V) :
    (V ⊗[K] V) ≃ₗ[K] (V × E) :=
  LinearEquiv.ofBijective (μ.prod R)
    (independentCompositionBoundary_bijective_of_minimal_record μ R hμR hE)

end

end GaloisForLFunctions.HTGeometry
