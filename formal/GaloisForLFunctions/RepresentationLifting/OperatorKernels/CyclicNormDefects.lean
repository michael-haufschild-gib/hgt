import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import GaloisForLFunctions.RepresentationLifting.CyclicRegularCoordinates

/-!
# Operator defects of the cyclic norm resolution

For a cyclic group of order `q`, the regular norm and difference have kernel
dimensions `q - 1` and `1`, in every characteristic. Their endomorphism
quotients have dimensions `q(q-1)` and `q`. The doubled exact differential
has quotient dimension `2q²`. These are exact instances of kernel amplification.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

universe u
variable (K G : Type u) [Field K] [CommGroup G] [Fintype G]

theorem cyclicRegular_finrank :
    Module.finrank K (CyclicRegular K G) = Fintype.card G :=
  Module.finrank_eq_card_basis (MonoidAlgebra.basis G K)

/-- The norm image is the invariant line even when the group order vanishes in the field. -/
theorem cyclicRegularNorm_range :
    (cyclicRegularNorm K G).range = Submodule.span K {cyclicNormVector K G} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact Submodule.mem_span_singleton.mpr
      ⟨cyclicAugmentation K G w, (cyclicRegularNorm_eq_smul K G w).symm⟩
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨MonoidAlgebra.single 1 a, ?_⟩
    rw [cyclicRegularNorm_eq_smul, cyclicAugmentation_single]

theorem cyclicRegularNorm_range_finrank :
    Module.finrank K (cyclicRegularNorm K G).range = 1 := by
  rw [cyclicRegularNorm_range]
  apply finrank_span_singleton
  intro h
  have hc := cyclicNormVector_coeff K G (1 : G)
  rw [h] at hc
  exact zero_ne_one hc

theorem cyclicRegularNorm_kernel_finrank :
    Module.finrank K (cyclicRegularNorm K G).ker = Fintype.card G - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (cyclicRegularNorm K G)
  rw [cyclicRegularNorm_range_finrank, cyclicRegular_finrank] at h
  omega

/-- Norm observations retain exactly the augmentation-zero directions. -/
theorem cyclicNorm_endomorphism_defect :
    Module.finrank K (Module.End K (CyclicRegular K G) ⧸
      (precompose (W := CyclicRegular K G) (cyclicRegularNorm K G)).range) =
      Fintype.card G * (Fintype.card G - 1) := by
  rw [finrank_endomorphism_quotient, cyclicRegular_finrank, cyclicRegularNorm_kernel_finrank]

variable [IsCyclic G]

theorem cyclicRegularDelta_kernel_finrank :
    Module.finrank K (cyclicRegularDelta K G).ker = 1 := by
  rw [← cyclicRegular_norm_delta_exact, cyclicRegularNorm_range_finrank]

/-- Difference observations lose exactly the invariant line. -/
theorem cyclicDelta_endomorphism_defect :
    Module.finrank K (Module.End K (CyclicRegular K G) ⧸
      (precompose (W := CyclicRegular K G) (cyclicRegularDelta K G)).range) =
      Fintype.card G := by
  rw [finrank_endomorphism_quotient, cyclicRegular_finrank,
    cyclicRegularDelta_kernel_finrank, Nat.mul_one]

/-- Exactness forces precisely half the doubled space into the differential's kernel. -/
theorem cyclicDifferential_kernel_finrank :
    Module.finrank K (cyclicDifferential K G).ker = Fintype.card G := by
  have h := LinearMap.finrank_range_add_finrank_ker (cyclicDifferential K G)
  rw [cyclicDifferential_exact] at h
  change _ + _ = Module.finrank K (CyclicRegular K G × CyclicRegular K G) at h
  rw [Module.finrank_prod, cyclicRegular_finrank] at h
  omega

/-- The doubled cyclic complex produces an exact quadratic operator defect. -/
theorem cyclicDifferential_endomorphism_defect :
    Module.finrank K (Module.End K (CyclicDetector K G) ⧸
      (precompose (W := CyclicDetector K G) (cyclicDifferential K G)).range) =
      2 * Fintype.card G ^ 2 := by
  rw [finrank_endomorphism_quotient, cyclicDifferential_kernel_finrank]
  change Module.finrank K (CyclicRegular K G × CyclicRegular K G) * _ = _
  rw [Module.finrank_prod, cyclicRegular_finrank]
  ring

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicNorm_endomorphism_defect
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicDelta_endomorphism_defect
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicDifferential_endomorphism_defect
