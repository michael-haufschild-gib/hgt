import GaloisForLFunctions.ArithmeticDefectRigidity.ContractedCofactorModulesEmbedInTheOriginal
import GaloisForLFunctions.ArithmeticDefectRigidity.AZeroCofactorForcesFiniteDimension

/-!
# Actual cofactor contractions compose

A zero diagonal kills its dilation and forces a finite-dimensional cutoff.
Positive cofactor contractions compose by multiplication of their indices,
both for normalized kernels and for their principal quotient ideals.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- A zero diagonal means that the whole selected dilation operator vanishes. -/
theorem dilation_eq_zero_iff_kernel_diag_eq_zero {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    dilation L p = 0 ↔ L.kernel p p = 0 := by
  constructor
  · intro h
    have hv : vector L p = 0 := by
      have hh := congrArg (fun D : Hilbert L →L[ℂ] Hilbert L => D (vector L 1)) h
      simpa only [dilation_vector, mul_one, zero_apply] using hh
    rw [← norm_vector_sq, hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · intro h
    apply KernelHilbert.ext_on_vectors (complexKernel L)
    intro j
    change dilation L p (vector L j) = 0
    rw [dilation_vector]
    apply vector_eq_zero_of_le_of_kernel_diag_eq_zero L ?_ h
    change (p : ℕ) ≤ (p : ℕ) * (j : ℕ)
    exact Nat.le_mul_of_pos_right _ j.property

/-- Every actual cofactor either vanishes with a finite-dimensional cutoff,
or yields another actual module with its exact principal quotient ideal. -/
theorem actual_cofactor_contraction_alternative {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    (dilation L p = 0 ∧ FiniteDimensional ℂ (Hilbert L) ∧
      Module.finrank ℂ (Hilbert L) ≤ (p : ℕ) - 1) ∨
    ∃ M : ActualCofactorLimit ε,
      (∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p) ∧
      annihilator M = cofactorAnnihilator L p := by
  by_cases hp : 0 < L.kernel p p
  · exact Or.inr (exists_actual_contracted_module L p hp)
  · have hnonneg : 0 ≤ L.kernel p p := by rw [← norm_vector_sq]; positivity
    have hz := le_antisymm (le_of_not_gt hp) hnonneg
    exact Or.inl ⟨(dilation_eq_zero_iff_kernel_diag_eq_zero L p).mpr hz,
      finiteDimensional_and_finrank_le_of_kernel_diag_eq_zero L hz⟩

/-- Positive contracted states compose by multiplying their cofactor indices. -/
theorem contracted_kernel_compose {ε : SubcriticalDamping}
    (L M N : ActualCofactorLimit ε) (p q : ℕ+) (hp : 0 < L.kernel p p)
    (hM : ∀ j k, M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p)
    (hN : ∀ j k, N.kernel j k = M.kernel (q * j) (q * k) / M.kernel q q) :
    ∀ j k, N.kernel j k = L.kernel ((p * q) * j) ((p * q) * k) /
      L.kernel (p * q) (p * q) := by
  intro j k
  rw [hN, hM, hM, ← mul_assoc, ← mul_assoc]
  exact div_div_div_cancel_right₀ hp.ne' _ _

/-- Principal quotient ideals obey the same multiplication law. -/
theorem cofactorAnnihilator_compose {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (p q : ℕ+)
    (hI : annihilator M = cofactorAnnihilator L p) :
    cofactorAnnihilator M q = cofactorAnnihilator L (p * q) := by
  ext a
  change a ∈ (annihilator M).colon
    (Ideal.span {pointMass (σ := 1 / 2) (q : ℕ)} : Set _) ↔ _
  rw [hI, Ideal.mem_colon_span_singleton]
  change a * pointMass (q : ℕ) ∈ (annihilator L).colon
      (Ideal.span {pointMass (σ := 1 / 2) (p : ℕ)} : Set _) ↔
    a ∈ (annihilator L).colon
      (Ideal.span {pointMass (σ := 1 / 2) ((p * q : ℕ+) : ℕ)} : Set _)
  rw [Ideal.mem_colon_span_singleton, Ideal.mem_colon_span_singleton,
    mul_assoc, pointMass_mul, Nat.mul_comm (q : ℕ) (p : ℕ)]
  rfl

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.actual_cofactor_contraction_alternative
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.contracted_kernel_compose
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cofactorAnnihilator_compose
end
