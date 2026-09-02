import GaloisForLFunctions.HTGeometry.FiniteRightFactorSpecialization
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedDomain

/-!
# Specialization of tensor-fraction derivation eigenvectors

A derivation on the left factor of a tensor product commutes with specialization of the right
factor.  Over an algebraically closed constant field, a nonzero fraction in a tensor product that
solves a rank-one differential equation therefore specializes to a nonzero solution in the left
field.  Only the finitely many right coefficients in the numerator and denominator are needed, so
the right factor may be an arbitrary field extension.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Linear map obtained by applying a derivation only to the left tensor factor. -/
def tensorLeftDerivationLinearMap
    (C A B : Type*) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (D : Derivation C A A) :
    (A ⊗[C] B) →ₗ[C] (A ⊗[C] B) :=
  TensorProduct.map D.toLinearMap LinearMap.id

@[simp]
theorem tensorLeftDerivationLinearMap_tmul
    (C A B : Type*) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (D : Derivation C A A) (a : A) (b : B) :
    tensorLeftDerivationLinearMap C A B D (a ⊗ₜ[C] b) = D a ⊗ₜ[C] b := by
  simp [tensorLeftDerivationLinearMap]

/-- Derivation obtained by differentiating only the left tensor factor. -/
def tensorLeftDerivation
    (C A B : Type*) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (D : Derivation C A A) :
    Derivation C (A ⊗[C] B) (A ⊗[C] B) :=
  Derivation.mk' (tensorLeftDerivationLinearMap C A B D) (by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, zero_smul, smul_zero, add_zero]
    | tmul a b =>
        induction y using TensorProduct.induction_on with
        | zero => simp only [mul_zero, map_zero, smul_zero, zero_smul, add_zero]
        | tmul a' b' =>
            simp only [Algebra.TensorProduct.tmul_mul_tmul,
              tensorLeftDerivationLinearMap_tmul, Derivation.leibniz,
              smul_eq_mul]
            rw [TensorProduct.add_tmul]
            rw [mul_comm b b']
        | add y₁ y₂ h₁ h₂ =>
            rw [mul_add, map_add, h₁, h₂, map_add, smul_add]
            simp only [add_smul]
            abel
    | add x₁ x₂ h₁ h₂ =>
        rw [add_mul, map_add, h₁, h₂, map_add, add_smul]
        simp only [smul_add]
        abel)

@[simp]
theorem tensorLeftDerivation_tmul
    (C A B : Type*) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (D : Derivation C A A) (a : A) (b : B) :
    tensorLeftDerivation C A B D (a ⊗ₜ[C] b) = D a ⊗ₜ[C] b :=
  rfl

/-- Right-factor specialization intertwines a derivation acting on the left tensor factor. -/
theorem tensorSpecialization_tensorLeftDerivation
    (C A R : Type*) [Field C] [CommRing A] [CommRing R]
    [Algebra C A] [Algebra C R] (D : Derivation C A A) (φ : R →ₐ[C] C)
    (x : A ⊗[C] R) :
    GaloisForLFunctions.tensorSpecialization C A R φ
        (tensorLeftDerivation C A R D x) =
      D (GaloisForLFunctions.tensorSpecialization C A R φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
      simp only [tensorLeftDerivation_tmul,
        GaloisForLFunctions.tensorSpecialization_tmul]
      rw [Derivation.leibniz]
      simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Inclusion of a right subalgebra intertwines a derivation acting on the left tensor factor. -/
theorem tensorRightSubalgebraMap_tensorLeftDerivation
    (C A B : Type*) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (R : Subalgebra C B)
    (D : Derivation C A A) (x : A ⊗[C] R) :
    GaloisForLFunctions.tensorRightSubalgebraMap C A B R
        (tensorLeftDerivation C A R D x) =
      tensorLeftDerivation C A B D
        (GaloisForLFunctions.tensorRightSubalgebraMap C A B R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rfl
  | add x y hx hy => simp [hx, hy]

/-- A nonzero tensor fraction satisfying a left-factor rank-one differential equation specializes
to a nonzero solution in the left field. -/
theorem exists_left_eigenvector_of_tensor_fraction_identity
    (C A R : Type*) [Field C] [IsAlgClosed C] [Field A] [CommRing R] [IsDomain R]
    [Algebra C A] [Algebra C R] [Algebra.FiniteType C R]
    (D : Derivation C A A) (q : A) (N S : A ⊗[C] R)
    (hN : N ≠ 0) (hS : S ≠ 0)
    (hidentity : tensorLeftDerivation C A R D N * S -
        N * tensorLeftDerivation C A R D S =
      (q ⊗ₜ[C] (1 : R)) * N * S) :
    ∃ u : A, u ≠ 0 ∧ D u = q * u := by
  haveI : IsDomain (A ⊗[C] R) :=
    letI : IsDomain (R ⊗[C] A) :=
      isDomain_tensorProduct_of_finiteType (k := C) (A := R) (B := A)
    (Algebra.TensorProduct.comm C A R).toRingEquiv.toMulEquiv.isDomain _
  obtain ⟨φ, hφNS⟩ := GaloisForLFunctions.exists_tensorSpecialization_ne_zero
    C A R (N * S) (mul_ne_zero hN hS)
  let sp := GaloisForLFunctions.tensorSpecialization C A R φ
  let n := sp N
  let s := sp S
  have hns : n * s ≠ 0 := by simpa [sp, n, s] using hφNS
  have hn : n ≠ 0 := left_ne_zero_of_mul hns
  have hs : s ≠ 0 := right_ne_zero_of_mul hns
  have hid : D n * s - n * D s = q * n * s := by
    simpa [sp, n, s, tensorSpecialization_tensorLeftDerivation,
      GaloisForLFunctions.tensorSpecialization_tmul] using congr_arg sp hidentity
  refine ⟨n / s, div_ne_zero hn hs, ?_⟩
  have hdu : (n / s) * D s + s * D (n / s) = D n := by
    have h := congr_arg D (div_mul_cancel₀ n hs)
    simpa only [Derivation.leibniz, smul_eq_mul] using h
  apply (mul_left_cancel₀ hs)
  calc
    s * D (n / s) = D n - (n / s) * D s := by linear_combination hdu
    _ = q * n := by
      field_simp [hs]
      linear_combination hid
    _ = s * (q * (n / s)) := by field_simp [hs]

/-- Finite-support form: the right tensor factor may be any field extension. -/
theorem exists_left_eigenvector_of_arbitrary_right_tensor_fraction_identity
    (C A B : Type*) [Field C] [IsAlgClosed C] [Field A] [Field B]
    [Algebra C A] [Algebra C B]
    (D : Derivation C A A) (q : A) (N S : A ⊗[C] B)
    (hN : N ≠ 0) (hS : S ≠ 0)
    (hidentity : tensorLeftDerivation C A B D N * S -
        N * tensorLeftDerivation C A B D S =
      (q ⊗ₜ[C] (1 : B)) * N * S) :
    ∃ u : A, u ≠ 0 ∧ D u = q * u := by
  obtain ⟨R, hR, NR, SR, hNR, hSR⟩ :=
    GaloisForLFunctions.exists_fg_right_subalgebra_lifts_pair C A B N S
  letI : Algebra.FiniteType C R :=
    GaloisForLFunctions.finiteTypeOfSubalgebraFG R hR
  have hNR0 : NR ≠ 0 := by
    intro hzero
    apply hN
    rw [← hNR, hzero, map_zero]
  have hSR0 : SR ≠ 0 := by
    intro hzero
    apply hS
    rw [← hSR, hzero, map_zero]
  have hidentityR : tensorLeftDerivation C A R D NR * SR -
        NR * tensorLeftDerivation C A R D SR =
      (q ⊗ₜ[C] (1 : R)) * NR * SR := by
    apply GaloisForLFunctions.tensorRightSubalgebraMap_injective C A B R
    simpa only [map_sub, map_mul,
      GaloisForLFunctions.tensorRightSubalgebraMap_tmul,
      tensorRightSubalgebraMap_tensorLeftDerivation,
      hNR, hSR, Subalgebra.coe_one] using hidentity
  exact exists_left_eigenvector_of_tensor_fraction_identity
    C A R D q NR SR hNR0 hSR0 hidentityR

end

end GaloisForLFunctions.HTGeometry
