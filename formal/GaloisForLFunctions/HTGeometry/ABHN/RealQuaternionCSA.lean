import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer
import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Real quaternion central simple algebra

This module places Mathlib's real quaternion division algebra in the project Brauer group.  Its
Brauer class is self-opposite and therefore has exponent dividing two.  This is the concrete
non-split candidate underlying the classical real local invariant.  The separate classification
that every real central simple algebra is split or quaternionic is not postulated here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped Quaternion TensorProduct Matrix

/-- A real quaternion commuting with every quaternion has no imaginary component. -/
theorem realQuaternion_eq_re_of_commutes (q : ℍ) (hq : ∀ x : ℍ, x * q = q * x) :
    q = (q.re : ℍ) := by
  have hI := hq ⟨0, 1, 0, 0⟩
  have hJ := hq ⟨0, 0, 1, 0⟩
  have hImI : q.imI = 0 := by
    have h := congrArg (fun x : ℍ => x.imK) hJ
    simp only [Quaternion.imK_mul, zero_mul, zero_add, one_mul, mul_zero, sub_zero] at h
    linarith
  have hImJ : q.imJ = 0 := by
    have h := congrArg (fun x : ℍ => x.imK) hI
    simp only [Quaternion.imK_mul, zero_mul, zero_add, one_mul, mul_zero, sub_zero] at h
    linarith
  have hImK : q.imK = 0 := by
    have h := congrArg (fun x : ℍ => x.imJ) hI
    simp only [Quaternion.imJ_mul, zero_mul, zero_add, one_mul, mul_zero, sub_zero] at h
    linarith
  apply Quaternion.ext <;> simp [hImI, hImJ, hImK]

/-- The center of the real quaternions is precisely the scalar copy of `ℝ`. -/
theorem realQuaternion_isCentral : Algebra.IsCentral ℝ ℍ where
  out := by
    intro q hq
    rw [Algebra.mem_bot]
    refine ⟨q.re, ?_⟩
    exact (realQuaternion_eq_re_of_commutes q (Subalgebra.mem_center_iff.mp hq)).symm

/-- The Hamilton quaternions form a finite-dimensional central simple algebra over `ℝ`. -/
noncomputable def realQuaternionCSA : CSA ℝ where
  carrier := ℍ
  isCentral := realQuaternion_isCentral
  isSimple := by infer_instance
  fin_dim := by infer_instance

/-- The Hamilton quaternions are not commutative. -/
theorem realQuaternion_not_mul_comm : ¬ ∀ q r : ℍ, q * r = r * q := by
  intro h
  have h' := congrArg (fun x : ℍ => x.imK) (h ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩)
  simp only [Quaternion.imK_mul, zero_add, add_zero, one_mul, mul_zero, sub_zero, zero_sub] at h'
  linarith

/-- The quaternion CSA is not isomorphic to the degree-one split algebra. This does not itself
show that its Brauer class is nontrivial, since Brauer equivalence also allows matrix
stabilization. -/
theorem realQuaternion_no_scalarAlgEquiv : ¬ Nonempty (ℝ ≃ₐ[ℝ] ℍ) := by
  rintro ⟨e⟩
  apply realQuaternion_not_mul_comm
  intro q r
  obtain ⟨a, rfl⟩ := e.surjective q
  obtain ⟨b, rfl⟩ := e.surjective r
  calc
    e a * e b = e (a * b) := (map_mul e a b).symm
    _ = e (b * a) := by rw [mul_comm]
    _ = e b * e a := map_mul e b a

/-- The real `2 × 2` matrix algebra has a nonzero nonunit, exhibited by a square-zero matrix. -/
private theorem realMatrix_two_exists_nonunit :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ, M ≠ 0 ∧ ¬ IsUnit M := by
  let N : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 0, 0]
  refine ⟨N, ?_, ?_⟩
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [N] at h01
  · intro hunit
    have hsq : N * N = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply]
    have : IsUnit (N * N) := hunit.mul hunit
    rw [hsq] at this
    exact not_isUnit_zero this

/-- Hamilton quaternions are not isomorphic to a split real matrix algebra of any degree.
This proves nonsplitness as a central simple algebra.  It does not identify their Brauer class:
Brauer equivalence permits matrix stabilization on both sides. -/
theorem realQuaternion_no_matrixAlgEquiv (n : ℕ) :
    ¬ Nonempty (ℍ ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) := by
  rintro ⟨e⟩
  have hn : n = 2 := by
    have hdim : 4 = n * n := by
      simpa [Quaternion.finrank_eq_four, Module.finrank_matrix] using e.toLinearEquiv.finrank_eq
    have hdim' : (4 : ℝ) = (n : ℝ) * (n : ℝ) := by
      exact_mod_cast hdim
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn' : (n : ℝ) = 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    exact_mod_cast hn'
  subst n
  obtain ⟨N, hN, hNunit⟩ := realMatrix_two_exists_nonunit
  apply hNunit
  have he : e.symm N ≠ 0 := by
    intro h
    apply hN
    simpa using congrArg e h
  simpa using he.isUnit.map e

/-- Quaternion conjugation is an algebra equivalence from the real quaternions to their
opposite algebra, so the opposite represents the same Brauer class. -/
theorem realQuaternionBrauerClass_opposite :
    brauerClass (oppositeCSA realQuaternionCSA) = brauerClass realQuaternionCSA := by
  exact
    (brauerClass_eq_of_algEquiv realQuaternionCSA (oppositeCSA realQuaternionCSA)
      Quaternion.starAe).symm

/-- The Brauer inverse of the real quaternion class is the class itself. -/
theorem realQuaternionBrauerTensorNeg :
    brauerTensorNeg ℝ (brauerClass realQuaternionCSA) = brauerClass realQuaternionCSA := by
  rw [brauerTensorNeg_brauerClass]
  exact realQuaternionBrauerClass_opposite

/-- The real quaternion class has order dividing two in the Brauer group. -/
theorem realQuaternionBrauerClass_add_self :
    brauerTensorAdd ℝ (brauerClass realQuaternionCSA) (brauerClass realQuaternionCSA) =
      brauerSplitClass ℝ := by
  calc
    brauerTensorAdd ℝ (brauerClass realQuaternionCSA) (brauerClass realQuaternionCSA) =
      brauerTensorAdd ℝ (brauerTensorNeg ℝ (brauerClass realQuaternionCSA))
        (brauerClass realQuaternionCSA) := by
          exact congrArg (fun x => brauerTensorAdd ℝ x (brauerClass realQuaternionCSA))
            realQuaternionBrauerTensorNeg.symm
    _ = brauerSplitClass ℝ :=
      brauerTensorNeg_add_self ℝ (brauerClass realQuaternionCSA)

/-- The standard faithful representation of Hamilton quaternions by complex `2 × 2` matrices. -/
noncomputable def realQuaternionComplexMatrix (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + (q.imI : ℂ) * Complex.I,
      (q.imJ : ℂ) + (q.imK : ℂ) * Complex.I;
     -(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I,
      (q.re : ℂ) - (q.imI : ℂ) * Complex.I]

theorem realQuaternionComplexMatrix_mul (p q : ℍ) :
    realQuaternionComplexMatrix (p * q) =
      realQuaternionComplexMatrix p * realQuaternionComplexMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realQuaternionComplexMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring

/-- The complex matrix representation, as an `ℝ`-algebra morphism. -/
noncomputable def realQuaternionComplexMatrixAlgHom :
    ℍ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := realQuaternionComplexMatrix
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realQuaternionComplexMatrix]
  map_mul' := realQuaternionComplexMatrix_mul
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realQuaternionComplexMatrix]
  map_add' := by
    intro p q
    ext i j
    fin_cases i <;> fin_cases j <;> simp [realQuaternionComplexMatrix] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realQuaternionComplexMatrix, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

/-- The scalar extension of the quaternion matrix representation to `ℂ`. -/
noncomputable def realQuaternionComplexificationMap :
    ℂ ⊗[ℝ] ℍ →ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    realQuaternionComplexMatrixAlgHom
      (fun c q => Algebra.commutes c (realQuaternionComplexMatrix q))

theorem realQuaternionComplexificationMap_tmul (c : ℂ) (q : ℍ) :
    realQuaternionComplexificationMap (c ⊗ₜ[ℝ] q) = c • realQuaternionComplexMatrix q := by
  rw [realQuaternionComplexificationMap, Algebra.TensorProduct.lift_tmul]
  change (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ)) c * realQuaternionComplexMatrix q = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]

private def realQuaternionI : ℍ := ⟨0, 1, 0, 0⟩
private def realQuaternionJ : ℍ := ⟨0, 0, 1, 0⟩
private def realQuaternionK : ℍ := ⟨0, 0, 0, 1⟩

/-- The quaternion basis spans all complex `2 × 2` matrices after scalar extension. -/
theorem realQuaternionComplexificationMap_surjective :
    Function.Surjective realQuaternionComplexificationMap := by
  intro M
  refine ⟨
    (M 0 0 / 2) ⊗ₜ[ℝ] (1 : ℍ) + (-M 0 0 * Complex.I / 2) ⊗ₜ[ℝ] realQuaternionI +
      (M 1 1 / 2) ⊗ₜ[ℝ] (1 : ℍ) + (M 1 1 * Complex.I / 2) ⊗ₜ[ℝ] realQuaternionI +
      (M 0 1 / 2) ⊗ₜ[ℝ] realQuaternionJ + (-M 0 1 * Complex.I / 2) ⊗ₜ[ℝ] realQuaternionK +
      (-M 1 0 / 2) ⊗ₜ[ℝ] realQuaternionJ + (-M 1 0 * Complex.I / 2) ⊗ₜ[ℝ] realQuaternionK,
    ?_⟩
  simp only [map_add, realQuaternionComplexificationMap_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realQuaternionComplexMatrix, realQuaternionI, realQuaternionJ, realQuaternionK] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem realQuaternionComplexificationMap_finrank_eq :
    Module.finrank ℂ (ℂ ⊗[ℝ] ℍ) =
      Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Module.finrank_tensorProduct, Module.finrank_matrix]
  simp [Quaternion.finrank_eq_four]

/-- Complexification splits the Hamilton quaternions as the `2 × 2` matrix algebra. -/
noncomputable def realQuaternionComplexificationAlgEquiv :
    ℂ ⊗[ℝ] ℍ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  AlgEquiv.ofBijective realQuaternionComplexificationMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        realQuaternionComplexificationMap_finrank_eq).mpr
          realQuaternionComplexificationMap_surjective,
      realQuaternionComplexificationMap_surjective⟩

/-- The real quaternion Brauer class vanishes after extension to `ℂ`. -/
theorem scalarExtension_realQuaternionBrauerClass_eq_split :
    scalarExtensionBrauerMap ℝ ℂ (brauerClass realQuaternionCSA) = brauerSplitClass ℂ := by
  calc
    scalarExtensionBrauerMap ℝ ℂ (brauerClass realQuaternionCSA) =
        brauerClass (scalarExtensionCSA (L := ℂ) realQuaternionCSA) := rfl
    _ = brauerClass (matrixFinCSA (scalarCSA ℂ) 2) :=
      brauerClass_eq_of_algEquiv _ _ realQuaternionComplexificationAlgEquiv
    _ = brauerSplitClass ℂ := brauerClass_matrixFinCSA_scalar_eq 2

end GaloisForLFunctions.HTGeometry.ABHN
