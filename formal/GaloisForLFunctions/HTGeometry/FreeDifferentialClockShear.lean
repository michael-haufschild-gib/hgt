import GaloisForLFunctions.HTGeometry.FreeDifferentialVariationalOreBasis
import GaloisForLFunctions.HTGeometry.SemilinearKaehlerDescent
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C]

def freeClockShearForwardJetImage (p : Fin 2 × ℕ) : JetPoly C (Fin 2) :=
  if p.1 = 0 then MvPolynomial.X (1, p.2)
  else MvPolynomial.X (0, p.2) + MvPolynomial.X (1, p.2 + 1)

def freeClockShearBackwardJetImage (p : Fin 2 × ℕ) : JetPoly C (Fin 2) :=
  if p.1 = 0 then -MvPolynomial.X (0, p.2 + 1) + MvPolynomial.X (1, p.2)
  else MvPolynomial.X (0, p.2)

def freeClockShearForwardPolyHom : JetPoly C (Fin 2) →ₐ[C] JetPoly C (Fin 2) :=
  MvPolynomial.bind₁ freeClockShearForwardJetImage

def freeClockShearBackwardPolyHom : JetPoly C (Fin 2) →ₐ[C] JetPoly C (Fin 2) :=
  MvPolynomial.bind₁ freeClockShearBackwardJetImage

omit [CharZero C] in
@[simp] theorem freeClockShearForwardPolyHom_X (p : Fin 2 × ℕ) :
    freeClockShearForwardPolyHom (C := C) (MvPolynomial.X p) =
      freeClockShearForwardJetImage p := by
  simp [freeClockShearForwardPolyHom]

omit [CharZero C] in
@[simp] theorem freeClockShearBackwardPolyHom_X (p : Fin 2 × ℕ) :
    freeClockShearBackwardPolyHom (C := C) (MvPolynomial.X p) =
      freeClockShearBackwardJetImage p := by
  simp [freeClockShearBackwardPolyHom]

omit [CharZero C] in
theorem freeClockShearForwardPolyHom_comp_backward :
    freeClockShearForwardPolyHom (C := C).comp freeClockShearBackwardPolyHom = AlgHom.id C _ := by
  ext p
  rcases p with ⟨i, n⟩
  fin_cases i <;>
    simp [freeClockShearForwardJetImage, freeClockShearBackwardJetImage]

omit [CharZero C] in
theorem freeClockShearBackwardPolyHom_comp_forward :
    freeClockShearBackwardPolyHom (C := C).comp freeClockShearForwardPolyHom = AlgHom.id C _ := by
  ext p
  rcases p with ⟨i, n⟩
  fin_cases i <;>
    simp [freeClockShearForwardJetImage, freeClockShearBackwardJetImage]

def freeClockShearPolyEquiv : JetPoly C (Fin 2) ≃ₐ[C] JetPoly C (Fin 2) :=
  AlgEquiv.ofAlgHom freeClockShearForwardPolyHom freeClockShearBackwardPolyHom
    freeClockShearForwardPolyHom_comp_backward freeClockShearBackwardPolyHom_comp_forward

def freeClockShearRingEquiv : JetField C (Fin 2) ≃+* JetField C (Fin 2) :=
  IsFractionRing.ringEquivOfRingEquiv (freeClockShearPolyEquiv (C := C)).toRingEquiv

omit [CharZero C] in
@[simp] theorem freeClockShearRingEquiv_jet_zero (n : ℕ) :
    freeClockShearRingEquiv (C := C) (JetField.jet (0, n)) = JetField.jet (1, n) := by
  rw [freeClockShearRingEquiv, JetField.jet,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [freeClockShearPolyEquiv, freeClockShearForwardJetImage]
  rfl

omit [CharZero C] in
@[simp] theorem freeClockShearRingEquiv_jet_one (n : ℕ) :
    freeClockShearRingEquiv (C := C) (JetField.jet (1, n)) =
      JetField.jet (0, n) + JetField.jet (1, n + 1) := by
  rw [freeClockShearRingEquiv, JetField.jet,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [freeClockShearPolyEquiv, freeClockShearForwardJetImage, map_add]
  rfl

omit [CharZero C] in
@[simp] theorem freeClockShearRingEquiv_symm_jet_zero (n : ℕ) :
    (freeClockShearRingEquiv (C := C)).symm (JetField.jet (0, n)) =
      -JetField.jet (0, n + 1) + JetField.jet (1, n) := by
  rw [freeClockShearRingEquiv, JetField.jet]
  change IsFractionRing.ringEquivOfRingEquiv
      (freeClockShearPolyEquiv (C := C)).toRingEquiv.symm
        (algebraMap (JetPoly C (Fin 2)) (JetField C (Fin 2)) (MvPolynomial.X (0, n))) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [freeClockShearPolyEquiv, freeClockShearBackwardJetImage, map_add]
  rfl

omit [CharZero C] in
@[simp] theorem freeClockShearRingEquiv_symm_jet_one (n : ℕ) :
    (freeClockShearRingEquiv (C := C)).symm (JetField.jet (1, n)) =
      JetField.jet (0, n) := by
  rw [freeClockShearRingEquiv, JetField.jet]
  change IsFractionRing.ringEquivOfRingEquiv
      (freeClockShearPolyEquiv (C := C)).toRingEquiv.symm
        (algebraMap (JetPoly C (Fin 2)) (JetField C (Fin 2)) (MvPolynomial.X (1, n))) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [freeClockShearPolyEquiv, freeClockShearBackwardJetImage]
  rfl

omit [CharZero C] in
theorem freeClockShearRingEquiv_fixes (c : C) :
    freeClockShearRingEquiv (C := C) (algebraMap C (JetField C (Fin 2)) c) =
      algebraMap C (JetField C (Fin 2)) c := by
  rw [IsScalarTower.algebraMap_apply C (JetPoly C (Fin 2)) (JetField C (Fin 2))]
  rw [freeClockShearRingEquiv,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [freeClockShearPolyEquiv]

theorem freeClockShearRingEquiv_deriv_comm (x : JetField C (Fin 2)) :
    freeClockShearRingEquiv (C := C) x′ =
      (freeClockShearRingEquiv (C := C) x)′ := by
  let σ := freeClockShearRingEquiv (C := C)
  let D : Derivation C (JetField C (Fin 2)) (JetField C (Fin 2)) :=
    GaloisForLFunctions.conjugateDerivation (RingEquiv.refl C) σ
      (freeClockShearRingEquiv_fixes (C := C)) JetField.jetDerivation
  have hD : D = JetField.jetDerivation := by
    apply JetField.derivation_ext
    intro p
    rcases p with ⟨i, n⟩
    fin_cases i
    · simp [D, σ, GaloisForLFunctions.conjugateDerivation_apply,
        JetField.jetDerivation_jet]
    · simp [D, σ, GaloisForLFunctions.conjugateDerivation_apply,
        JetField.jetDerivation_jet, map_add]
  have hx := congrArg (fun E : Derivation C (JetField C (Fin 2)) (JetField C (Fin 2)) => E x) hD
  change σ.symm (JetField.jetDerivation (σ x)) = JetField.jetDerivation x at hx
  have hx' := congrArg σ hx
  simpa [σ, JetField.deriv_eq] using hx'.symm

def freeClockShear : FreeAut (C := C) (ι := Fin 2) where
  toRingEquiv := freeClockShearRingEquiv
  fixes := freeClockShearRingEquiv_fixes
  deriv_comm := freeClockShearRingEquiv_deriv_comm

/-- Literal Fréchet matrix of the rank-two clock shear. -/
def freeClockShearFrechetMatrix : Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))) :=
  !![0, 1; 1, DiffOp.mono 1 1]

theorem freeFrechetMatrix_freeClockShear :
    freeFrechetMatrix (freeClockShear (C := C)) = freeClockShearFrechetMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [freeFrechetMatrix, freeClockShear, freeClockShearFrechetMatrix,
      JetField.frechet_jet_of_ne]
  · simp [freeFrechetMatrix, freeClockShear, freeClockShearFrechetMatrix,
      JetField.frechet_jet_self, DiffOp.one_def]
  · simp [freeFrechetMatrix, freeClockShear, freeClockShearFrechetMatrix,
      JetField.frechet_add, JetField.frechet_jet_self, JetField.frechet_jet_of_ne,
      DiffOp.one_def]
  · simp [freeFrechetMatrix, freeClockShear, freeClockShearFrechetMatrix,
      JetField.frechet_add, JetField.frechet_jet_self, JetField.frechet_jet_of_ne]

theorem matDeg_freeClockShearFrechetMatrix :
    DiffOp.matDeg (freeClockShearFrechetMatrix (C := C)) = 1 := by
  refine le_antisymm (DiffOp.matDeg_le fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;>
      simp [freeClockShearFrechetMatrix, DiffOp.degree_zero, DiffOp.degree_one,
        DiffOp.degree_mono]
  · have h : DiffOp.degree
        (freeClockShearFrechetMatrix (C := C) 1 1) = 1 := by
      simp [freeClockShearFrechetMatrix, DiffOp.degree_mono]
    calc
      1 = DiffOp.degree (freeClockShearFrechetMatrix (C := C) 1 1) := h.symm
      _ ≤ DiffOp.matDeg (freeClockShearFrechetMatrix (C := C)) :=
        DiffOp.degree_le_matDeg _ 1 1

omit [CharZero C] in
theorem topCoeffMatrix_freeClockShearFrechetMatrix :
    DiffOp.topCoeffMatrix (freeClockShearFrechetMatrix (C := C)) 1 =
      !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [freeClockShearFrechetMatrix, DiffOp.topCoeffMatrix, DiffOp.one_def,
      DiffOp.coeff_mono_of_ne]

omit [CharZero C] in
private theorem freeClockShear_leading_chain_entry (n : ℕ) :
    DiffOp.chainProdK (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetMatrix (C := C)) 1) n 1 1 = 1 := by
  rw [show (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetMatrix (C := C)) 1) =
      (fun _ : ℕ => (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (JetField C (Fin 2)))) by
    funext _
    exact topCoeffMatrix_freeClockShearFrechetMatrix]
  induction n with
  | zero => simp [DiffOp.chainProdK]
  | succ n ih =>
      rw [DiffOp.chainProdK_succ, Matrix.mul_apply]
      simp [Fin.sum_univ_two, ih]

omit [CharZero C] in
private theorem freeClockShear_leading_chain_ne_zero (n : ℕ) :
    DiffOp.chainProdK (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetMatrix (C := C)) 1) n ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (JetField C (Fin 2)) => M 1 1) hzero
  rw [freeClockShear_leading_chain_entry, Matrix.zero_apply] at hentry
  exact one_ne_zero hentry

omit [CharZero C] in
private theorem chainProd_const_eq_pow
    (A : Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2)))) (n : ℕ) :
    DiffOp.chainProd (K := JetField C (Fin 2)) (fun _ => A) n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [DiffOp.chainProd_succ, ih, pow_succ]

theorem matDeg_freeClockShearFrechetMatrix_pow (n : ℕ) :
    DiffOp.matDeg (freeClockShearFrechetMatrix (C := C) ^ n) = n := by
  rw [← chainProd_const_eq_pow]
  simpa using DiffOp.matDeg_chainProd_eq
    (fun _ : ℕ => freeClockShearFrechetMatrix (C := C)) 1
    (fun _ i j => by
      have h := DiffOp.degree_le_matDeg (freeClockShearFrechetMatrix (C := C)) i j
      rwa [matDeg_freeClockShearFrechetMatrix] at h)
    freeClockShear_leading_chain_ne_zero n

theorem mapFreeFrechetMatrix_freeClockShear_matrix :
    mapFreeFrechetMatrix (freeClockShear (C := C))
        (freeClockShearFrechetMatrix (C := C)) =
      freeClockShearFrechetMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mapFreeFrechetMatrix, freeClockShearFrechetMatrix, freeClockShear,
      DiffOp.map_zero', DiffOp.map_one', DiffOp.map_mono]

theorem mapFreeFrechetMatrix_freeClockShear_matrix_pow (n : ℕ) :
    mapFreeFrechetMatrix (freeClockShear (C := C))
        (freeClockShearFrechetMatrix (C := C) ^ n) =
      freeClockShearFrechetMatrix ^ n := by
  let φ : DiffOp (JetField C (Fin 2)) →+* DiffOp (JetField C (Fin 2)) :=
    DiffOp.mapRingHom (freeClockShear (C := C)).toRingEquiv.toRingHom
      (freeClockShear (C := C)).deriv_comm
  have hφ : (freeClockShearFrechetMatrix (C := C)).map φ =
      freeClockShearFrechetMatrix := by
    exact mapFreeFrechetMatrix_freeClockShear_matrix (C := C)
  change (freeClockShearFrechetMatrix (C := C) ^ n).map φ = _
  rw [Matrix.map_pow, hφ]

theorem freeFrechetMatrix_freeClockShear_pow_succ (n : ℕ) :
    freeFrechetMatrix (freeClockShear (C := C) ^ (n + 1)) =
      freeClockShearFrechetMatrix ^ (n + 1) := by
  induction n with
  | zero => simpa using freeFrechetMatrix_freeClockShear (C := C)
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ,
        freeFrechetMatrix_mul, ih,
        mapFreeFrechetMatrix_freeClockShear_matrix_pow,
        freeFrechetMatrix_freeClockShear, pow_succ]
      simp [pow_succ, mul_assoc]

/-- Exact unit clock cost: the n-th shear iterate has differential order n. -/
theorem freeDifferentialOrder_freeClockShear_pow (n : ℕ) :
    freeDifferentialOrder (freeClockShear (C := C) ^ n) = n := by
  cases n with
  | zero => exact freeDifferentialOrder_one
  | succ n =>
      rw [freeDifferentialOrder_eq_matDeg_freeFrechetMatrix,
        freeFrechetMatrix_freeClockShear_pow_succ,
        matDeg_freeClockShearFrechetMatrix_pow]

/-- The intrinsic asymptotic clock speed of the rank-two shear is exactly one. -/
theorem freeOrderTranslationLength_freeClockShear :
    freeOrderGauge.translationLength (freeClockShear (C := C)) = 1 := by
  have hlim := tendsto_normalized_freeDifferentialOrder (freeClockShear (C := C))
  have heq :
      (fun n : ℕ =>
        (freeDifferentialOrder (freeClockShear (C := C) ^ n) : ℝ) / n) =ᶠ[Filter.atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    rw [freeDifferentialOrder_freeClockShear_pow]
    exact div_self (Nat.cast_ne_zero.mpr (by omega))
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique hlim (hone.congr' heq.symm)

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
