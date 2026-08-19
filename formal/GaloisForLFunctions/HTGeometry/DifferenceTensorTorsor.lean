import GaloisForLFunctions.HTGeometry.DifferenceGaloisMatrix

/-!
# The difference operator on a tensor square

The torsor property of a Picard--Vessiot ring compares the two copies of a fundamental matrix
inside `R ⊗_K R`, so the difference operator has to act there.  It does not act by a `K`-linear
tensor map, because the operator moves the base field: it is `σ_K`-semilinear.  But the twist is by
an automorphism of `K`, so the tensor relations are permuted rather than destroyed, and the map
`x ⊗ y ↦ σ x ⊗ σ y` descends to the tensor product over `K` all the same.

This file constructs that map as a ring automorphism, with an explicit two-sided inverse built from
`σ⁻¹`, and proves the comparison statement it exists for: two invertible fundamental solution
matrices of the same system differ by a matrix of constants.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- The inverse automorphism is compatible with the inverse shift of the base. -/
theorem differenceCompat_symm {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) (a : K) :
    σR.symm (algebraMap K R a) = algebraMap K R (σK.symm a) := by
  apply σR.injective
  rw [σR.apply_symm_apply, hcompat, σK.apply_symm_apply]

/-- The additive map `x ⊗ y ↦ σ x ⊗ σ y` on the tensor square. -/
def differenceTensorAddHom (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) :
    (R ⊗[K] R) →+ (R ⊗[K] R) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun x : R => AddMonoidHom.mk' (fun y : R => σR x ⊗ₜ[K] σR y)
        (fun y₁ y₂ => by rw [map_add, TensorProduct.tmul_add]))
      (fun x₁ x₂ => by
        refine AddMonoidHom.ext fun y => ?_
        show σR (x₁ + x₂) ⊗ₜ[K] σR y = σR x₁ ⊗ₜ[K] σR y + σR x₂ ⊗ₜ[K] σR y
        rw [map_add, TensorProduct.add_tmul]))
    (by
      intro a x y
      show σR (a • x) ⊗ₜ[K] σR y = σR x ⊗ₜ[K] σR (a • y)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hcompat,
        ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul])

@[simp] theorem differenceTensorAddHom_tmul (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) (x y : R) :
    differenceTensorAddHom σK σR hcompat (x ⊗ₜ[K] y) = σR x ⊗ₜ[K] σR y := rfl

/-- The difference operator on the tensor square, as a ring homomorphism. -/
def differenceTensorHom (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) :
    (R ⊗[K] R) →+* (R ⊗[K] R) where
  toFun := differenceTensorAddHom σK σR hcompat
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [Algebra.TensorProduct.one_def, differenceTensorAddHom_tmul, map_one,
      ← Algebra.TensorProduct.one_def]
  map_mul' := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul x' y' =>
            rw [Algebra.TensorProduct.tmul_mul_tmul, differenceTensorAddHom_tmul,
              differenceTensorAddHom_tmul, differenceTensorAddHom_tmul, map_mul, map_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
        | add v₁ v₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | add u₁ u₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

@[simp] theorem differenceTensorHom_tmul (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) (x y : R) :
    differenceTensorHom σK σR hcompat (x ⊗ₜ[K] y) = σR x ⊗ₜ[K] σR y := rfl

/-- **The difference operator on the tensor square is an automorphism.** -/
def differenceTensorEquiv (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) :
    (R ⊗[K] R) ≃+* (R ⊗[K] R) :=
  RingEquiv.ofRingHom (differenceTensorHom σK σR hcompat)
    (differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat))
    (by
      refine RingHom.ext fun u => ?_
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          show differenceTensorHom σK σR hcompat
            (differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat) (x ⊗ₜ[K] y)) = x ⊗ₜ[K] y
          rw [differenceTensorHom_tmul, differenceTensorHom_tmul, σR.apply_symm_apply,
            σR.apply_symm_apply]
      | add u₁ u₂ h₁ h₂ =>
          show differenceTensorHom σK σR hcompat
            (differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat) (u₁ + u₂)) = u₁ + u₂
          rw [map_add, map_add]
          rw [show differenceTensorHom σK σR hcompat
              (differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat) u₁) = u₁ from h₁,
            show differenceTensorHom σK σR hcompat
              (differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat) u₂) = u₂ from h₂])
    (by
      refine RingHom.ext fun u => ?_
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          show differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat)
            (differenceTensorHom σK σR hcompat (x ⊗ₜ[K] y)) = x ⊗ₜ[K] y
          rw [differenceTensorHom_tmul, differenceTensorHom_tmul, σR.symm_apply_apply,
            σR.symm_apply_apply]
      | add u₁ u₂ h₁ h₂ =>
          show differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat)
            (differenceTensorHom σK σR hcompat (u₁ + u₂)) = u₁ + u₂
          rw [map_add, map_add]
          rw [show differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat)
              (differenceTensorHom σK σR hcompat u₁) = u₁ from h₁,
            show differenceTensorHom σK.symm σR.symm (differenceCompat_symm hcompat)
              (differenceTensorHom σK σR hcompat u₂) = u₂ from h₂])

@[simp] theorem differenceTensorEquiv_tmul (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a)) (x y : R) :
    differenceTensorEquiv σK σR hcompat (x ⊗ₜ[K] y) = σR x ⊗ₜ[K] σR y := rfl

/-! ### Two fundamental matrices differ by a matrix of constants -/

variable {n : ℕ}

/-- **Comparison of fundamental matrices.**  Two invertible fundamental solution matrices of the
same system differ by a matrix fixed by the difference operator. -/
theorem map_invOf_mul_eq_self {S : Type*} [CommRing S] (τ : S ≃+* S)
    (B Y Z : Matrix (Fin n) (Fin n) S) [Invertible Y] [Invertible Z]
    (hY : Y.map (τ : S → S) = B * Y) (hZ : Z.map (τ : S → S) = B * Z) :
    (⅟Y * Z).map (τ : S → S) = ⅟Y * Z := by
  classical
  haveI hYτ : Invertible (Y.map (τ : S → S)) := by
    have h := Invertible.map
      (τ.mapMatrix : Matrix (Fin n) (Fin n) S ≃+* Matrix (Fin n) (Fin n) S) Y
    rwa [RingEquiv.mapMatrix_apply] at h
  have hYM : Y * (⅟Y * Z) = Z := by rw [← mul_assoc, mul_invOf_self, one_mul]
  have hL : (Y.map (τ : S → S)) * ((⅟Y * Z).map (τ : S → S)) = B * Z := by
    rw [← Matrix.map_mul, hYM, hZ]
  have hR : (Y.map (τ : S → S)) * (⅟Y * Z) = B * Z := by
    rw [hY, mul_assoc, hYM]
  have hcancel := congrArg (fun W => ⅟(Y.map (τ : S → S)) * W) (hL.trans hR.symm)
  simpa only [← mul_assoc, invOf_mul_self, one_mul] using hcancel

/-! ### The two copies of a fundamental matrix in the tensor square -/

/-- The left copy of a matrix in the tensor square. -/
def leftFundamental (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (Y : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (R ⊗[K] R) :=
  Y.map (fun x => x ⊗ₜ[K] (1 : R))

/-- The right copy of a matrix in the tensor square. -/
def rightFundamental (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (Y : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (R ⊗[K] R) :=
  Y.map (fun x => (1 : R) ⊗ₜ[K] x)

theorem leftFundamental_apply (Y : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    leftFundamental K Y i j = Y i j ⊗ₜ[K] (1 : R) := rfl

theorem rightFundamental_apply (Y : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    rightFundamental K Y i j = (1 : R) ⊗ₜ[K] Y i j := rfl

/-- **The torsor comparison matrix.**  Inside the tensor square the two copies of an invertible
fundamental solution matrix differ by an invertible matrix all of whose entries are constants.
This is the statement that makes the Picard--Vessiot ring a torsor under its Galois group. -/
theorem exists_tensor_comparison_matrix (σK : K ≃+* K) (σR : R ≃+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y) :
    ∃ Z : Matrix (Fin n) (Fin n) (R ⊗[K] R),
      leftFundamental K Y * Z = rightFundamental K Y ∧
      Z.map (differenceTensorEquiv σK σR hcompat) = Z ∧ IsUnit Z.det := by
  classical
  set incL : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeLeft : R →ₐ[K] (R ⊗[K] R)).toRingHom with hincL
  set incR : R →+* (R ⊗[K] R) :=
    (Algebra.TensorProduct.includeRight : R →ₐ[K] (R ⊗[K] R)).toRingHom with hincR
  have hLeq : leftFundamental K Y = Y.map (incL : R → (R ⊗[K] R)) := rfl
  have hReq : rightFundamental K Y = Y.map (incR : R → (R ⊗[K] R)) := rfl
  haveI hLinv : Invertible (leftFundamental K Y) := by
    rw [hLeq]
    have h := Invertible.map
      (incL.mapMatrix : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) (R ⊗[K] R)) Y
    rwa [RingHom.mapMatrix_apply] at h
  haveI hRinv : Invertible (rightFundamental K Y) := by
    rw [hReq]
    have h := Invertible.map
      (incR.mapMatrix : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) (R ⊗[K] R)) Y
    rwa [RingHom.mapMatrix_apply] at h
  set BT : Matrix (Fin n) (Fin n) (R ⊗[K] R) :=
    B.map (algebraMap K (R ⊗[K] R)) with hBT
  have hbaseL : ∀ b : K, incL (algebraMap K R b) = algebraMap K (R ⊗[K] R) b := by
    intro b
    exact (Algebra.TensorProduct.includeLeft : R →ₐ[K] (R ⊗[K] R)).commutes b
  have hbaseR : ∀ b : K, incR (algebraMap K R b) = algebraMap K (R ⊗[K] R) b := by
    intro b
    exact (Algebra.TensorProduct.includeRight : R →ₐ[K] (R ⊗[K] R)).commutes b
  have hLsys : (leftFundamental K Y).map (differenceTensorEquiv σK σR hcompat)
      = BT * leftFundamental K Y := by
    refine Matrix.ext fun i j => ?_
    have hstep : (differenceTensorEquiv σK σR hcompat) (Y i j ⊗ₜ[K] (1 : R))
        = (σR (Y i j)) ⊗ₜ[K] (1 : R) := by
      rw [differenceTensorEquiv_tmul, map_one]
    have hrow := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, leftFundamental, Matrix.mul_apply, hBT] at hrow ⊢
    rw [hstep, hrow]
    have hcast : (∑ x, (algebraMap K R) (B i x) * Y x j) ⊗ₜ[K] (1 : R)
        = incL (∑ x, (algebraMap K R) (B i x) * Y x j) := rfl
    rw [hcast, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hbaseL]
    rfl
  have hRsys : (rightFundamental K Y).map (differenceTensorEquiv σK σR hcompat)
      = BT * rightFundamental K Y := by
    refine Matrix.ext fun i j => ?_
    have hstep : (differenceTensorEquiv σK σR hcompat) ((1 : R) ⊗ₜ[K] Y i j)
        = (1 : R) ⊗ₜ[K] (σR (Y i j)) := by
      rw [differenceTensorEquiv_tmul, map_one]
    have hrow := congrFun (congrFun hY i) j
    simp only [Matrix.map_apply, rightFundamental, Matrix.mul_apply, hBT] at hrow ⊢
    rw [hstep, hrow]
    have hcast : (1 : R) ⊗ₜ[K] (∑ x, (algebraMap K R) (B i x) * Y x j)
        = incR (∑ x, (algebraMap K R) (B i x) * Y x j) := rfl
    rw [hcast, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hbaseR]
    rfl
  refine ⟨⅟(leftFundamental K Y) * rightFundamental K Y, ?_, ?_, ?_⟩
  · rw [← mul_assoc, mul_invOf_self, one_mul]
  · exact map_invOf_mul_eq_self (differenceTensorEquiv σK σR hcompat) BT
      (leftFundamental K Y) (rightFundamental K Y) hLsys hRsys
  · haveI : Invertible (⅟(leftFundamental K Y)) := invertibleInvOf
    have hdet : (⅟(leftFundamental K Y) * rightFundamental K Y).det
        = (⅟(leftFundamental K Y)).det * (rightFundamental K Y).det := Matrix.det_mul _ _
    rw [hdet]
    exact (Matrix.isUnit_det_of_invertible _).mul (Matrix.isUnit_det_of_invertible _)


end

end GaloisForLFunctions.HTGeometry
