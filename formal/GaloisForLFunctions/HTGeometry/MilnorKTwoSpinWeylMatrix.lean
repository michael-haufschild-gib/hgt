import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylKernel

/-!
# Signed-monomial quotient of the rank-four Spin-Weyl group

The concrete Spin action is converted to matrices.  Each rotor maps to its exact Steinberg Weyl
matrix.  Restriction to the rotor-generated subgroup surjects onto the generated signed-monomial
matrix group, whose elements have `±1` scales and determinant one; kernel is exactly `{1, -1}`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

/-- Matrix of the concrete Spin vector action in the standard coordinate basis. -/
def spinVectorMatrixRepresentation :
    spinGroup spinQ →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun s := LinearMap.toMatrix vectorBasis vectorBasis
    (spinVectorLinearEquiv s).toLinearMap
  map_one' := by
    rw [show spinVectorLinearEquiv (1 : spinGroup spinQ) = 1 from
      map_one spinVectorRepresentation]
    exact LinearMap.toMatrix_one vectorBasis
  map_mul' s t := by
    rw [show spinVectorLinearEquiv (s * t) =
        spinVectorLinearEquiv s * spinVectorLinearEquiv t from
      map_mul spinVectorRepresentation s t]
    exact LinearMap.toMatrix_mul vectorBasis _ _

@[simp] theorem spinVectorMatrixRepresentation_apply (s : spinGroup spinQ) :
    spinVectorMatrixRepresentation s =
      LinearMap.toMatrix vectorBasis vectorBasis
        (spinVectorLinearEquiv s).toLinearMap := rfl

theorem spinVectorMatrixRepresentation_weylLift (i j : Fin 4)
    (hij : i ≠ j) :
    spinVectorMatrixRepresentation (weylLift i j hij) =
      weylMatrix i j (1 : ℝˣ) := by
  ext r k
  rw [spinVectorMatrixRepresentation_apply, LinearMap.toMatrix_apply]
  rw [show vectorBasis k = basisVector k by
    exact Pi.basisFun_apply ℝ (Fin 4) k]
  change vectorBasis.repr
      (spinVectorLinearEquiv (weylLift i j hij) (basisVector k)) r = _
  rw [spinVectorLinearEquiv_weylLift_basis]
  simp only [weylVectorAction]
  split_ifs <;>
    by_cases hri : r = i <;>
    by_cases hrj : r = j <;>
    by_cases hrk : r = k <;>
    simp_all [weylMatrix, vectorBasis, basisVector, eq_comm]

theorem spinVectorMatrixRepresentation_eq_one_iff (s : spinGroup spinQ) :
    spinVectorMatrixRepresentation s = 1 ↔
      s = 1 ∨ s = centralNegOne := by
  rw [← spinVectorRepresentation_eq_one_iff]
  constructor
  · intro hs
    apply LinearEquiv.ext
    intro v
    have hlin : (spinVectorLinearEquiv s).toLinearMap =
        LinearMap.id := by
      apply (LinearMap.toMatrix vectorBasis vectorBasis).injective
      rw [LinearMap.toMatrix_id]
      exact hs
    exact LinearMap.congr_fun hlin v
  · intro hs
    change spinVectorLinearEquiv s = 1 at hs
    change LinearMap.toMatrix vectorBasis vectorBasis
      (spinVectorLinearEquiv s).toLinearMap = 1
    rw [hs]
    exact LinearMap.toMatrix_one vectorBasis

/-- Invertible matrix form of the Spin vector representation. -/
def spinVectorMatrixUnitRepresentation :
    spinGroup spinQ →* (Matrix (Fin 4) (Fin 4) ℝ)ˣ where
  toFun s :=
    { val := spinVectorMatrixRepresentation s
      inv := spinVectorMatrixRepresentation s⁻¹
      val_inv := by
        rw [← map_mul]
        rw [mul_inv_cancel]
        exact map_one spinVectorMatrixRepresentation
      inv_val := by
        rw [← map_mul]
        rw [inv_mul_cancel]
        exact map_one spinVectorMatrixRepresentation }
  map_one' := Units.ext (map_one spinVectorMatrixRepresentation)
  map_mul' s t := Units.ext (map_mul spinVectorMatrixRepresentation s t)

@[simp] theorem spinVectorMatrixUnitRepresentation_val (s : spinGroup spinQ) :
    ((spinVectorMatrixUnitRepresentation s :
      (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Matrix (Fin 4) (Fin 4) ℝ) =
        spinVectorMatrixRepresentation s := rfl

/-- Unit matrix of one signed Weyl rotor. -/
def spinWeylMatrixGenerator (i j : Fin 4) (hij : i ≠ j) :
    (Matrix (Fin 4) (Fin 4) ℝ)ˣ :=
  spinVectorMatrixUnitRepresentation (weylLift i j hij)

@[simp] theorem spinWeylMatrixGenerator_val (i j : Fin 4) (hij : i ≠ j) :
    (spinWeylMatrixGenerator i j hij : Matrix (Fin 4) (Fin 4) ℝ) =
      weylMatrix i j (1 : ℝˣ) :=
  spinVectorMatrixRepresentation_weylLift i j hij

theorem spinWeylMatrixGenerator_signedMonomial (i j : Fin 4) (hij : i ≠ j) :
    (spinWeylMatrixGenerator i j hij : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix (Equiv.swap i j)
        (steinbergWeylRootScale (i := i) (j := j) (1 : ℝˣ)) := by
  rw [spinWeylMatrixGenerator_val, weylMatrix_eq_signedMonomial hij]

theorem spinWeylMatrixGenerator_det (i j : Fin 4) (hij : i ≠ j) :
    Matrix.det (spinWeylMatrixGenerator i j hij :
      Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  rw [spinWeylMatrixGenerator_val, ← transvection_weyl hij]
  simp [Matrix.det_mul, Matrix.det_transvection_of_ne, hij, Ne.symm hij]

def IsSignedMonomialUnit (A : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ℝˣ),
    (∀ p, c p = 1 ∨ c p = -1) ∧
      (A : Matrix (Fin 4) (Fin 4) ℝ) = signedMonomialMatrix σ c

theorem signedMonomialMatrix_one :
    signedMonomialMatrix (1 : Equiv.Perm (Fin 4)) (fun _ => (1 : ℝˣ)) = 1 := by
  ext r s
  simp [signedMonomialMatrix, Matrix.one_apply]

theorem signedMonomialMatrix_inv_data
    (A : (Matrix (Fin 4) (Fin 4) ℝ)ˣ)
    (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ℝˣ)
    (hA : (A : Matrix (Fin 4) (Fin 4) ℝ) = signedMonomialMatrix σ c) :
    ((A⁻¹ : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹) := by
  let B := signedMonomialMatrix σ.symm (fun p => (c (σ.symm p))⁻¹)
  have hBA : B * (A : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
    rw [hA, signedMonomialMatrix_mul]
    ext r s
    simp [signedMonomialMatrix, Matrix.one_apply]
  have hB : B = A.inv := by
    calc
      B = B * 1 := by rw [mul_one]
      _ = B * ((A : Matrix (Fin 4) (Fin 4) ℝ) * A.inv) := by
        rw [A.val_inv]
      _ = (B * (A : Matrix (Fin 4) (Fin 4) ℝ)) * A.inv := by
        rw [mul_assoc]
      _ = A.inv := by rw [hBA, one_mul]
  exact hB.symm

theorem IsSignedMonomialUnit.one :
    IsSignedMonomialUnit (1 : (Matrix (Fin 4) (Fin 4) ℝ)ˣ) := by
  exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, signedMonomialMatrix_one.symm⟩

theorem IsSignedMonomialUnit.mul {A B : (Matrix (Fin 4) (Fin 4) ℝ)ˣ}
    (hA : IsSignedMonomialUnit A) (hB : IsSignedMonomialUnit B) :
    IsSignedMonomialUnit (A * B) := by
  obtain ⟨σ, c, hc, hAc⟩ := hA
  obtain ⟨τ, d, hd, hBd⟩ := hB
  refine ⟨τ.trans σ, fun p => c (τ p) * d p, ?_, ?_⟩
  · intro p
    rcases hc (τ p) with hc' | hc' <;>
      rcases hd p with hd' | hd' <;>
      simp [hc', hd']
  · change (A : Matrix (Fin 4) (Fin 4) ℝ) *
      (B : Matrix (Fin 4) (Fin 4) ℝ) = _
    rw [hAc, hBd, signedMonomialMatrix_mul]

theorem IsSignedMonomialUnit.inv {A : (Matrix (Fin 4) (Fin 4) ℝ)ˣ}
    (hA : IsSignedMonomialUnit A) : IsSignedMonomialUnit A⁻¹ := by
  obtain ⟨σ, c, hc, hAc⟩ := hA
  refine ⟨σ.symm, fun p => (c (σ.symm p))⁻¹, ?_,
    signedMonomialMatrix_inv_data A σ c hAc⟩
  intro p
  rcases hc (σ.symm p) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- Signed-monomial matrix group generated by the rank-four Weyl rotors. -/
def generatedSignedMonomialSubgroup :
    Subgroup (Matrix (Fin 4) (Fin 4) ℝ)ˣ :=
  Subgroup.closure {A | ∃ (i j : Fin 4) (hij : i ≠ j),
    A = spinWeylMatrixGenerator i j hij}

theorem generatedSignedMonomialSubgroup_det_one
    (A : generatedSignedMonomialSubgroup) :
    Matrix.det (A.1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  rcases A with ⟨A, hA⟩
  change Matrix.det (A : Matrix (Fin 4) (Fin 4) ℝ) = 1
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      exact spinWeylMatrixGenerator_det i j hij
  | one => simp
  | mul x y _ _ hx hy =>
      rw [Units.val_mul, Matrix.det_mul, hx, hy, one_mul]
  | inv x _ hx =>
      have hdet := congrArg Matrix.det x.inv_val
      rw [Matrix.det_mul, hx, Matrix.det_one, mul_one] at hdet
      simpa using hdet

theorem generatedSignedMonomialSubgroup_isSignedMonomial
    (A : generatedSignedMonomialSubgroup) : IsSignedMonomialUnit A.1 := by
  rcases A with ⟨A, hA⟩
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      refine ⟨Equiv.swap i j,
        steinbergWeylRootScale (i := i) (j := j) (1 : ℝˣ), ?_,
        spinWeylMatrixGenerator_signedMonomial i j hij⟩
      intro p
      by_cases hpi : p = i
      · subst p
        simp [steinbergWeylRootScale]
      · by_cases hpj : p = j
        · subst p
          simp [steinbergWeylRootScale, Ne.symm hij]
        · simp [steinbergWeylRootScale, hpi, hpj]
  | one => exact IsSignedMonomialUnit.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem spinWeyl_matrix_mem_generated (s : spinWeylSubgroup) :
    spinVectorMatrixUnitRepresentation s.1 ∈ generatedSignedMonomialSubgroup := by
  rcases s with ⟨s, hs⟩
  change spinVectorMatrixUnitRepresentation s ∈ generatedSignedMonomialSubgroup
  induction hs using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩
  | one =>
      rw [map_one]
      exact generatedSignedMonomialSubgroup.one_mem
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact generatedSignedMonomialSubgroup.mul_mem hx hy
  | inv x _ hx =>
      rw [map_inv]
      exact generatedSignedMonomialSubgroup.inv_mem hx

/-- Canonical surjection from Spin-Weyl rotors onto their signed-monomial matrix group. -/
def spinWeylMatrixRepresentation :
    spinWeylSubgroup →* generatedSignedMonomialSubgroup :=
  (spinVectorMatrixUnitRepresentation.comp spinWeylSubgroup.subtype).codRestrict
    generatedSignedMonomialSubgroup spinWeyl_matrix_mem_generated

theorem spinWeylMatrixRepresentation_surjective :
    Function.Surjective spinWeylMatrixRepresentation := by
  intro A
  rcases A with ⟨A, hA⟩
  change ∃ s, spinWeylMatrixRepresentation s = ⟨A, hA⟩
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      exact ⟨⟨weylLift i j hij,
        weylLift_mem_spinWeylSubgroup i j hij⟩, rfl⟩
  | one => exact ⟨1, map_one spinWeylMatrixRepresentation⟩
  | mul x y _ _ hx hy =>
      obtain ⟨sx, hsx⟩ := hx
      obtain ⟨sy, hsy⟩ := hy
      refine ⟨sx * sy, ?_⟩
      apply Subtype.ext
      rw [map_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val hsx)
        (congrArg Subtype.val hsy)
  | inv x _ hx =>
      obtain ⟨sx, hsx⟩ := hx
      refine ⟨sx⁻¹, ?_⟩
      apply Subtype.ext
      rw [map_inv]
      exact congrArg Inv.inv (congrArg Subtype.val hsx)

def centralNegOneSpinWeyl : spinWeylSubgroup :=
  ⟨centralNegOne, centralNegOne_mem_spinWeylSubgroup⟩

/-- Exact kernel of the generated signed-monomial quotient. -/
theorem spinWeylMatrixRepresentation_eq_one_iff (s : spinWeylSubgroup) :
    spinWeylMatrixRepresentation s = 1 ↔
      s = 1 ∨ s = centralNegOneSpinWeyl := by
  have hunit : spinVectorMatrixUnitRepresentation s.1 = 1 ↔
      s.1 = 1 ∨ s.1 = centralNegOne := by
    rw [← Units.val_inj, spinVectorMatrixUnitRepresentation_val,
      Units.val_one, spinVectorMatrixRepresentation_eq_one_iff]
  constructor
  · intro hs
    have hsunit : spinVectorMatrixUnitRepresentation s.1 = 1 :=
      congrArg Subtype.val hs
    rcases hunit.mp hsunit with hs | hs
    · exact Or.inl (Subtype.ext hs)
    · exact Or.inr (Subtype.ext hs)
  · intro hs
    apply Subtype.ext
    apply hunit.mpr
    rcases hs with hs | hs
    · exact Or.inl (congrArg Subtype.val hs)
    · exact Or.inr (congrArg Subtype.val hs)

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end
