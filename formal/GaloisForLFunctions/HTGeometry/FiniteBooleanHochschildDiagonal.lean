import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm
import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint
import GaloisForLFunctions.RHTower.FunctionTensorProduct
import GaloisForLFunctions.RHTower.CyclicBarTensorOperators
import GaloisForLFunctions.RHTower.CyclicBarProjectiveContinuity
import GaloisForLFunctions.HTGeometry.AlternatingContraction
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Finite Boolean separability diagonals

Algebraic and sharp projective-seminorm layer of the canonical diagonal of a finite Boolean
function algebra.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Finite Boolean spectrum. -/
abbrev FiniteBooleanCube (I : Type*) := I → Bool

/-- Complex function algebra on a finite Boolean spectrum. -/
abbrev FiniteBooleanAlgebra (I : Type*) := FiniteBooleanCube I → ℂ

/-- Atomic idempotent at one Boolean configuration. -/
def finiteBooleanAtom (x : FiniteBooleanCube I) : FiniteBooleanAlgebra I :=
  fun y => if y = x then 1 else 0

/-- Canonical finite Boolean separability diagonal. -/
def finiteBooleanDiagonal :
    FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I :=
  ∑ x : FiniteBooleanCube I, finiteBooleanAtom x ⊗ₜ[ℂ] finiteBooleanAtom x

/-- Pointwise multiplication, as a bilinear map. -/
def finiteBooleanMultiplicationBilinear :
    FiniteBooleanAlgebra I →ₗ[ℂ] FiniteBooleanAlgebra I →ₗ[ℂ] FiniteBooleanAlgebra I :=
  LinearMap.mk₂ ℂ (fun f g x => f x * g x)
    (fun f g h => by ext x; simp [add_mul])
    (fun c f g => by ext x; simp [mul_assoc])
    (fun f g h => by ext x; simp [mul_add])
    (fun c f g => by ext x; simp [mul_left_comm])

/-- Multiplication on the algebraic tensor product. -/
def finiteBooleanMultiplication :
    (FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I) →ₗ[ℂ] FiniteBooleanAlgebra I :=
  TensorProduct.lift finiteBooleanMultiplicationBilinear

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem finiteBooleanMultiplication_tmul (f g : FiniteBooleanAlgebra I) :
    finiteBooleanMultiplication (f ⊗ₜ[ℂ] g) = f * g := by
  rfl

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem finiteBooleanMultiplicationBilinear_apply
    (f g : FiniteBooleanAlgebra I) (x : FiniteBooleanCube I) :
    finiteBooleanMultiplicationBilinear f g x = f x * g x := rfl

/-- Multiplying the diagonal gives the unit. -/
theorem finiteBooleanMultiplication_diagonal :
    finiteBooleanMultiplication (finiteBooleanDiagonal (I := I)) = 1 := by
  classical
  ext y
  simp [finiteBooleanDiagonal, finiteBooleanMultiplication, finiteBooleanMultiplicationBilinear,
    finiteBooleanAtom]

/-- Pointwise left multiplication by a fixed Boolean observable. -/
def finiteBooleanMulLeft (a : FiniteBooleanAlgebra I) :
    FiniteBooleanAlgebra I →ₗ[ℂ] FiniteBooleanAlgebra I :=
  LinearMap.mulLeft ℂ a

/-- Left action on the first tensor factor. -/
def finiteBooleanTensorLeft (a : FiniteBooleanAlgebra I) :
    (FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I) →ₗ[ℂ]
      (FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I) :=
  TensorProduct.map (finiteBooleanMulLeft a) LinearMap.id

/-- Right action on the second tensor factor. -/
def finiteBooleanTensorRight (a : FiniteBooleanAlgebra I) :
    (FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I) →ₗ[ℂ]
      (FiniteBooleanAlgebra I ⊗[ℂ] FiniteBooleanAlgebra I) :=
  TensorProduct.map LinearMap.id (finiteBooleanMulLeft a)

/-- The canonical diagonal centralizes every Boolean observable. -/
theorem finiteBooleanDiagonal_centralizes (a : FiniteBooleanAlgebra I) :
    finiteBooleanTensorLeft a (finiteBooleanDiagonal (I := I)) =
      finiteBooleanTensorRight a (finiteBooleanDiagonal (I := I)) := by
  classical
  apply GaloisForLFunctions.RHTower.functionTensorProductHom_injective
  ext z
  rcases z with ⟨x, y⟩
  simp only [finiteBooleanTensorLeft, finiteBooleanTensorRight, finiteBooleanDiagonal,
    finiteBooleanMulLeft, map_sum, TensorProduct.map_tmul,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    Finset.sum_apply]
  change (∑ c, (a * finiteBooleanAtom c) x * finiteBooleanAtom c y) =
    ∑ c, finiteBooleanAtom c x * (a * finiteBooleanAtom c) y
  by_cases hxy : x = y
  · subst y
    simp [finiteBooleanAtom]
  · simp [finiteBooleanAtom, hxy]

/-- A Walsh character regarded as an element of the Boolean function algebra. -/
def finiteBooleanWalsh (B : Finset I) : FiniteBooleanAlgebra I :=
  orientationWalshCharacter B

/-- Fourier--Walsh expansion of the canonical Boolean diagonal. -/
theorem finiteBooleanDiagonal_eq_walsh :
    finiteBooleanDiagonal (I := I) =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ •
        ∑ B : Finset I, finiteBooleanWalsh B ⊗ₜ[ℂ] finiteBooleanWalsh B := by
  classical
  apply GaloisForLFunctions.RHTower.functionTensorProductHom_injective
  ext z
  rcases z with ⟨x, y⟩
  simp only [finiteBooleanDiagonal, map_sum,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    LinearMapClass.map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    finiteBooleanWalsh]
  rw [sum_orientationWalshCharacter_mul_eq]
  by_cases hxy : x = y
  · subst y
    simp [finiteBooleanAtom]
  · simp [finiteBooleanAtom, hxy]

/-- Every finite Boolean Walsh character has supremum norm one. -/
theorem norm_finiteBooleanWalsh (B : Finset I) :
    ‖finiteBooleanWalsh B‖ = 1 := by
  classical
  rw [Pi.norm_def]
  have hpoint : ∀ x : FiniteBooleanCube I, ‖finiteBooleanWalsh B x‖₊ = 1 := by
    intro x
    apply NNReal.eq
    have hsign : ∀ i : I, ‖primeDirichletSign (x i)‖ = 1 := by
      intro i
      cases x i <;> simp [primeDirichletSign]
    simp [finiteBooleanWalsh, orientationWalshCharacter, hsign]
  simp_rw [hpoint]
  rw [Finset.sup_const Finset.univ_nonempty]
  rfl

private theorem projTensorSeminorm_sum_le
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) {α : Type*} (s : Finset α) (f : α → E) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (map_add_le_add p (f a) (∑ i ∈ s, f i)) (add_le_add le_rfl ih)

/-- Sharp projective norm of the finite Boolean separability diagonal. -/
theorem projTensorSeminorm_finiteBooleanDiagonal :
    projTensorSeminorm (normSeminorm ℂ (FiniteBooleanAlgebra I))
        (normSeminorm ℂ (FiniteBooleanAlgebra I)) (finiteBooleanDiagonal (I := I)) = 1 := by
  classical
  let p := normSeminorm ℂ (FiniteBooleanAlgebra I)
  let P := projTensorSeminorm p p
  have hupper : P (finiteBooleanDiagonal (I := I)) ≤ 1 := by
    rw [finiteBooleanDiagonal_eq_walsh]
    rw [map_smul_eq_mul]
    have hsum := projTensorSeminorm_sum_le P (Finset.univ : Finset (Finset I))
      (fun B => finiteBooleanWalsh B ⊗ₜ[ℂ] finiteBooleanWalsh B)
    have hpure : ∀ B : Finset I,
        P (finiteBooleanWalsh B ⊗ₜ[ℂ] finiteBooleanWalsh B) ≤ 1 := by
      intro B
      have h := projTensorSeminorm_tmul_le p p (finiteBooleanWalsh B) (finiteBooleanWalsh B)
      rw [show p (finiteBooleanWalsh B) = 1 by
        exact norm_finiteBooleanWalsh B, one_mul] at h
      exact h
    calc
      ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ *
          P (∑ B : Finset I, finiteBooleanWalsh B ⊗ₜ[ℂ] finiteBooleanWalsh B)
          ≤ ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ *
              ∑ B : Finset I, P (finiteBooleanWalsh B ⊗ₜ[ℂ] finiteBooleanWalsh B) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ ≤ ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ * ∑ _B : Finset I, (1 : ℝ) := by
        gcongr with B
        exact hpure B
      _ = 1 := by
        rw [norm_inv, norm_pow, Complex.norm_ofNat, Finset.sum_const, Finset.card_univ,
          Fintype.card_finset, nsmul_eq_mul]
        norm_num
  have hlower : 1 ≤ P (finiteBooleanDiagonal (I := I)) := by
    have hmul := projTensorSeminorm_lift_le p p p finiteBooleanMultiplicationBilinear
      (C := 1) (by norm_num) (fun f g => by
        change ‖f * g‖ ≤ 1 * (‖f‖ * ‖g‖)
        simpa using norm_mul_le f g)
      (finiteBooleanDiagonal (I := I))
    rw [show TensorProduct.lift finiteBooleanMultiplicationBilinear =
        finiteBooleanMultiplication (I := I) from rfl,
      finiteBooleanMultiplication_diagonal] at hmul
    simpa [p, P] using hmul
  exact le_antisymm hupper hlower

/-! ## The all-degree algebraic contraction -/

/-- Atomic basis of the finite Boolean function algebra. -/
def finiteBooleanAtomBasis :
    Module.Basis (FiniteBooleanCube I) ℂ (FiniteBooleanAlgebra I) :=
  Finsupp.basisSingleOne.map
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (FiniteBooleanCube I))

@[simp]
theorem finiteBooleanAtomBasis_apply (x : FiniteBooleanCube I) :
    finiteBooleanAtomBasis x = finiteBooleanAtom x := by
  classical
  ext y
  by_cases hxy : x = y
  · subst y
    simp [finiteBooleanAtomBasis, finiteBooleanAtom,
      Finsupp.linearEquivFunOnFinite_apply, Finsupp.single_apply]
  · have hyx : y ≠ x := Ne.symm hxy
    simp [finiteBooleanAtomBasis, finiteBooleanAtom,
      Finsupp.linearEquivFunOnFinite_apply, Finsupp.single_apply, hxy, hyx]

/-- Tensor-product atomic basis in Hochschild degree `n`. -/
def finiteBooleanHochschildBasis (n : ℕ) :
    Module.Basis (Fin (n + 1) → FiniteBooleanCube I) ℂ
      (CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n) :=
  Basis.piTensorProduct fun _ => finiteBooleanAtomBasis (I := I)

@[simp]
theorem finiteBooleanHochschildBasis_apply (n : ℕ)
    (x : Fin (n + 1) → FiniteBooleanCube I) :
    finiteBooleanHochschildBasis n x =
      PiTensorProduct.tprod ℂ (fun j => finiteBooleanAtom (x j)) := by
  rw [finiteBooleanHochschildBasis, Basis.piTensorProduct_apply]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext j
  exact finiteBooleanAtomBasis_apply (x j)

/-- Extra degeneracy induced by the separability diagonal: duplicate the first atomic
configuration. -/
def finiteBooleanHochschildContraction (n : ℕ) :
    CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n →ₗ[ℂ]
      CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1) :=
  (finiteBooleanHochschildBasis n).constr ℂ fun x =>
    finiteBooleanHochschildBasis (n + 1) (Fin.cons (x 0) x)

@[simp]
theorem finiteBooleanHochschildContraction_basis (n : ℕ)
    (x : Fin (n + 1) → FiniteBooleanCube I) :
    finiteBooleanHochschildContraction n (finiteBooleanHochschildBasis n x) =
      finiteBooleanHochschildBasis (n + 1) (Fin.cons (x 0) x) := by
  exact Module.Basis.constr_basis (finiteBooleanHochschildBasis n) ℂ _ x

/-- The first Hochschild face cancels the Boolean separability contraction. -/
theorem cyclicBarFace_zero_comp_finiteBooleanHochschildContraction (n : ℕ) :
    cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) (0 : Fin (n + 2)) ∘ₗ
        finiteBooleanHochschildContraction n =
      LinearMap.id (R := ℂ) (M := CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n) := by
  apply Module.Basis.ext (finiteBooleanHochschildBasis n)
    (f₁ := cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) (0 : Fin (n + 2)) ∘ₗ
      finiteBooleanHochschildContraction n)
    (f₂ := LinearMap.id (R := ℂ) (M := CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n))
  intro x
  rw [LinearMap.comp_apply, finiteBooleanHochschildContraction_basis,
    finiteBooleanHochschildBasis_apply, cyclicBarFace_tprod,
    finiteBooleanHochschildBasis_apply, LinearMap.id_apply]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext j
  ext y
  rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl]
  rw [cyclicBarFaceTuple, Fin.lastCases_castSucc]
  change cyclicBarFaceNonwrapTuple (0 : Fin (n + 1))
      (fun k => finiteBooleanAtom ((Fin.cons (x 0) x :
        Fin (n + 2) → FiniteBooleanCube I) k)) j y = finiteBooleanAtom (x j) y
  cases j using Fin.cases with
  | zero => simp [cyclicBarFaceNonwrapTuple, finiteBooleanAtom]
  | succ j => simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, finiteBooleanAtom]

@[simp]
theorem finiteBooleanAtom_mul (x y : FiniteBooleanCube I) :
    finiteBooleanAtom x * finiteBooleanAtom y =
      if x = y then finiteBooleanAtom x else 0 := by
  classical
  ext z
  by_cases hxy : x = y
  · subst y
    simp [finiteBooleanAtom, Pi.mul_apply]
  · by_cases hzx : z = x
    · subst z
      simp [finiteBooleanAtom, Pi.mul_apply, hxy]
    · simp [finiteBooleanAtom, Pi.mul_apply, hxy, hzx]

/-- Compatibility of an atomic configuration with a cyclic-bar face. -/
def finiteBooleanFaceCompatible {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → FiniteBooleanCube I) : Prop :=
  Fin.lastCases (x (Fin.last (n + 1)) = x 0)
    (fun j => x j.castSucc = x j.succ) i

/-- Configuration obtained by deleting the right factor of a compatible face. -/
def finiteBooleanFaceConfig {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → FiniteBooleanCube I) :
    Fin (n + 1) → FiniteBooleanCube I :=
  Fin.lastCases (Fin.removeNth (Fin.last (n + 1)) x)
    (fun j => Fin.removeNth j.succ x) i

/-- A compatible cyclic-bar face contracts the corresponding atomic tensor. -/
theorem cyclicBarFace_finiteBooleanHochschildBasis_of_compatible {n : ℕ}
    (i : Fin (n + 2)) (x : Fin (n + 2) → FiniteBooleanCube I)
    (h : finiteBooleanFaceCompatible i x) :
    cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i
        (finiteBooleanHochschildBasis (n + 1) x) =
      finiteBooleanHochschildBasis n (finiteBooleanFaceConfig i x) := by
  classical
  rw [finiteBooleanHochschildBasis_apply, cyclicBarFace_tprod]
  induction i using Fin.lastCases with
  | last =>
      simp only [finiteBooleanFaceCompatible, Fin.lastCases_last] at h
      simp only [finiteBooleanFaceConfig, Fin.lastCases_last, cyclicBarFaceTuple,
        Fin.lastCases_last, finiteBooleanHochschildBasis_apply]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j = 0
      · subst j
        simp only [cyclicBarFaceWrapTuple, Function.update_self, finiteBooleanAtom_mul,
          Fin.removeNth_last]
        rw [if_pos h, h]
        rfl
      · simp only [cyclicBarFaceWrapTuple, Function.update_of_ne hj,
          Fin.removeNth_last]
        rfl
  | cast i =>
      simp only [finiteBooleanFaceCompatible, Fin.lastCases_castSucc] at h
      simp only [finiteBooleanFaceConfig, Fin.lastCases_castSucc, cyclicBarFaceTuple,
        Fin.lastCases_castSucc, finiteBooleanHochschildBasis_apply]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j = i
      · subst j
        simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, h]
      · simp [cyclicBarFaceNonwrapTuple, Fin.removeNth, hj]

/-- An incompatible cyclic-bar face kills the corresponding atomic tensor. -/
theorem cyclicBarFace_finiteBooleanHochschildBasis_of_incompatible {n : ℕ}
    (i : Fin (n + 2)) (x : Fin (n + 2) → FiniteBooleanCube I)
    (h : ¬finiteBooleanFaceCompatible i x) :
    cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i
        (finiteBooleanHochschildBasis (n + 1) x) = 0 := by
  classical
  rw [finiteBooleanHochschildBasis_apply, cyclicBarFace_tprod]
  induction i using Fin.lastCases with
  | last =>
      simp only [finiteBooleanFaceCompatible, Fin.lastCases_last] at h
      apply MultilinearMap.map_coord_zero (PiTensorProduct.tprod ℂ) 0
      simp [cyclicBarFaceTuple, cyclicBarFaceWrapTuple, h]
  | cast i =>
      simp only [finiteBooleanFaceCompatible, Fin.lastCases_castSucc] at h
      apply MultilinearMap.map_coord_zero (PiTensorProduct.tprod ℂ) i
      simp [cyclicBarFaceTuple, cyclicBarFaceNonwrapTuple, h]

theorem finiteBooleanFaceCompatible_succ_cons {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → FiniteBooleanCube I) :
    finiteBooleanFaceCompatible i.succ (Fin.cons (x 0) x) ↔
      finiteBooleanFaceCompatible i x := by
  induction i using Fin.lastCases with
  | last =>
      simp [finiteBooleanFaceCompatible]
  | cast i =>
      unfold finiteBooleanFaceCompatible
      rw [show i.castSucc.succ = i.succ.castSucc by rfl,
        Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      simp

theorem finiteBooleanFaceConfig_zero {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → FiniteBooleanCube I) :
    finiteBooleanFaceConfig i x 0 = x 0 := by
  induction i using Fin.lastCases with
  | last =>
      unfold finiteBooleanFaceConfig
      rw [Fin.lastCases_last]
      change Fin.init x 0 = x 0
      rfl
  | cast i => simp [finiteBooleanFaceConfig, Fin.removeNth]

theorem finiteBooleanFaceConfig_succ_cons {n : ℕ} (i : Fin (n + 2))
    (x : Fin (n + 2) → FiniteBooleanCube I) :
    finiteBooleanFaceConfig i.succ (Fin.cons (x 0) x) =
      Fin.cons (x 0) (finiteBooleanFaceConfig i x) := by
  induction i using Fin.lastCases with
  | last =>
      unfold finiteBooleanFaceConfig
      rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) by rfl,
        Fin.lastCases_last, Fin.lastCases_last]
      change Fin.removeNth (Fin.last (n + 1)).succ
          (Fin.cons (x 0) x : Fin (n + 3) → FiniteBooleanCube I) =
        (Fin.cons (x 0) (Fin.removeNth (Fin.last (n + 1)) x) :
          Fin (n + 2) → FiniteBooleanCube I)
      exact removeNth_succ_cons (x 0) x (Fin.last (n + 1))
  | cast i =>
      unfold finiteBooleanFaceConfig
      rw [show i.castSucc.succ = i.succ.castSucc by rfl,
        Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      change Fin.removeNth i.succ.succ
          (Fin.cons (x 0) x : Fin (n + 3) → FiniteBooleanCube I) =
        (Fin.cons (x 0) (Fin.removeNth i.succ x) :
          Fin (n + 2) → FiniteBooleanCube I)
      exact removeNth_succ_cons (x 0) x i.succ

/-- Every later face commutes past the separability contraction with the expected shift. -/
theorem cyclicBarFace_succ_comp_finiteBooleanHochschildContraction (n : ℕ)
    (i : Fin (n + 2)) :
    cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i.succ ∘ₗ
        finiteBooleanHochschildContraction (n + 1) =
      finiteBooleanHochschildContraction n ∘ₗ
        cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i := by
  apply Module.Basis.ext (finiteBooleanHochschildBasis (n + 1))
    (f₁ := cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i.succ ∘ₗ
      finiteBooleanHochschildContraction (n + 1))
    (f₂ := finiteBooleanHochschildContraction n ∘ₗ
      cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i)
  intro x
  rw [LinearMap.comp_apply, finiteBooleanHochschildContraction_basis,
    LinearMap.comp_apply]
  by_cases h : finiteBooleanFaceCompatible i x
  · have hs : finiteBooleanFaceCompatible i.succ (Fin.cons (x 0) x) :=
      (finiteBooleanFaceCompatible_succ_cons i x).2 h
    rw [cyclicBarFace_finiteBooleanHochschildBasis_of_compatible i.succ _ hs,
      cyclicBarFace_finiteBooleanHochschildBasis_of_compatible i x h,
      finiteBooleanHochschildContraction_basis,
      finiteBooleanFaceConfig_succ_cons, finiteBooleanFaceConfig_zero]
  · have hs : ¬finiteBooleanFaceCompatible i.succ (Fin.cons (x 0) x) := by
      exact fun hs => h ((finiteBooleanFaceCompatible_succ_cons i x).1 hs)
    rw [cyclicBarFace_finiteBooleanHochschildBasis_of_incompatible i.succ _ hs,
      cyclicBarFace_finiteBooleanHochschildBasis_of_incompatible i x h, map_zero]

/-- Hochschild boundary on the genuine cyclic-bar tensor power. -/
def finiteBooleanHochschildBoundary (n : ℕ) :
    CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1) →ₗ[ℂ]
      CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n :=
  ∑ i : Fin (n + 2), ((-1 : ℂ) ^ (i : ℕ)) •
    cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i

@[simp]
theorem finiteBooleanHochschildBoundary_apply (n : ℕ)
    (z : CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1)) :
    finiteBooleanHochschildBoundary n z =
      ∑ i : Fin (n + 2), ((-1 : ℂ) ^ (i : ℕ)) •
        cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i z := by
  simp [finiteBooleanHochschildBoundary]

/-- The separability contraction contracts every positive Hochschild degree. -/
theorem finiteBooleanHochschildContraction_identity (n : ℕ) :
    finiteBooleanHochschildBoundary (n + 1) ∘ₗ
          finiteBooleanHochschildContraction (n + 1) +
        finiteBooleanHochschildContraction n ∘ₗ
          finiteBooleanHochschildBoundary n =
      LinearMap.id (R := ℂ)
        (M := CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1)) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    finiteBooleanHochschildBoundary_apply]
  rw [Fin.sum_univ_succ]
  have hzero :
      cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) (0 : Fin (n + 3))
          (finiteBooleanHochschildContraction (n + 1) z) = z := by
    have h := congrArg (fun f => f z)
      (cyclicBarFace_zero_comp_finiteBooleanHochschildContraction
        (I := I) (n + 1))
    simpa [LinearMap.comp_apply] using h
  rw [hzero]
  simp only [Fin.val_zero, pow_zero, one_smul, map_sum, map_smul]
  have hterm : ∀ i : Fin (n + 2),
      (-1 : ℂ) ^ ((i.succ : Fin (n + 3)) : ℕ) •
          cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i.succ
            (finiteBooleanHochschildContraction (n + 1) z) =
        -((-1 : ℂ) ^ (i : ℕ) •
          finiteBooleanHochschildContraction n
            (cyclicBarFace (R := ℂ) (A := FiniteBooleanAlgebra I) i z)) := by
    intro i
    have hface := congrArg (fun f => f z)
      (cyclicBarFace_succ_comp_finiteBooleanHochschildContraction
        (I := I) n i)
    rw [Fin.val_succ, pow_succ]
    simp only [LinearMap.comp_apply] at hface
    rw [hface, mul_smul]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib]
  abel

/-! ## Dimension-free projective bound -/

/-- Walsh presentation of the separability contraction on an elementary tensor. -/
def finiteBooleanWalshContractionTuple {n : ℕ} (B : Finset I)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    Fin (n + 2) → FiniteBooleanAlgebra I :=
  Fin.cons (finiteBooleanWalsh B)
    (Fin.cons (finiteBooleanWalsh B * a 0) (Fin.tail a))

theorem finiteBooleanWalshContractionTuple_update_zero {n : ℕ} (B : Finset I)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) (z : FiniteBooleanAlgebra I) :
    finiteBooleanWalshContractionTuple B (Function.update a 0 z) =
      Function.update (finiteBooleanWalshContractionTuple B a) 1
        (finiteBooleanWalsh B * z) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [finiteBooleanWalshContractionTuple]
  | succ j =>
      cases j using Fin.cases with
      | zero => simp [finiteBooleanWalshContractionTuple]
      | succ j =>
          simp only [finiteBooleanWalshContractionTuple, Fin.cons_succ, Fin.tail]
          rw [Function.update_of_ne (Fin.ne_of_gt (by simp))]
          rfl

theorem finiteBooleanWalshContractionTuple_update_succ {n : ℕ} (B : Finset I)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) (k : Fin n)
    (z : FiniteBooleanAlgebra I) :
    finiteBooleanWalshContractionTuple B (Function.update a k.succ z) =
      Function.update (finiteBooleanWalshContractionTuple B a) k.succ.succ z := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp only [finiteBooleanWalshContractionTuple, Fin.cons_zero]
      rw [Function.update_of_ne (Fin.ne_of_lt (by simp))]
      rw [Fin.cons_zero]
  | succ j =>
      cases j using Fin.cases with
      | zero =>
          simp only [finiteBooleanWalshContractionTuple, Fin.cons_succ, Fin.cons_zero]
          have hne : (0 : Fin (n + 1)).succ ≠ k.succ.succ := by
            intro e
            have he := congrArg Fin.val e
            simp at he
          have hne₀ : (0 : Fin (n + 1)) ≠ k.succ := Fin.ne_of_lt (by simp)
          rw [Function.update_of_ne hne, Function.update_of_ne hne₀]
          rfl
      | succ j =>
          simp only [finiteBooleanWalshContractionTuple, Fin.cons_succ, Fin.tail]
          by_cases h : j = k
          · subst j
            simp
          · have h₁ : j.succ ≠ k.succ := by
              intro e
              apply h
              apply Fin.ext
              exact Nat.succ.inj (congrArg Fin.val e)
            have h₂ : j.succ.succ ≠ k.succ.succ :=
              fun e => h₁ (Fin.ext (Nat.succ.inj (congrArg Fin.val e)))
            rw [Function.update_of_ne h₁, Function.update_of_ne h₂]
            rfl

/-- Multilinear Walsh-average formula for the separability contraction. -/
def finiteBooleanWalshContractionMultilinear (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin (n + 1) ↦ FiniteBooleanAlgebra I)
      (CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1)) :=
  MultilinearMap.mk'
    (fun a ↦ ((2 : ℂ) ^ Fintype.card I)⁻¹ •
      ∑ B : Finset I, PiTensorProduct.tprod ℂ
        (finiteBooleanWalshContractionTuple B a))
    (by
      intro a k u v
      cases k using Fin.cases with
      | zero =>
          simp_rw [finiteBooleanWalshContractionTuple_update_zero,
            mul_add, (PiTensorProduct.tprod ℂ).map_update_add]
          rw [Finset.sum_add_distrib, smul_add]
      | succ k =>
          simp_rw [finiteBooleanWalshContractionTuple_update_succ,
            (PiTensorProduct.tprod ℂ).map_update_add]
          rw [Finset.sum_add_distrib, smul_add])
    (by
      intro a k r u
      cases k using Fin.cases with
      | zero =>
          simp_rw [finiteBooleanWalshContractionTuple_update_zero,
            mul_smul_comm, (PiTensorProduct.tprod ℂ).map_update_smul]
          rw [← Finset.smul_sum, smul_comm]
      | succ k =>
          simp_rw [finiteBooleanWalshContractionTuple_update_succ,
            (PiTensorProduct.tprod ℂ).map_update_smul]
          rw [← Finset.smul_sum, smul_comm])

@[simp]
theorem norm_finiteBooleanWalsh_apply (B : Finset I) (x : FiniteBooleanCube I) :
    ‖finiteBooleanWalsh B x‖ = 1 := by
  classical
  have hsign : ∀ i : I, ‖primeDirichletSign (x i)‖ = 1 := by
    intro i
    cases x i <;> simp [primeDirichletSign]
  simp [finiteBooleanWalsh, orientationWalshCharacter, hsign]

@[simp]
theorem norm_finiteBooleanWalsh_mul (B : Finset I) (f : FiniteBooleanAlgebra I) :
    ‖finiteBooleanWalsh B * f‖ = ‖f‖ := by
  classical
  have hsquare : finiteBooleanWalsh B * finiteBooleanWalsh B = 1 := by
    ext x
    simp only [finiteBooleanWalsh, orientationWalshCharacter, Pi.mul_apply,
      Pi.one_apply]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i hi
    cases x i <;> norm_num [primeDirichletSign]
  apply le_antisymm
  · simpa [norm_finiteBooleanWalsh (I := I) B] using
      norm_mul_le (finiteBooleanWalsh B) f
  · calc
      ‖f‖ = ‖finiteBooleanWalsh B * (finiteBooleanWalsh B * f)‖ := by
        rw [← mul_assoc, hsquare, one_mul]
      _ ≤ ‖finiteBooleanWalsh B‖ * ‖finiteBooleanWalsh B * f‖ :=
        norm_mul_le _ _
      _ = ‖finiteBooleanWalsh B * f‖ := by rw [norm_finiteBooleanWalsh, one_mul]

theorem finiteBooleanWalshContractionTuple_norm_prod {n : ℕ} (B : Finset I)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    (∏ j, ‖finiteBooleanWalshContractionTuple B a j‖) = ∏ j, ‖a j‖ := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [finiteBooleanWalshContractionTuple, Fin.cons_zero, Fin.cons_succ,
    norm_finiteBooleanWalsh, norm_finiteBooleanWalsh_mul, one_mul]
  congr 1

theorem finiteBooleanWalshContractionMultilinear_norm_le (n : ℕ)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    ‖finiteBooleanWalshContractionMultilinear n a‖ ≤ ∏ j, ‖a j‖ := by
  change ‖((2 : ℂ) ^ Fintype.card I)⁻¹ •
      ∑ B : Finset I, PiTensorProduct.tprod ℂ
        (finiteBooleanWalshContractionTuple B a)‖ ≤ _
  rw [norm_smul]
  have hsum :
      ‖∑ B : Finset I, PiTensorProduct.tprod ℂ
          (finiteBooleanWalshContractionTuple B a)‖ ≤
        ∑ B : Finset I, ‖PiTensorProduct.tprod ℂ
          (finiteBooleanWalshContractionTuple B a)‖ := by
    simpa using
      norm_sum_le (Finset.univ : Finset (Finset I))
        (fun B => PiTensorProduct.tprod ℂ
          (finiteBooleanWalshContractionTuple B a))
  calc
    ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ *
          ‖∑ B : Finset I, PiTensorProduct.tprod ℂ
            (finiteBooleanWalshContractionTuple B a)‖
        ≤ ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ *
          ∑ B : Finset I, ‖PiTensorProduct.tprod ℂ
            (finiteBooleanWalshContractionTuple B a)‖ :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ ‖((2 : ℂ) ^ Fintype.card I)⁻¹‖ *
          ∑ _B : Finset I, ∏ j, ‖a j‖ := by
      gcongr with B
      exact (PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℂ)
        (finiteBooleanWalshContractionTuple B a)).trans_eq
          (finiteBooleanWalshContractionTuple_norm_prod B a)
    _ = ∏ j, ‖a j‖ := by
      rw [norm_inv, norm_pow, Complex.norm_ofNat, Finset.sum_const,
        Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      have htwo : (2 : ℝ) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by norm_num)
      calc
        ((2 : ℝ) ^ Fintype.card I)⁻¹ *
            ((2 : ℝ) ^ Fintype.card I * ∏ j, ‖a j‖) =
            (((2 : ℝ) ^ Fintype.card I)⁻¹ *
              (2 : ℝ) ^ Fintype.card I) * ∏ j, ‖a j‖ := by ring
        _ = ∏ j, ‖a j‖ := by rw [inv_mul_cancel₀ htwo, one_mul]

theorem finiteBooleanWalsh_mul_atom (B : Finset I) (x : FiniteBooleanCube I) :
    finiteBooleanWalsh B * finiteBooleanAtom x =
      finiteBooleanWalsh B x • finiteBooleanAtom x := by
  classical
  ext y
  by_cases h : y = x
  · subst y
    simp [finiteBooleanAtom]
  · simp [finiteBooleanAtom, h]

/-- Fourier inversion reconstructs each atomic idempotent. -/
theorem finiteBooleanWalsh_inversion_atom (x : FiniteBooleanCube I) :
    ((2 : ℂ) ^ Fintype.card I)⁻¹ •
        ∑ B : Finset I, finiteBooleanWalsh B x • finiteBooleanWalsh B =
      finiteBooleanAtom x := by
  classical
  ext y
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, finiteBooleanWalsh]
  rw [sum_orientationWalshCharacter_mul_eq]
  by_cases h : x = y
  · subst y
    simp [finiteBooleanAtom, pow_ne_zero]
  · simp [finiteBooleanAtom, h, Ne.symm h]

/-- Prepending one tensor factor while fixing the remaining factors. -/
def finiteBooleanPrependLinear {n : ℕ}
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    FiniteBooleanAlgebra I →ₗ[ℂ]
      CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1) where
  toFun f := ((PiTensorProduct.tprod ℂ).curryLeft f) a
  map_add' f g := by
    rw [map_add]
    rfl
  map_smul' r f := by
    rw [map_smul]
    rfl

@[simp]
theorem finiteBooleanPrependLinear_apply {n : ℕ}
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) (f : FiniteBooleanAlgebra I) :
    finiteBooleanPrependLinear a f =
      PiTensorProduct.tprod ℂ (Fin.cons f a) := rfl

theorem finiteBooleanWalshContractionTuple_eq_update {n : ℕ} (B : Finset I)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    finiteBooleanWalshContractionTuple B a =
      Function.update (Fin.cons (finiteBooleanWalsh B) a) 1
        (finiteBooleanWalsh B * a 0) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp [finiteBooleanWalshContractionTuple]
  | succ j =>
      cases j using Fin.cases with
      | zero => simp [finiteBooleanWalshContractionTuple]
      | succ j =>
          simp only [finiteBooleanWalshContractionTuple, Fin.cons_succ]
          have hne : (j.succ.succ : Fin (n + 2)) ≠ (1 : Fin (n + 2)) := by
            intro e
            have he := congrArg Fin.val e
            simp at he
          rw [Function.update_of_ne hne]
          rfl

theorem finiteBooleanWalshContractionMultilinear_basis (n : ℕ)
    (x : Fin (n + 1) → FiniteBooleanCube I) :
    finiteBooleanWalshContractionMultilinear n
        (fun j => finiteBooleanAtom (x j)) =
      finiteBooleanHochschildBasis (n + 1) (Fin.cons (x 0) x) := by
  let a : Fin (n + 1) → FiniteBooleanAlgebra I :=
    fun j => finiteBooleanAtom (x j)
  have ha0 : a 0 = finiteBooleanAtom (x 0) := rfl
  have hterm : ∀ B : Finset I,
      PiTensorProduct.tprod ℂ (finiteBooleanWalshContractionTuple B a) =
        finiteBooleanWalsh B (x 0) •
          finiteBooleanPrependLinear a (finiteBooleanWalsh B) := by
    intro B
    rw [finiteBooleanWalshContractionTuple_eq_update, ha0,
      finiteBooleanWalsh_mul_atom]
    change (PiTensorProduct.tprod ℂ)
        (Function.update
          (Fin.cons (finiteBooleanWalsh B) a :
            Fin (n + 2) → FiniteBooleanAlgebra I) (1 : Fin (n + 2))
          (finiteBooleanWalsh B (x 0) • finiteBooleanAtom (x 0))) = _
    rw [(PiTensorProduct.tprod ℂ).map_update_smul]
    have hupdate : Function.update
        (Fin.cons (finiteBooleanWalsh B) a :
          Fin (n + 2) → FiniteBooleanAlgebra I) (1 : Fin (n + 2))
          (finiteBooleanAtom (x 0)) = Fin.cons (finiteBooleanWalsh B) a := by
      funext j
      by_cases hj : j = 1
      · subst j
        rw [Function.update_self]
        exact ha0.symm
      · rw [Function.update_of_ne hj]
    rw [hupdate, finiteBooleanPrependLinear_apply]
  change ((2 : ℂ) ^ Fintype.card I)⁻¹ •
      ∑ B : Finset I, PiTensorProduct.tprod ℂ
        (finiteBooleanWalshContractionTuple B a) = _
  simp_rw [hterm]
  rw [finiteBooleanHochschildBasis_apply]
  calc
    ((2 : ℂ) ^ Fintype.card I)⁻¹ •
          ∑ B : Finset I, finiteBooleanWalsh B (x 0) •
            finiteBooleanPrependLinear a (finiteBooleanWalsh B) =
        ((2 : ℂ) ^ Fintype.card I)⁻¹ •
          finiteBooleanPrependLinear a
            (∑ B : Finset I, finiteBooleanWalsh B (x 0) •
              finiteBooleanWalsh B) := by
      congr 1
      rw [map_sum]
      simp_rw [map_smul]
    _ = finiteBooleanPrependLinear a
        (((2 : ℂ) ^ Fintype.card I)⁻¹ •
          ∑ B : Finset I, finiteBooleanWalsh B (x 0) •
            finiteBooleanWalsh B) := by rw [map_smul]
    _ = finiteBooleanPrependLinear a (finiteBooleanAtom (x 0)) := by
      rw [finiteBooleanWalsh_inversion_atom]
    _ = PiTensorProduct.tprod ℂ
        (fun j : Fin (n + 2) => finiteBooleanAtom
          ((Fin.cons (x 0) x : Fin (n + 2) → FiniteBooleanCube I) j)) := by
      rw [finiteBooleanPrependLinear_apply]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j => rfl

/-- Linear Walsh-average contraction on projective Hochschild chains. -/
def finiteBooleanWalshContraction (n : ℕ) :
    CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n →ₗ[ℂ]
      CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1) :=
  PiTensorProduct.lift (finiteBooleanWalshContractionMultilinear (I := I) n)

@[simp]
theorem finiteBooleanWalshContraction_tprod (n : ℕ)
    (a : Fin (n + 1) → FiniteBooleanAlgebra I) :
    finiteBooleanWalshContraction n (PiTensorProduct.tprod ℂ a) =
      finiteBooleanWalshContractionMultilinear n a :=
  PiTensorProduct.lift.tprod _

theorem finiteBooleanWalshContraction_eq (n : ℕ) :
    finiteBooleanWalshContraction (I := I) n =
      finiteBooleanHochschildContraction n := by
  apply Module.Basis.ext (finiteBooleanHochschildBasis n)
  intro x
  rw [finiteBooleanHochschildBasis_apply,
    finiteBooleanWalshContraction_tprod,
    finiteBooleanWalshContractionMultilinear_basis]
  rw [← finiteBooleanHochschildBasis_apply (I := I) n x,
    finiteBooleanHochschildContraction_basis]

/-- Continuous Walsh contraction, constructed with bound one before projective lifting. -/
def finiteBooleanHochschildContractionContinuousMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (n + 1) ↦ FiniteBooleanAlgebra I)
      (CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1)) :=
  (finiteBooleanWalshContractionMultilinear (I := I) n).mkContinuous 1
    (by
      intro a
      simpa using finiteBooleanWalshContractionMultilinear_norm_le (I := I) n a)

/-- Projectively continuous separability contraction in every Hochschild degree. -/
def finiteBooleanHochschildContractionContinuous (n : ℕ) :
    CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n →L[ℂ]
      CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1) :=
  PiTensorProduct.liftEquiv ℂ
    (fun _ : Fin (n + 1) ↦ FiniteBooleanAlgebra I)
    (CyclicBarTensor ℂ (FiniteBooleanAlgebra I) (n + 1))
      (finiteBooleanHochschildContractionContinuousMultilinear (I := I) n)

@[simp]
theorem finiteBooleanHochschildContractionContinuous_apply (n : ℕ)
    (z : CyclicBarTensor ℂ (FiniteBooleanAlgebra I) n) :
    finiteBooleanHochschildContractionContinuous n z =
      finiteBooleanHochschildContraction n z := by
  change finiteBooleanWalshContraction n z =
    finiteBooleanHochschildContraction n z
  rw [finiteBooleanWalshContraction_eq]

/-- Dimension-free operator norm: every Boolean Hochschild contraction has norm at most one. -/
theorem norm_finiteBooleanHochschildContractionContinuous_le_one (n : ℕ) :
    ‖finiteBooleanHochschildContractionContinuous (I := I) n‖ ≤ 1 := by
  let f := finiteBooleanHochschildContractionContinuousMultilinear (I := I) n
  have hf : ‖f‖ ≤ 1 := by
    dsimp [f, finiteBooleanHochschildContractionContinuousMultilinear]
    exact MultilinearMap.mkContinuous_norm_le _ (by norm_num)
      (fun a => by
        simpa using finiteBooleanWalshContractionMultilinear_norm_le (I := I) n a)
  calc
    ‖finiteBooleanHochschildContractionContinuous (I := I) n‖ ≤ ‖f‖ := by
      rw [finiteBooleanHochschildContractionContinuous,
        PiTensorProduct.liftEquiv_apply]
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
    _ ≤ 1 := hf

/-! ## Multiplicativity for disjoint packets -/

theorem functionTensorProductHom_mul
    {X Y : Type*} (u v : (X → ℂ) ⊗[ℂ] (Y → ℂ)) :
    GaloisForLFunctions.RHTower.functionTensorProductHom ℂ X Y (u * v) =
      GaloisForLFunctions.RHTower.functionTensorProductHom ℂ X Y u *
        GaloisForLFunctions.RHTower.functionTensorProductHom ℂ X Y v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          ext z
          simp [GaloisForLFunctions.RHTower.functionTensorProductHom_tmul]
          ring
      | add v w hv hw => simp [mul_add, hv, hw]
  | add u w hu hw => simp [add_mul, hu, hw]

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Pull an observable on the left packet to the disjoint union packet. -/
def finiteBooleanPullInl :
    FiniteBooleanAlgebra I →ₗ[ℂ] FiniteBooleanAlgebra (I ⊕ J) where
  toFun f x := f (fun i => x (Sum.inl i))
  map_add' f g := rfl
  map_smul' c f := rfl

/-- Pull an observable on the right packet to the disjoint union packet. -/
def finiteBooleanPullInr :
    FiniteBooleanAlgebra J →ₗ[ℂ] FiniteBooleanAlgebra (I ⊕ J) where
  toFun f x := f (fun j => x (Sum.inr j))
  map_add' f g := rfl
  map_smul' c f := rfl

theorem finiteBooleanDiagonal_eval (x y : FiniteBooleanCube I) :
    GaloisForLFunctions.RHTower.functionTensorProductHom ℂ
        (FiniteBooleanCube I) (FiniteBooleanCube I)
        (finiteBooleanDiagonal (I := I)) (x, y) =
      if x = y then 1 else 0 := by
  classical
  simp only [finiteBooleanDiagonal, map_sum,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    Finset.sum_apply]
  by_cases h : x = y
  · subst y
    simp [finiteBooleanAtom]
  · simp [finiteBooleanAtom, h]

theorem finiteBooleanPullInl_diagonal_eval
    (x y : FiniteBooleanCube (I ⊕ J)) :
    GaloisForLFunctions.RHTower.functionTensorProductHom ℂ
        (FiniteBooleanCube (I ⊕ J)) (FiniteBooleanCube (I ⊕ J))
        (TensorProduct.map (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanDiagonal (I := I))) (x, y) =
      if (fun i => x (Sum.inl i)) = (fun i => y (Sum.inl i)) then 1 else 0 := by
  classical
  simp only [finiteBooleanDiagonal, map_sum, TensorProduct.map_tmul,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    Finset.sum_apply, finiteBooleanPullInl]
  by_cases h : (fun i => x (Sum.inl i)) = (fun i => y (Sum.inl i))
  · rw [if_pos h]
    simp [finiteBooleanAtom, h]
  · rw [if_neg h]
    simp [finiteBooleanAtom, h]

theorem finiteBooleanPullInr_diagonal_eval
    (x y : FiniteBooleanCube (I ⊕ J)) :
    GaloisForLFunctions.RHTower.functionTensorProductHom ℂ
        (FiniteBooleanCube (I ⊕ J)) (FiniteBooleanCube (I ⊕ J))
        (TensorProduct.map (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanDiagonal (I := J))) (x, y) =
      if (fun j => x (Sum.inr j)) = (fun j => y (Sum.inr j)) then 1 else 0 := by
  classical
  simp only [finiteBooleanDiagonal, map_sum, TensorProduct.map_tmul,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    Finset.sum_apply, finiteBooleanPullInr]
  by_cases h : (fun j => x (Sum.inr j)) = (fun j => y (Sum.inr j))
  · rw [if_pos h]
    simp [finiteBooleanAtom, h]
  · rw [if_neg h]
    simp [finiteBooleanAtom, h]

/-- Separability diagonals multiply exactly under disjoint packet union. -/
theorem finiteBooleanDiagonal_sum_multiplicative :
    finiteBooleanDiagonal (I := I ⊕ J) =
      TensorProduct.map (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanDiagonal (I := I)) *
        TensorProduct.map (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanDiagonal (I := J)) := by
  classical
  apply GaloisForLFunctions.RHTower.functionTensorProductHom_injective
  ext z
  rcases z with ⟨x, y⟩
  rw [functionTensorProductHom_mul, finiteBooleanDiagonal_eval]
  simp only [Pi.mul_apply]
  rw [
    finiteBooleanPullInl_diagonal_eval, finiteBooleanPullInr_diagonal_eval]
  by_cases hI : (fun i => x (Sum.inl i)) = (fun i => y (Sum.inl i))
  · by_cases hJ : (fun j => x (Sum.inr j)) = (fun j => y (Sum.inr j))
    · have hxy : x = y := by
        funext s
        cases s with
        | inl i => exact congrFun hI i
        | inr j => exact congrFun hJ j
      simp [hI, hJ, hxy]
    · have hxy : x ≠ y := fun h => hJ (by simpa [h])
      simp [hI, hJ, hxy]
  · have hxy : x ≠ y := fun h => hI (by simpa [h])
    simp [hI, hxy]

/-! ## The exact one-coordinate fracture -/

/-- Atomic idempotent in the two-point algebra. -/
def twoPointBooleanAtom (x : Bool) : Bool → ℂ :=
  fun y => if y = x then 1 else 0

/-- The one-coordinate diagonal. -/
def twoPointBooleanDiagonal :
    (Bool → ℂ) ⊗[ℂ] (Bool → ℂ) :=
  ∑ x : Bool, twoPointBooleanAtom x ⊗ₜ[ℂ] twoPointBooleanAtom x

/-- The old diagonal extended by the tensor unit in a new Boolean coordinate. -/
def twoPointBooleanUnitTensor : (Bool → ℂ) ⊗[ℂ] (Bool → ℂ) :=
  (1 : Bool → ℂ) ⊗ₜ[ℂ] (1 : Bool → ℂ)

/-- Exact projective distance between a new Boolean diagonal and the old unit extension. -/
theorem projTensorSeminorm_twoPointBoolean_fracture :
    projTensorSeminorm (normSeminorm ℂ (Bool → ℂ)) (normSeminorm ℂ (Bool → ℂ))
      (twoPointBooleanDiagonal - twoPointBooleanUnitTensor) = 1 := by
  classical
  let A := Bool → ℂ
  let p := normSeminorm ℂ A
  let P := projTensorSeminorm p p
  let u : A := fun x => if x then -1 else 1
  have hu : ‖u‖ = 1 := by
    rw [Pi.norm_def]
    norm_num [u]
  have hone : ‖(1 : A)‖ = 1 := by simp
  have one_apply (b : Bool) : (1 : A) b = 1 := rfl
  have hdecomp : twoPointBooleanDiagonal - twoPointBooleanUnitTensor =
      ((2 : ℂ)⁻¹ • (u ⊗ₜ[ℂ] u - (1 : A) ⊗ₜ[ℂ] (1 : A))) := by
    apply GaloisForLFunctions.RHTower.functionTensorProductHom_injective
    ext z
    rcases z with ⟨x, y⟩
    simp only [twoPointBooleanDiagonal, twoPointBooleanUnitTensor, map_sub, map_sum,
      map_smul, GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
      GaloisForLFunctions.RHTower.functionTensorProductHom_tmul]
    cases x <;> cases y <;>
      norm_num [twoPointBooleanAtom, u, one_apply]
  have hupper : P (twoPointBooleanDiagonal - twoPointBooleanUnitTensor) ≤ 1 := by
    rw [hdecomp, map_smul_eq_mul]
    refine le_trans (mul_le_mul_of_nonneg_left (map_sub_le_add P _ _) (norm_nonneg _)) ?_
    have huu := projTensorSeminorm_tmul_le p p u u
    have h11 := projTensorSeminorm_tmul_le p p (1 : A) (1 : A)
    simp [p, hu] at huu
    simp [p, hone] at h11
    change P (u ⊗ₜ[ℂ] u) ≤ 1 at huu
    change P ((1 : A) ⊗ₜ[ℂ] (1 : A)) ≤ 1 at h11
    calc
      ‖(2 : ℂ)⁻¹‖ *
          (P (u ⊗ₜ[ℂ] u) + P ((1 : A) ⊗ₜ[ℂ] (1 : A)))
          ≤ ‖(2 : ℂ)⁻¹‖ * (1 + 1) := by gcongr
      _ = 1 := by norm_num
  have hlower : 1 ≤ P (twoPointBooleanDiagonal - twoPointBooleanUnitTensor) := by
    let evalBilinear : A →ₗ[ℂ] A →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun f g => f false * g true)
        (fun f g h => by
          change (f false + g false) * h true = f false * h true + g false * h true
          ring)
        (fun c f g => by
          change (c * f false) * g true = c * (f false * g true)
          ring)
        (fun f g h => by
          change f false * (g true + h true) = f false * g true + f false * h true
          ring)
        (fun c f g => by
          change f false * (c * g true) = c * (f false * g true)
          ring)
    have heval : ∀ f g : A, ‖evalBilinear f g‖ ≤ 1 * (p f * p g) := by
      intro f g
      have hf : ‖f false‖ ≤ ‖f‖ := by
        rw [Pi.norm_def]
        exact_mod_cast Finset.le_sup (f := fun b => ‖f b‖₊) (Finset.mem_univ false)
      have hg : ‖g true‖ ≤ ‖g‖ := by
        rw [Pi.norm_def]
        exact_mod_cast Finset.le_sup (f := fun b => ‖g b‖₊) (Finset.mem_univ true)
      simpa [evalBilinear, p] using
        (calc
          ‖f false * g true‖ ≤ ‖f false‖ * ‖g true‖ := norm_mul_le _ _
          _ ≤ ‖f‖ * ‖g‖ := mul_le_mul hf hg (norm_nonneg _) (norm_nonneg _))
    have h := projTensorSeminorm_lift_le p p (normSeminorm ℂ ℂ) evalBilinear
      (C := 1) (by norm_num) heval (twoPointBooleanDiagonal - twoPointBooleanUnitTensor)
    have heq : TensorProduct.lift evalBilinear
        (twoPointBooleanDiagonal - twoPointBooleanUnitTensor) = -1 := by
      rw [hdecomp]
      simp only [map_smul, map_sub, TensorProduct.lift.tmul]
      have eval_apply : ∀ f g : A, evalBilinear f g = f false * g true := fun _ _ => rfl
      rw [eval_apply, eval_apply]
      norm_num [u, one_apply]
    rw [heq] at h
    simpa [P] using h
  exact le_antisymm hupper hlower

/-! ## The cofinal one-coordinate fracture over an arbitrary old packet -/

/-- Evaluation on a pair of points, regarded as a functional on the algebraic tensor square. -/
def finiteFunctionTensorEvaluation {X : Type*} (x y : X) :
    ((X → ℂ) ⊗[ℂ] (X → ℂ)) →ₗ[ℂ] ℂ :=
  TensorProduct.lift <|
    LinearMap.mk₂ ℂ (fun f g => f x * g y)
      (fun f g h => by
        change (f x + g x) * h y = f x * h y + g x * h y
        ring)
      (fun c f g => by
        change (c * f x) * g y = c * (f x * g y)
        ring)
      (fun f g h => by
        change f x * (g y + h y) = f x * g y + f x * h y
        ring)
      (fun c f g => by
        change f x * (c * g y) = c * (f x * g y)
        ring)

@[simp]
theorem finiteFunctionTensorEvaluation_tmul {X : Type*} (x y : X) (f g : X → ℂ) :
    finiteFunctionTensorEvaluation x y (f ⊗ₜ[ℂ] g) = f x * g y := by
  rfl

theorem finiteFunctionTensorEvaluation_eq_functionTensorProductHom
    {X : Type*} (x y : X) (z : (X → ℂ) ⊗[ℂ] (X → ℂ)) :
    finiteFunctionTensorEvaluation x y z =
      GaloisForLFunctions.RHTower.functionTensorProductHom ℂ X X z (x, y) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro f g
    rfl
  · intro u v hu hv
    simp only [map_add, Pi.add_apply, hu, hv]

/-- Pair evaluation has dual projective norm at most one. -/
theorem norm_finiteFunctionTensorEvaluation_le_projTensorSeminorm
    {X : Type*} [Fintype X] (x y : X) (z : (X → ℂ) ⊗[ℂ] (X → ℂ)) :
    ‖finiteFunctionTensorEvaluation x y z‖ ≤
      projTensorSeminorm (normSeminorm ℂ (X → ℂ)) (normSeminorm ℂ (X → ℂ)) z := by
  let p := normSeminorm ℂ (X → ℂ)
  let evalBilinear : (X → ℂ) →ₗ[ℂ] (X → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun f g => f x * g y)
      (fun f g h => by
        change (f x + g x) * h y = f x * h y + g x * h y
        ring)
      (fun c f g => by
        change (c * f x) * g y = c * (f x * g y)
        ring)
      (fun f g h => by
        change f x * (g y + h y) = f x * g y + f x * h y
        ring)
      (fun c f g => by
        change f x * (c * g y) = c * (f x * g y)
        ring)
  have heval : ∀ f g : X → ℂ, ‖evalBilinear f g‖ ≤ 1 * (p f * p g) := by
    intro f g
    have hf : ‖f x‖ ≤ ‖f‖ := by
      rw [Pi.norm_def]
      exact_mod_cast Finset.le_sup (f := fun a => ‖f a‖₊) (Finset.mem_univ x)
    have hg : ‖g y‖ ≤ ‖g‖ := by
      rw [Pi.norm_def]
      exact_mod_cast Finset.le_sup (f := fun a => ‖g a‖₊) (Finset.mem_univ y)
    simpa [evalBilinear, p] using
      (calc
        ‖f x * g y‖ ≤ ‖f x‖ * ‖g y‖ := norm_mul_le _ _
        _ ≤ ‖f‖ * ‖g‖ := mul_le_mul hf hg (norm_nonneg _) (norm_nonneg _))
  have h := projTensorSeminorm_lift_le p p (normSeminorm ℂ ℂ) evalBilinear
    (C := 1) (by norm_num) heval z
  simpa [finiteFunctionTensorEvaluation, evalBilinear, p] using h

/-- Canonical shuffle that places two disjoint packet tensor squares in the large tensor square. -/
def finiteBooleanDiagonalShuffleBilinear :
    ((FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ)) →ₗ[ℂ]
      ((FiniteBooleanCube J → ℂ) ⊗[ℂ] (FiniteBooleanCube J → ℂ)) →ₗ[ℂ]
        ((FiniteBooleanCube (I ⊕ J) → ℂ) ⊗[ℂ] (FiniteBooleanCube (I ⊕ J) → ℂ)) :=
  LinearMap.mk₂ ℂ
    (fun u v =>
      TensorProduct.map (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanPullInl (I := I) (J := J)) u *
        TensorProduct.map (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanPullInr (I := I) (J := J)) v)
    (fun u v w => by simp only [map_add, add_mul])
    (fun c u v => by simp only [map_smul, smul_mul_assoc])
    (fun u v w => by simp only [map_add, mul_add])
    (fun c u v => by simp only [map_smul, mul_smul_comm])

/-- Linearized canonical shuffle for disjoint packet tensor squares. -/
def finiteBooleanDiagonalShuffle :
    (((FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ)) ⊗[ℂ]
      ((FiniteBooleanCube J → ℂ) ⊗[ℂ] (FiniteBooleanCube J → ℂ))) →ₗ[ℂ]
        ((FiniteBooleanCube (I ⊕ J) → ℂ) ⊗[ℂ] (FiniteBooleanCube (I ⊕ J) → ℂ)) :=
  TensorProduct.lift finiteBooleanDiagonalShuffleBilinear

@[simp]
theorem finiteBooleanDiagonalShuffle_tmul
    (u : (FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ))
    (v : (FiniteBooleanCube J → ℂ) ⊗[ℂ] (FiniteBooleanCube J → ℂ)) :
    finiteBooleanDiagonalShuffle (I := I) (J := J) (u ⊗ₜ[ℂ] v) =
      TensorProduct.map (finiteBooleanPullInl (I := I) (J := J))
          (finiteBooleanPullInl (I := I) (J := J)) u *
        TensorProduct.map (finiteBooleanPullInr (I := I) (J := J))
          (finiteBooleanPullInr (I := I) (J := J)) v := by
  rfl

/-- Identify the two-point Boolean algebra with the cube on one singleton coordinate. -/
def twoPointToSingletonCube : (Bool → ℂ) →ₗ[ℂ] (FiniteBooleanCube PUnit → ℂ) where
  toFun f x := f (x PUnit.unit)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The induced identification on tensor squares. -/
def twoPointTensorToSingletonCube :
    ((Bool → ℂ) ⊗[ℂ] (Bool → ℂ)) →ₗ[ℂ]
      ((FiniteBooleanCube PUnit → ℂ) ⊗[ℂ] (FiniteBooleanCube PUnit → ℂ)) :=
  TensorProduct.map twoPointToSingletonCube twoPointToSingletonCube

theorem twoPointTensorToSingletonCube_diagonal :
    twoPointTensorToSingletonCube twoPointBooleanDiagonal =
      finiteBooleanDiagonal (I := PUnit) := by
  classical
  apply GaloisForLFunctions.RHTower.functionTensorProductHom_injective
  ext z
  rcases z with ⟨x, y⟩
  rw [finiteBooleanDiagonal_eval]
  simp only [twoPointTensorToSingletonCube, twoPointBooleanDiagonal, map_sum,
    TensorProduct.map_tmul, GaloisForLFunctions.RHTower.functionTensorProductHom_tmul,
    Finset.sum_apply, twoPointToSingletonCube]
  by_cases h : x = y
  · subst y
    cases hx : x PUnit.unit <;> simp [twoPointBooleanAtom, hx]
  · have hxy : x PUnit.unit ≠ y PUnit.unit := by
      intro heq
      apply h
      funext i
      cases i
      exact heq
    rw [if_neg h]
    cases hx : x PUnit.unit <;> cases hy : y PUnit.unit <;>
      simp_all [twoPointBooleanAtom]

theorem twoPointTensorToSingletonCube_unit :
    twoPointTensorToSingletonCube twoPointBooleanUnitTensor =
      (1 : FiniteBooleanCube PUnit → ℂ) ⊗ₜ[ℂ] (1 : FiniteBooleanCube PUnit → ℂ) := by
  rfl

/-- Canonical shuffle for adjoining one Boolean coordinate. -/
def finiteBooleanCofinalShuffle :
    (((FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ)) ⊗[ℂ]
      ((Bool → ℂ) ⊗[ℂ] (Bool → ℂ))) →ₗ[ℂ]
        ((FiniteBooleanCube (I ⊕ PUnit) → ℂ) ⊗[ℂ]
          (FiniteBooleanCube (I ⊕ PUnit) → ℂ)) :=
  finiteBooleanDiagonalShuffle (I := I) (J := PUnit) ∘ₗ
    TensorProduct.map LinearMap.id twoPointTensorToSingletonCube

@[simp]
theorem finiteBooleanCofinalShuffle_tmul
    (u : (FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ))
    (v : (Bool → ℂ) ⊗[ℂ] (Bool → ℂ)) :
    finiteBooleanCofinalShuffle (I := I) (u ⊗ₜ[ℂ] v) =
      finiteBooleanDiagonalShuffle (I := I) (J := PUnit)
        (u ⊗ₜ[ℂ] twoPointTensorToSingletonCube v) := by
  rfl

/-- Old diagonal extended by the tensor unit in one newly adjoined Boolean coordinate. -/
def finiteBooleanDiagonalUnitExtension :
    (FiniteBooleanCube (I ⊕ PUnit) → ℂ) ⊗[ℂ]
      (FiniteBooleanCube (I ⊕ PUnit) → ℂ) :=
  finiteBooleanCofinalShuffle (I := I)
    (finiteBooleanDiagonal (I := I) ⊗ₜ[ℂ] twoPointBooleanUnitTensor)

/-- Canonical shuffled representative of the jump caused by adjoining one Boolean coordinate. -/
def finiteBooleanCofinalFracture :
    (((FiniteBooleanCube I → ℂ) ⊗[ℂ] (FiniteBooleanCube I → ℂ)) ⊗[ℂ]
      ((Bool → ℂ) ⊗[ℂ] (Bool → ℂ))) :=
  finiteBooleanDiagonal (I := I) ⊗ₜ[ℂ]
    (twoPointBooleanDiagonal - twoPointBooleanUnitTensor)

/-- Shuffling the outer fracture gives exactly new diagonal minus old unit extension. -/
theorem finiteBooleanDiagonal_sub_unitExtension_eq_shuffle_fracture :
    finiteBooleanDiagonal (I := I ⊕ PUnit) - finiteBooleanDiagonalUnitExtension (I := I) =
      finiteBooleanCofinalShuffle (I := I)
        (finiteBooleanCofinalFracture (I := I)) := by
  rw [finiteBooleanDiagonal_sum_multiplicative (I := I) (J := PUnit)]
  simp only [finiteBooleanDiagonalUnitExtension, finiteBooleanCofinalFracture,
    finiteBooleanCofinalShuffle_tmul, finiteBooleanDiagonalShuffle_tmul,
    twoPointTensorToSingletonCube_diagonal, twoPointTensorToSingletonCube_unit, map_sub,
    mul_sub]

/-- The one-coordinate cofinal jump has exact iterated projective norm one for every old packet. -/
theorem projTensorSeminorm_finiteBooleanCofinalFracture :
    projTensorSeminorm
      (projTensorSeminorm (normSeminorm ℂ (FiniteBooleanCube I → ℂ))
        (normSeminorm ℂ (FiniteBooleanCube I → ℂ)))
      (projTensorSeminorm (normSeminorm ℂ (Bool → ℂ))
        (normSeminorm ℂ (Bool → ℂ)))
      (finiteBooleanCofinalFracture (I := I)) = 1 := by
  classical
  let AI := FiniteBooleanCube I → ℂ
  let AB := Bool → ℂ
  let EI := AI ⊗[ℂ] AI
  let EB := AB ⊗[ℂ] AB
  let pI := normSeminorm ℂ AI
  let pB := normSeminorm ℂ AB
  let PI := projTensorSeminorm pI pI
  let PB := projTensorSeminorm pB pB
  let D : EI := finiteBooleanDiagonal (I := I)
  let F : EB := twoPointBooleanDiagonal - twoPointBooleanUnitTensor
  have hDI : PI D = 1 := by
    simpa [PI, pI, D, AI] using projTensorSeminorm_finiteBooleanDiagonal (I := I)
  have hFB : PB F = 1 := by
    simpa [PB, pB, F, AB] using projTensorSeminorm_twoPointBoolean_fracture
  have hupper : projTensorSeminorm PI PB (finiteBooleanCofinalFracture (I := I)) ≤ 1 := by
    have h := projTensorSeminorm_tmul_le PI PB D F
    simpa [finiteBooleanCofinalFracture, D, F, hDI, hFB] using h
  have hlower : 1 ≤ projTensorSeminorm PI PB (finiteBooleanCofinalFracture (I := I)) := by
    let x₀ : FiniteBooleanCube I := fun _ => false
    let φ : EI →ₗ[ℂ] ℂ := finiteFunctionTensorEvaluation x₀ x₀
    let ψ : EB →ₗ[ℂ] ℂ := finiteFunctionTensorEvaluation false true
    have hφ : ∀ u : EI, ‖φ u‖ ≤ PI u := by
      intro u
      simpa [φ, PI, pI, EI, AI] using
        norm_finiteFunctionTensorEvaluation_le_projTensorSeminorm x₀ x₀ u
    have hψ : ∀ v : EB, ‖ψ v‖ ≤ PB v := by
      intro v
      simpa [ψ, PB, pB, EB, AB] using
        norm_finiteFunctionTensorEvaluation_le_projTensorSeminorm false true v
    let outerBilinear : EI →ₗ[ℂ] EB →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun u v => φ u * ψ v)
        (fun u v w => by
          simp only [map_add]
          ring)
        (fun c u v => by
          simp only [map_smul, smul_eq_mul]
          ring)
        (fun u v w => by
          simp only [map_add]
          ring)
        (fun c u v => by
          simp only [map_smul, smul_eq_mul]
          ring)
    have houter : ∀ u : EI, ∀ v : EB,
        ‖outerBilinear u v‖ ≤ 1 * (PI u * PB v) := by
      intro u v
      simpa [outerBilinear] using
        (calc
          ‖φ u * ψ v‖ ≤ ‖φ u‖ * ‖ψ v‖ := norm_mul_le _ _
          _ ≤ PI u * PB v := mul_le_mul (hφ u) (hψ v) (norm_nonneg _) (by positivity))
    have h := projTensorSeminorm_lift_le PI PB (normSeminorm ℂ ℂ) outerBilinear
      (C := 1) (by norm_num) houter (finiteBooleanCofinalFracture (I := I))
    have hφD : φ D = 1 := by
      change finiteFunctionTensorEvaluation x₀ x₀ (finiteBooleanDiagonal (I := I)) = 1
      rw [finiteFunctionTensorEvaluation_eq_functionTensorProductHom]
      simpa using finiteBooleanDiagonal_eval (I := I) x₀ x₀
    have hψF : ψ F = -1 := by
      change finiteFunctionTensorEvaluation false true
        (twoPointBooleanDiagonal - twoPointBooleanUnitTensor) = -1
      rw [finiteFunctionTensorEvaluation_eq_functionTensorProductHom]
      simp [twoPointBooleanDiagonal, twoPointBooleanUnitTensor, twoPointBooleanAtom,
        GaloisForLFunctions.RHTower.functionTensorProductHom_tmul]
    have heq : TensorProduct.lift outerBilinear
        (finiteBooleanCofinalFracture (I := I)) = -1 := by
      simp [finiteBooleanCofinalFracture, outerBilinear, D, F, hφD, hψF]
    rw [heq] at h
    simpa using h
  exact le_antisymm hupper hlower

end GaloisForLFunctions.HTGeometry
