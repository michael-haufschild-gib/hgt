import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm
import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint
import GaloisForLFunctions.RHTower.FunctionTensorProduct

/-!
# Finite Boolean separability diagonals

Algebraic and sharp projective-seminorm layer of the canonical diagonal of a finite Boolean
function algebra.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

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

@[simp]
omit [Fintype I] [DecidableEq I] in
theorem finiteBooleanMultiplication_tmul (f g : FiniteBooleanAlgebra I) :
    finiteBooleanMultiplication (f ⊗ₜ[ℂ] g) = f * g := by
  rfl

@[simp]
omit [Fintype I] [DecidableEq I] in
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

end GaloisForLFunctions.HTGeometry
