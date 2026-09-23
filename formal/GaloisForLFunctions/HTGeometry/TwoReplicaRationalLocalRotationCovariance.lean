import GaloisForLFunctions.HTGeometry.TwoReplicaFirstOrderCliffordInterpolation

/-!
# Exact rational local-rotation covariance of the two-replica q-local family

The nonunit-normalized one-qubit gate `1 + 2iP`, with its exact inverse,
preserves Pauli weight under conjugation.  Its doubled conjugation therefore
preserves the span of q-local collective commutators in both directions.  As a
consequence, the canonical greatest Hall-defect maximizer is fixed by every
such single-site rotation.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem complex_I_pow_five : Complex.I ^ (5 : ℕ) = Complex.I := by
  rw [show 5 = 4 + 1 by norm_num, pow_succ, Complex.I_pow_four, one_mul]

def boolPauliDoubleRotationGate (a : Fin 3) : Matrix Bool Bool ℂ :=
  1 + (2 * Complex.I) • finiteQubitPauli a

def boolPauliDoubleRotationGateInv (a : Fin 3) : Matrix Bool Bool ℂ :=
  (1 / 5 : ℂ) • (1 - (2 * Complex.I) • finiteQubitPauli a)

theorem boolPauliDoubleRotationGate_mul_inv (a : Fin 3) :
    boolPauliDoubleRotationGate a * boolPauliDoubleRotationGateInv a = 1 := by
  fin_cases a
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boolPauliDoubleRotationGate, boolPauliDoubleRotationGateInv,
        finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
        Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq] <;>
        simp [pow_succ, Complex.I_sq, complex_I_pow_five] <;> ring

theorem boolPauliDoubleRotationGate_inv_mul (a : Fin 3) :
    boolPauliDoubleRotationGateInv a * boolPauliDoubleRotationGate a = 1 := by
  fin_cases a
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boolPauliDoubleRotationGate, boolPauliDoubleRotationGateInv,
        finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
        Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq] <;>
        simp [pow_succ, Complex.I_sq, complex_I_pow_five] <;> ring

def boolPauliDoubleRotationTarget (a : Fin 3) : Option (Fin 3) → Option (Fin 3)
  | none => none
  | some b =>
      if b = a then some b
      else if b = pauliAxisNext a then some (pauliAxisPrev a)
      else some (pauliAxisNext a)

def boolPauliDoubleRotationSourceCoeff (a : Fin 3) : Option (Fin 3) → ℂ
  | none => 1
  | some b => if b = a then 1 else -(3 / 5 : ℂ)

def boolPauliDoubleRotationTargetCoeff (a : Fin 3) : Option (Fin 3) → ℂ
  | none => 0
  | some b =>
      if b = a then 0
      else if b = pauliAxisNext a then -(4 / 5 : ℂ) else (4 / 5 : ℂ)

theorem boolPauliDoubleRotationTarget_eq_none_iff (a : Fin 3)
    (p : Option (Fin 3)) :
    boolPauliDoubleRotationTarget a p = none ↔ p = none := by
  fin_cases a <;> fin_cases p <;>
    simp [boolPauliDoubleRotationTarget, pauliAxisNext, pauliAxisPrev]

theorem boolPauliDoubleRotation_conj (a : Fin 3) (p : Option (Fin 3)) :
    boolPauliDoubleRotationGate a * boolPauliOption p *
        boolPauliDoubleRotationGateInv a =
      boolPauliDoubleRotationSourceCoeff a p • boolPauliOption p +
        boolPauliDoubleRotationTargetCoeff a p •
          boolPauliOption (boolPauliDoubleRotationTarget a p) := by
  fin_cases a <;> fin_cases p
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boolPauliDoubleRotationGate, boolPauliDoubleRotationGateInv,
        boolPauliDoubleRotationTarget, boolPauliDoubleRotationSourceCoeff,
        boolPauliDoubleRotationTargetCoeff, pauliAxisNext, pauliAxisPrev,
        boolPauliOption, finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.one_apply, Matrix.smul_apply, Complex.I_mul_I] <;>
        ring_nf <;> norm_num [Complex.I_sq] <;>
        simp [pow_succ, Complex.I_sq, complex_I_pow_five] <;> ring

theorem boolPauliDoubleRotation_inv_conj (a : Fin 3) (p : Option (Fin 3)) :
    boolPauliDoubleRotationGateInv a * boolPauliOption p *
        boolPauliDoubleRotationGate a =
      boolPauliDoubleRotationSourceCoeff a p • boolPauliOption p -
        boolPauliDoubleRotationTargetCoeff a p •
          boolPauliOption (boolPauliDoubleRotationTarget a p) := by
  fin_cases a <;> fin_cases p
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boolPauliDoubleRotationGate, boolPauliDoubleRotationGateInv,
        boolPauliDoubleRotationTarget, boolPauliDoubleRotationSourceCoeff,
        boolPauliDoubleRotationTargetCoeff, pauliAxisNext, pauliAxisPrev,
        boolPauliOption, finiteQubitPauli, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.one_apply, Matrix.smul_apply, Complex.I_mul_I] <;>
        ring_nf <;> norm_num [Complex.I_sq] <;>
        simp [pow_succ, Complex.I_sq, complex_I_pow_five] <;> ring

def finiteSingleSiteDoubleRotationGate
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteSingleSiteMatrix j (boolPauliDoubleRotationGate a)

def finiteSingleSiteDoubleRotationGateInv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteSingleSiteMatrix j (boolPauliDoubleRotationGateInv a)

theorem finiteSingleSiteMatrix_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (M N : Matrix Bool Bool ℂ) :
    finiteSingleSiteMatrix j M * finiteSingleSiteMatrix j N =
      finiteSingleSiteMatrix j (M * N) := by
  rw [finiteSingleSiteMatrix, finiteSingleSiteMatrix, finiteSingleSiteMatrix,
    finiteLocalMatrix_mul]
  congr 1
  funext s
  by_cases hs : s = j <;> simp [hs]

theorem finiteSingleSiteDoubleRotationGate_mul_inv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    finiteSingleSiteDoubleRotationGate j a *
        finiteSingleSiteDoubleRotationGateInv j a = 1 := by
  rw [finiteSingleSiteDoubleRotationGate,
    finiteSingleSiteDoubleRotationGateInv, finiteSingleSiteMatrix_mul,
    boolPauliDoubleRotationGate_mul_inv, finiteSingleSiteMatrix_one]

theorem finiteSingleSiteDoubleRotationGate_inv_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    finiteSingleSiteDoubleRotationGateInv j a *
        finiteSingleSiteDoubleRotationGate j a = 1 := by
  rw [finiteSingleSiteDoubleRotationGate,
    finiteSingleSiteDoubleRotationGateInv, finiteSingleSiteMatrix_mul,
    boolPauliDoubleRotationGate_inv_mul, finiteSingleSiteMatrix_one]

def finiteSingleSiteDoubleRotationTarget
    {σ : Type*} [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    σ → Option (Fin 3) :=
  Function.update P j (boolPauliDoubleRotationTarget a (P j))

theorem finitePauliWeight_doubleRotationTarget
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    finitePauliWeight (finiteSingleSiteDoubleRotationTarget j a P) =
      finitePauliWeight P := by
  rw [finitePauliWeight, finitePauliWeight]
  congr 1
  ext s
  by_cases hs : s = j
  · subst s
    simp [finiteSingleSiteDoubleRotationTarget,
      boolPauliDoubleRotationTarget_eq_none_iff]
  · simp [finiteSingleSiteDoubleRotationTarget, hs]

theorem finiteLocalMatrix_update_twoTerm
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (P : σ → Matrix Bool Bool ℂ)
    (M N : Matrix Bool Bool ℂ) (c d : ℂ) :
    finiteLocalMatrix (Function.update P j (c • M + d • N)) =
      c • finiteLocalMatrix (Function.update P j M) +
        d • finiteLocalMatrix (Function.update P j N) := by
  ext x y
  simp only [finiteLocalMatrix, Matrix.smul_apply, Matrix.add_apply]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun s => Function.update P j (c • M + d • N) s (x s) (y s))
      (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ
      (fun s => Function.update P j M s (x s) (y s))
      (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ
      (fun s => Function.update P j N s (x s) (y s))
      (Finset.mem_univ j)]
  simp only [Function.update_self, Matrix.add_apply, Matrix.smul_apply]
  have hprodM :
      (∏ s ∈ Finset.univ.erase j,
          Function.update P j M s (x s) (y s)) =
        ∏ s ∈ Finset.univ.erase j, P s (x s) (y s) := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have hprodN :
      (∏ s ∈ Finset.univ.erase j,
          Function.update P j N s (x s) (y s)) =
        ∏ s ∈ Finset.univ.erase j, P s (x s) (y s) := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have hprodL :
      (∏ s ∈ Finset.univ.erase j,
          Function.update P j (c • M + d • N) s (x s) (y s)) =
        ∏ s ∈ Finset.univ.erase j, P s (x s) (y s) := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  rw [hprodM, hprodN, hprodL]
  ring

theorem finiteSingleSiteDoubleRotation_conj_finitePauliMatrix
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    finiteSingleSiteDoubleRotationGate j a * finitePauliMatrix P *
        finiteSingleSiteDoubleRotationGateInv j a =
      boolPauliDoubleRotationSourceCoeff a (P j) • finitePauliMatrix P +
        boolPauliDoubleRotationTargetCoeff a (P j) •
          finitePauliMatrix (finiteSingleSiteDoubleRotationTarget j a P) := by
  rw [finiteSingleSiteDoubleRotationGate,
    finiteSingleSiteDoubleRotationGateInv, finiteSingleSiteMatrix,
    finiteSingleSiteMatrix, finitePauliMatrix_eq_finiteLocalMatrix,
    finiteLocalMatrix_mul, finiteLocalMatrix_mul]
  let c := boolPauliDoubleRotationSourceCoeff a (P j)
  let d := boolPauliDoubleRotationTargetCoeff a (P j)
  let p' := boolPauliDoubleRotationTarget a (P j)
  have hpoint :
      (fun s =>
        (if s = j then boolPauliDoubleRotationGate a else 1) *
          boolPauliOption (P s) *
            (if s = j then boolPauliDoubleRotationGateInv a else 1)) =
      Function.update (fun s => boolPauliOption (P s)) j
        (c • boolPauliOption (P j) + d • boolPauliOption p') := by
    funext s
    by_cases hs : s = j
    · subst s
      simpa [c, d, p'] using boolPauliDoubleRotation_conj a (P j)
    · simp [hs]
  rw [hpoint, finiteLocalMatrix_update_twoTerm]
  have hsource : Function.update (fun s => boolPauliOption (P s)) j
      (boolPauliOption (P j)) = fun s => boolPauliOption (P s) := by
    funext s
    by_cases hs : s = j <;> simp [hs]
  rw [hsource]
  have htarget :
      Function.update (fun s => boolPauliOption (P s)) j (boolPauliOption p') =
        fun s => boolPauliOption (finiteSingleSiteDoubleRotationTarget j a P s) := by
    funext s
    by_cases hs : s = j <;>
      simp [finiteSingleSiteDoubleRotationTarget, hs, p']
  rw [finitePauliMatrix_eq_finiteLocalMatrix, htarget]

theorem finiteSingleSiteDoubleRotation_inv_conj_finitePauliMatrix
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    finiteSingleSiteDoubleRotationGateInv j a * finitePauliMatrix P *
        finiteSingleSiteDoubleRotationGate j a =
      boolPauliDoubleRotationSourceCoeff a (P j) • finitePauliMatrix P -
        boolPauliDoubleRotationTargetCoeff a (P j) •
          finitePauliMatrix (finiteSingleSiteDoubleRotationTarget j a P) := by
  rw [finiteSingleSiteDoubleRotationGate,
    finiteSingleSiteDoubleRotationGateInv, finiteSingleSiteMatrix,
    finiteSingleSiteMatrix, finitePauliMatrix_eq_finiteLocalMatrix,
    finiteLocalMatrix_mul, finiteLocalMatrix_mul]
  let c := boolPauliDoubleRotationSourceCoeff a (P j)
  let d := -boolPauliDoubleRotationTargetCoeff a (P j)
  let p' := boolPauliDoubleRotationTarget a (P j)
  have hpoint :
      (fun s =>
        (if s = j then boolPauliDoubleRotationGateInv a else 1) *
          boolPauliOption (P s) *
            (if s = j then boolPauliDoubleRotationGate a else 1)) =
      Function.update (fun s => boolPauliOption (P s)) j
        (c • boolPauliOption (P j) + d • boolPauliOption p') := by
    funext s
    by_cases hs : s = j
    · subst s
      simpa [c, d, p', sub_eq_add_neg] using
        boolPauliDoubleRotation_inv_conj a (P j)
    · simp [hs]
  rw [hpoint, finiteLocalMatrix_update_twoTerm]
  have hsource : Function.update (fun s => boolPauliOption (P s)) j
      (boolPauliOption (P j)) = fun s => boolPauliOption (P s) := by
    funext s
    by_cases hs : s = j <;> simp [hs]
  rw [hsource]
  have htarget :
      Function.update (fun s => boolPauliOption (P s)) j (boolPauliOption p') =
        fun s => boolPauliOption (finiteSingleSiteDoubleRotationTarget j a P s) := by
    funext s
    by_cases hs : s = j <;>
      simp [finiteSingleSiteDoubleRotationTarget, hs, p']
  rw [finitePauliMatrix_eq_finiteLocalMatrix, htarget]
  simp [c, d, sub_eq_add_neg]

def matrixConjugationLinearEquivOfTwoSidedInverse
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G H : Matrix κ κ ℂ) (hGH : G * H = 1) (hHG : H * G = 1) :
    Matrix κ κ ℂ ≃ₗ[ℂ] Matrix κ κ ℂ where
  toFun X := G * X * H
  invFun X := H * X * G
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp
  left_inv X := by
    calc
      H * (G * X * H) * G = (H * G) * X * (H * G) := by noncomm_ring
      _ = X := by rw [hHG]; simp
  right_inv X := by
    calc
      G * (H * X * G) * H = (G * H) * X * (G * H) := by noncomm_ring
      _ = X := by rw [hGH]; simp

def finiteSingleSiteDoubleRotationDoubledGate
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) : FiniteTwoReplicaMatrix σ :=
  finiteSingleSiteDoubleRotationGate j a ⊗ₖ
    finiteSingleSiteDoubleRotationGate j a

def finiteSingleSiteDoubleRotationDoubledGateInv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) : FiniteTwoReplicaMatrix σ :=
  finiteSingleSiteDoubleRotationGateInv j a ⊗ₖ
    finiteSingleSiteDoubleRotationGateInv j a

theorem finiteSingleSiteDoubleRotationDoubledGate_mul_inv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    finiteSingleSiteDoubleRotationDoubledGate j a *
        finiteSingleSiteDoubleRotationDoubledGateInv j a = 1 := by
  rw [finiteSingleSiteDoubleRotationDoubledGate,
    finiteSingleSiteDoubleRotationDoubledGateInv,
    ← Matrix.mul_kronecker_mul,
    finiteSingleSiteDoubleRotationGate_mul_inv,
    Matrix.one_kronecker_one]

theorem finiteSingleSiteDoubleRotationDoubledGate_inv_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    finiteSingleSiteDoubleRotationDoubledGateInv j a *
        finiteSingleSiteDoubleRotationDoubledGate j a = 1 := by
  rw [finiteSingleSiteDoubleRotationDoubledGate,
    finiteSingleSiteDoubleRotationDoubledGateInv,
    ← Matrix.mul_kronecker_mul,
    finiteSingleSiteDoubleRotationGate_inv_mul,
    Matrix.one_kronecker_one]

def finiteSingleSiteDoubleRotationDoubledConjugationEquiv
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) :
    FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ :=
  matrixConjugationLinearEquivOfTwoSidedInverse
    (finiteSingleSiteDoubleRotationDoubledGate j a)
    (finiteSingleSiteDoubleRotationDoubledGateInv j a)
    (finiteSingleSiteDoubleRotationDoubledGate_mul_inv j a)
    (finiteSingleSiteDoubleRotationDoubledGate_inv_mul j a)

@[simp] theorem finiteSingleSiteDoubleRotationDoubledConjugationEquiv_apply
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (X : FiniteTwoReplicaMatrix σ) :
    finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a X =
      finiteSingleSiteDoubleRotationDoubledGate j a * X *
        finiteSingleSiteDoubleRotationDoubledGateInv j a := rfl

@[simp] theorem finiteSingleSiteDoubleRotationDoubledConjugationEquiv_symm_apply
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (X : FiniteTwoReplicaMatrix σ) :
    (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm X =
      finiteSingleSiteDoubleRotationDoubledGateInv j a * X *
        finiteSingleSiteDoubleRotationDoubledGate j a := rfl

theorem finiteSingleSiteDoubleRotationDoubled_conj_collectivePauli
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    finiteSingleSiteDoubleRotationDoubledGate j a *
        (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) *
          finiteSingleSiteDoubleRotationDoubledGateInv j a =
      boolPauliDoubleRotationSourceCoeff a (P j) •
          (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) +
        boolPauliDoubleRotationTargetCoeff a (P j) •
          (finiteTwoReplicaPauliLeft
              (finiteSingleSiteDoubleRotationTarget j a P) +
            finiteTwoReplicaPauliRight
              (finiteSingleSiteDoubleRotationTarget j a P)) := by
  let G := finiteSingleSiteDoubleRotationGate j a
  let H := finiteSingleSiteDoubleRotationGateInv j a
  let A := finitePauliMatrix P
  let B := finitePauliMatrix (finiteSingleSiteDoubleRotationTarget j a P)
  let c := boolPauliDoubleRotationSourceCoeff a (P j)
  let d := boolPauliDoubleRotationTargetCoeff a (P j)
  have hGH : G * H = 1 := finiteSingleSiteDoubleRotationGate_mul_inv j a
  have hconj : G * A * H = c • A + d • B := by
    exact finiteSingleSiteDoubleRotation_conj_finitePauliMatrix j a P
  change (G ⊗ₖ G) *
      (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
          (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ A) * (H ⊗ₖ H) =
    c • (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ A) +
    d • (B ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ B)
  rw [Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hGH, hconj]
  simp only [Matrix.add_kronecker, Matrix.kronecker_add,
    Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

theorem finiteSingleSiteDoubleRotationDoubled_inv_conj_collectivePauli
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (j : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    finiteSingleSiteDoubleRotationDoubledGateInv j a *
        (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) *
          finiteSingleSiteDoubleRotationDoubledGate j a =
      boolPauliDoubleRotationSourceCoeff a (P j) •
          (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) -
        boolPauliDoubleRotationTargetCoeff a (P j) •
          (finiteTwoReplicaPauliLeft
              (finiteSingleSiteDoubleRotationTarget j a P) +
            finiteTwoReplicaPauliRight
              (finiteSingleSiteDoubleRotationTarget j a P)) := by
  let G := finiteSingleSiteDoubleRotationGate j a
  let H := finiteSingleSiteDoubleRotationGateInv j a
  let A := finitePauliMatrix P
  let B := finitePauliMatrix (finiteSingleSiteDoubleRotationTarget j a P)
  let c := boolPauliDoubleRotationSourceCoeff a (P j)
  let d := boolPauliDoubleRotationTargetCoeff a (P j)
  let e := -d
  have hHG : H * G = 1 := finiteSingleSiteDoubleRotationGate_inv_mul j a
  have hconj : H * A * G = c • A + e • B := by
    simpa [e, sub_eq_add_neg, neg_smul] using
      finiteSingleSiteDoubleRotation_inv_conj_finitePauliMatrix j a P
  change (H ⊗ₖ H) *
      (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
          (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ A) * (G ⊗ₖ G) =
    c • (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ A) -
    d • (B ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ B)
  rw [Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, hHG, hconj]
  rw [sub_eq_add_neg, ← neg_smul]
  change _ = c • (A ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ A) +
    e • (B ⊗ₖ (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) + 1 ⊗ₖ B)
  simp only [Matrix.add_kronecker, Matrix.kronecker_add,
    Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

theorem ringCommutator_twoSidedInverse_conjugation
    {R : Type*} [Ring R] (G H K X : R) (hGH : G * H = 1) :
    G * ringCommutator K (H * X * G) * H =
      ringCommutator (G * K * H) X := by
  unfold ringCommutator
  calc
    G * (K * (H * X * G) - (H * X * G) * K) * H =
        (G * K * H) * X * (G * H) -
          (G * H) * X * (G * K * H) := by noncomm_ring
    _ = (G * K * H) * X - X * (G * K * H) := by rw [hGH]; simp

theorem finiteSingleSiteDoubleRotation_conjugatedQLocalCommutator_mem_span
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (j : σ) (a : Fin 3) (P : FiniteQLocalPauliLabel σ q) :
    ((((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a) :
        FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
      ((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm :
        FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) ∈
      linearFamilyOperatorSpan
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) := by
  let P' := finiteSingleSiteDoubleRotationTarget j a P.1
  let Pq' : FiniteQLocalPauliLabel σ q := ⟨P', by
    rw [finitePauliWeight_doubleRotationTarget]
    exact P.2⟩
  let c := boolPauliDoubleRotationSourceCoeff a (P.1 j)
  let d := boolPauliDoubleRotationTargetCoeff a (P.1 j)
  have heq :
      ((((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a) :
          FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
        ((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm :
          FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) =
        c • finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P +
          d • finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q Pq' := by
    apply LinearMap.ext
    intro X
    change finiteSingleSiteDoubleRotationDoubledGate j a *
        finiteTwoReplicaCollectiveCommutator P.1
          (finiteSingleSiteDoubleRotationDoubledGateInv j a * X *
            finiteSingleSiteDoubleRotationDoubledGate j a) *
          finiteSingleSiteDoubleRotationDoubledGateInv j a = _
    rw [finiteTwoReplicaCollectiveCommutator, ← ringCommutator_add_left',
      ringCommutator_twoSidedInverse_conjugation _ _ _ _
        (finiteSingleSiteDoubleRotationDoubledGate_mul_inv j a),
      finiteSingleSiteDoubleRotationDoubled_conj_collectivePauli,
      ringCommutator_add_left',
      ringCommutator_smul_left, ringCommutator_smul_left,
      ringCommutator_add_left', ringCommutator_add_left']
    change _ = c • finiteTwoReplicaCollectiveCommutator P.1 X +
      d • finiteTwoReplicaCollectiveCommutator P' X
    rw [finiteTwoReplicaCollectiveCommutator,
      finiteTwoReplicaCollectiveCommutator]
  rw [heq]
  exact (linearFamilyOperatorSpan _).add_mem
    ((linearFamilyOperatorSpan _).smul_mem c
      (Submodule.subset_span ⟨P, rfl⟩))
    ((linearFamilyOperatorSpan _).smul_mem d
      (Submodule.subset_span ⟨Pq', rfl⟩))

theorem finiteSingleSiteDoubleRotation_inverseConjugatedQLocalCommutator_mem_span
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (j : σ) (a : Fin 3) (P : FiniteQLocalPauliLabel σ q) :
    ((((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm :
        FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
      (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a :
        FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) ∈
      linearFamilyOperatorSpan
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) := by
  let P' := finiteSingleSiteDoubleRotationTarget j a P.1
  let Pq' : FiniteQLocalPauliLabel σ q := ⟨P', by
    rw [finitePauliWeight_doubleRotationTarget]
    exact P.2⟩
  let c := boolPauliDoubleRotationSourceCoeff a (P.1 j)
  let d := boolPauliDoubleRotationTargetCoeff a (P.1 j)
  have heq :
      ((((finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a).symm :
          FiniteTwoReplicaMatrix σ ≃ₗ[ℂ] FiniteTwoReplicaMatrix σ).toLinearMap.comp
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P)).comp
        (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a :
          FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ)) =
        c • finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q P -
          d • finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q Pq' := by
    apply LinearMap.ext
    intro X
    change finiteSingleSiteDoubleRotationDoubledGateInv j a *
        finiteTwoReplicaCollectiveCommutator P.1
          (finiteSingleSiteDoubleRotationDoubledGate j a * X *
            finiteSingleSiteDoubleRotationDoubledGateInv j a) *
          finiteSingleSiteDoubleRotationDoubledGate j a = _
    rw [finiteTwoReplicaCollectiveCommutator, ← ringCommutator_add_left',
      ringCommutator_twoSidedInverse_conjugation _ _ _ _
        (finiteSingleSiteDoubleRotationDoubledGate_inv_mul j a),
      finiteSingleSiteDoubleRotationDoubled_inv_conj_collectivePauli,
      sub_eq_add_neg, ringCommutator_add_left', ringCommutator_neg_left,
      ringCommutator_smul_left, ringCommutator_add_left']
    change _ = c • finiteTwoReplicaCollectiveCommutator P.1 X -
      d • finiteTwoReplicaCollectiveCommutator P' X
    rw [finiteTwoReplicaCollectiveCommutator,
      finiteTwoReplicaCollectiveCommutator]
    rw [ringCommutator_smul_left, ringCommutator_add_left']
    module
  rw [heq]
  exact (linearFamilyOperatorSpan _).sub_mem
    ((linearFamilyOperatorSpan _).smul_mem c
      (Submodule.subset_span ⟨P, rfl⟩))
    ((linearFamilyOperatorSpan _).smul_mem d
      (Submodule.subset_span ⟨Pq', rfl⟩))

theorem finiteTwoReplicaQLocal_greatestMaximizer_doubleRotation_fixed
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix σ))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix σ),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U →
      W ≤ U)
    (j : σ) (a : Fin 3) :
    U.map (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a :
      FiniteTwoReplicaMatrix σ →ₗ[ℂ] FiniteTwoReplicaMatrix σ) = U := by
  apply linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant
      (finiteTwoReplicaQLocalCollectiveCommutatorLinear σ q) U
      (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a)
      (finiteSingleSiteDoubleRotationDoubledConjugationEquiv j a) hgreatest
  · exact finiteSingleSiteDoubleRotation_conjugatedQLocalCommutator_mem_span
      q j a
  · exact finiteSingleSiteDoubleRotation_inverseConjugatedQLocalCommutator_mem_span
      q j a

end

end GaloisForLFunctions.HTGeometry
