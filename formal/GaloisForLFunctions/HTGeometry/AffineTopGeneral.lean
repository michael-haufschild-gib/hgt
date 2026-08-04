import GaloisForLFunctions.HTGeometry.ColumnPencilDeterminant
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Complex.Basic

/-!
# The affine top reduction over an arbitrary model

For a variable driven by `δ x = A·x + B` with `A, B` free of `x`, every jet of `x` is again affine in
it, so the output-jet Jacobian is a column pencil whose constant column is the sequence of homogeneous
coefficients.  Extracting the top coefficient and expanding along the first row leaves the Jacobian of
the positive coefficients — one variable fewer.

This is the model-independent form of the reduction.  Where the polynomial version substitutes a fresh
variable for `x`, here the corresponding fact is an injective algebra map

`Polynomial S → R`,  `T ↦ x`,

for the subalgebra `S` of everything free of `x`; that is exactly transcendence of `x` over `S`, and
it is available in a fraction field where no substitution out of the model exists.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The homogeneous coefficient of the `i`-th jet of an affinely driven element. -/
noncomputable def genJetA (δ : Derivation ℂ R R) (A : R) : ℕ → R
  | 0 => 1
  | (i + 1) => δ (genJetA δ A i) + genJetA δ A i * A

/-- The inhomogeneous coefficient of the `i`-th jet of an affinely driven element. -/
noncomputable def genJetB (δ : Derivation ℂ R R) (A B : R) : ℕ → R
  | 0 => 0
  | (i + 1) => δ (genJetB δ A B i) + genJetA δ A i * B

@[simp] theorem genJetA_zero (δ : Derivation ℂ R R) (A : R) : genJetA δ A 0 = 1 := rfl

@[simp] theorem genJetB_zero (δ : Derivation ℂ R R) (A B : R) : genJetB δ A B 0 = 0 := rfl

theorem genJetA_succ (δ : Derivation ℂ R R) (A : R) (i : ℕ) :
    genJetA δ A (i + 1) = δ (genJetA δ A i) + genJetA δ A i * A := rfl

theorem genJetB_succ (δ : Derivation ℂ R R) (A B : R) (i : ℕ) :
    genJetB δ A B (i + 1) = δ (genJetB δ A B i) + genJetA δ A i * B := rfl

/-- **The jets of an affinely driven element.** -/
theorem iterate_of_affine_law_general {δ : Derivation ℂ R R} {x A B : R}
    (hlaw : δ x = A * x + B) (i : ℕ) :
    ((δ : R → R)^[i]) x = genJetA δ A i * x + genJetB δ A B i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_add, Derivation.leibniz, hlaw,
        genJetA_succ, genJetB_succ]
      simp only [smul_eq_mul]
      ring

/-- The element's own derivation sees only the homogeneous coefficient. -/
theorem top_of_affine_general {δ dtop : Derivation ℂ R R} {x A B : R}
    (hlaw : δ x = A * x + B) (hx : dtop x = 1)
    (hA : ∀ i, dtop (genJetA δ A i) = 0) (hB : ∀ i, dtop (genJetB δ A B i) = 0) (i : ℕ) :
    dtop (((δ : R → R)^[i]) x) = genJetA δ A i := by
  rw [iterate_of_affine_law_general hlaw i, map_add, hB i, add_zero, Derivation.leibniz, hx,
    hA i]
  simp

/-- Every other derivation is affine in the element. -/
theorem low_of_affine_general {δ dlow : Derivation ℂ R R} {x A B : R}
    (hlaw : δ x = A * x + B) (hx : dlow x = 0) (i : ℕ) :
    dlow (((δ : R → R)^[i]) x) = dlow (genJetB δ A B i) + x * dlow (genJetA δ A i) := by
  rw [iterate_of_affine_law_general hlaw i, map_add, Derivation.leibniz, hx]
  simp only [smul_eq_mul, mul_zero]
  ring

/-! ## Stability -/

theorem genJetA_mem_general {δ : Derivation ℂ R R} {S : Subalgebra ℂ R}
    (hS : ∀ z ∈ S, δ z ∈ S) {A : R} (hA : A ∈ S) (i : ℕ) : genJetA δ A i ∈ S := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [genJetA_succ]
      exact Subalgebra.add_mem _ (hS _ ih) (Subalgebra.mul_mem _ ih hA)

theorem genJetB_mem_general {δ : Derivation ℂ R R} {S : Subalgebra ℂ R}
    (hS : ∀ z ∈ S, δ z ∈ S) {A B : R} (hA : A ∈ S) (hB : B ∈ S) (i : ℕ) :
    genJetB δ A B i ∈ S := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [genJetB_succ]
      exact Subalgebra.add_mem _ (hS _ ih)
        (Subalgebra.mul_mem _ (genJetA_mem_general hS hA i) hB)

/-! ## The determinant reduction -/

/-- **Observability of an affinely driven element reduces to that of its driver.**  The hypotheses are
the affine law, stability of the free subalgebra, the normalisations `d_top x = 1` and `d_j x = 0`,
and transcendence of `x` over the free subalgebra. -/
theorem det_ne_zero_of_affine_top_general {n : ℕ} {δ dtop : Derivation ℂ R R}
    {c : Fin n → Derivation ℂ R R} {S : Subalgebra ℂ R} {x A B : R}
    (hlaw : δ x = A * x + B)
    (hδS : ∀ z ∈ S, δ z ∈ S) (hA : A ∈ S) (hB : B ∈ S)
    (htopx : dtop x = 1) (htopS : ∀ z ∈ S, dtop z = 0)
    (hcx : ∀ j, c j x = 0) (hcS : ∀ j, ∀ z ∈ S, c j z ∈ S)
    (hinj : Function.Injective (Polynomial.aeval x : Polynomial S →ₐ[S] R))
    (hsub : (Matrix.of fun i j : Fin n => c j (genJetA δ A ((i : ℕ) + 1))).det ≠ 0) :
    (Matrix.of fun i j : Fin (n + 1) =>
        Fin.lastCases (motive := fun _ => R)
          (dtop (((δ : R → R)^[(i : ℕ)]) x))
          (fun j' : Fin n => c j' (((δ : R → R)^[(i : ℕ)]) x)) j).det ≠ 0 := by
  classical
  have hAmem : ∀ i, genJetA δ A i ∈ S := genJetA_mem_general hδS hA
  have hBmem : ∀ i, genJetB δ A B i ∈ S := genJetB_mem_general hδS hA hB
  have hAtop : ∀ i, dtop (genJetA δ A i) = 0 := fun i => htopS _ (hAmem i)
  have hBtop : ∀ i, dtop (genJetB δ A B i) = 0 := fun i => htopS _ (hBmem i)
  -- the entries, as elements of the free subalgebra
  set aS : Fin n → Fin (n + 1) → S :=
    fun j i => ⟨c j (genJetB δ A B (i : ℕ)), hcS j _ (hBmem (i : ℕ))⟩ with haSdef
  set bS : Fin n → Fin (n + 1) → S :=
    fun j i => ⟨c j (genJetA δ A (i : ℕ)), hcS j _ (hAmem (i : ℕ))⟩ with hbSdef
  set wS : Fin (n + 1) → S := fun i => ⟨genJetA δ A (i : ℕ), hAmem (i : ℕ)⟩ with hwSdef
  have hmap : (Polynomial.aeval x : Polynomial S →ₐ[S] R).toRingHom.mapMatrix
      (columnPencil aS bS wS)
      = Matrix.of fun i j : Fin (n + 1) =>
          Fin.lastCases (motive := fun _ => R)
            (dtop (((δ : R → R)^[(i : ℕ)]) x))
            (fun j' : Fin n => c j' (((δ : R → R)^[(i : ℕ)]) x)) j := by
    funext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    refine Fin.lastCases ?_ ?_ j
    · simp only [Matrix.of_apply, Fin.lastCases_last, columnPencil]
      rw [show (Polynomial.aeval x : Polynomial S →ₐ[S] R).toRingHom (Polynomial.C (wS i))
          = Polynomial.aeval x (Polynomial.C (wS i)) from rfl, Polynomial.aeval_C]
      rw [top_of_affine_general hlaw htopx hAtop hBtop (i : ℕ)]
      rfl
    · intro j'
      simp only [Matrix.of_apply, Fin.lastCases_castSucc, columnPencil]
      rw [show (Polynomial.aeval x : Polynomial S →ₐ[S] R).toRingHom
            (Polynomial.C (aS j' i) + Polynomial.X * Polynomial.C (bS j' i))
          = Polynomial.aeval x (Polynomial.C (aS j' i) + Polynomial.X * Polynomial.C (bS j' i))
          from rfl]
      rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
        low_of_affine_general hlaw (hcx j') (i : ℕ)]
      rfl
  intro hzero
  have hpencil : (columnPencil aS bS wS).det = 0 := by
    refine hinj ?_
    rw [map_zero]
    have := congrArg Matrix.det hmap
    rw [← RingHom.map_det] at this
    rw [show (Polynomial.aeval x : Polynomial S →ₐ[S] R) (columnPencil aS bS wS).det
        = (Polynomial.aeval x : Polynomial S →ₐ[S] R).toRingHom (columnPencil aS bS wS).det
        from rfl, this, hzero]
  have hlead : (columnLeading bS wS).det = 0 := by
    rw [← coeff_det_columnPencil aS bS wS, hpencil, Polynomial.coeff_zero]
  have hw0 : wS 0 = 1 := by
    rw [hwSdef]
    exact Subtype.ext (by simp)
  have hb0 : ∀ j : Fin n, bS j 0 = 0 := by
    intro j
    rw [hbSdef]
    refine Subtype.ext ?_
    simp only []
    rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, genJetA_zero]
    simp
  have hminor : (Matrix.of fun i j : Fin n => bS j i.succ).det = 0 := by
    have hexp := det_columnLeading_of_row_zero bS wS hw0 hb0
    rw [hexp] at hlead
    have hmul := congrArg (fun z : S => (-1 : S) ^ n * z) hlead
    simp only [mul_zero, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow] at hmul
    exact hmul
  refine hsub ?_
  have hval : (Matrix.of fun i j : Fin n => c j (genJetA δ A ((i : ℕ) + 1)))
      = (Subalgebra.val S).toRingHom.mapMatrix (Matrix.of fun i j : Fin n => bS j i.succ) := by
    funext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [hbSdef, Fin.val_succ]
  rw [hval, ← RingHom.map_det, hminor]
  simp

end GaloisForLFunctions.HTGeometry
