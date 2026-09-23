import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Reflection-positive Hankel kernels and quantum moments

Osterwalder--Schrader reflection positivity turns a reflected Euclidean kernel into a Hilbert
Gram form.  For the discrete additive semigroup, the reflected kernel is Hankel: its entries have
the form `m (i + j)`.  This file records the finite coefficient identity needed by the moment
infrastructure: if `m (i + j)` is the Gram value of two state vectors, then the moment functional
of every polynomial square is exactly a Hilbert norm square.

Both real and complex Hilbert spaces are supported.  The final pair of theorems supplies the
standard bounded-observable specialization: vacuum moments of a self-adjoint observable form the
required reflected Gram orbit.  No evolution parameter or spectral measure is introduced.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

noncomputable section

private theorem sum_toFn_smul_X_pow_eq (p : Polynomial ℝ) :
    (∑ i : Fin (p.natDegree + 1),
      Polynomial.toFn (p.natDegree + 1) p i • X ^ (i : ℕ)) = p := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  have hp : Polynomial.ofFn N c = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  change (∑ i : Fin N, c i • X ^ (i : ℕ)) = p
  calc
    (∑ i : Fin N, c i • X ^ (i : ℕ)) =
        ∑ i : Fin N, Polynomial.monomial (i : ℕ) (c i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
    _ = Polynomial.ofFn N c := (Polynomial.ofFn_eq_sum_monomial c).symm
    _ = p := hp

/-! ## Real reflection-positive packets -/

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state packet read by the coefficients of one finite real polynomial. -/
def reflectionPositiveStateVector (v : ℕ → E) {n : ℕ} (c : Fin n → ℝ) : E :=
  ∑ i : Fin n, c i • v (i : ℕ)

/-- A reflected Hankel Gram relation turns the packet inner product into the Hankel quadratic
form. -/
theorem inner_reflectionPositiveStateVector_self
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j))
    {n : ℕ} (c : Fin n → ℝ) :
    inner ℝ (reflectionPositiveStateVector v c)
        (reflectionPositiveStateVector v c) =
      ∑ i : Fin n, ∑ j : Fin n, c i * c j * m ((i : ℕ) + (j : ℕ)) := by
  rw [reflectionPositiveStateVector, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, hgram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

/-- **Real reflection-positive norm-square law.**  The moment functional on a polynomial square
is exactly the squared norm of its reflected state packet. -/
theorem momentFunctional_pow_two_eq_reflectionPositiveStateVector_normSq
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j))
    (p : Polynomial ℝ) :
    momentFunctional m (p ^ (2 : ℕ)) =
      ‖reflectionPositiveStateVector v
        (Polynomial.toFn (p.natDegree + 1) p)‖ ^ (2 : ℕ) := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  change momentFunctional m (p ^ (2 : ℕ)) = ‖reflectionPositiveStateVector v c‖ ^ (2 : ℕ)
  calc
    momentFunctional m (p ^ (2 : ℕ)) =
        momentFunctional m ((∑ i : Fin N, c i • X ^ (i : ℕ)) ^ (2 : ℕ)) := by
      rw [sum_toFn_smul_X_pow_eq]
    _ = ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * m ((i : ℕ) + (j : ℕ)) :=
      momentFunctional_sq_eq_hankelForm m c
    _ = inner ℝ (reflectionPositiveStateVector v c)
        (reflectionPositiveStateVector v c) :=
      (inner_reflectionPositiveStateVector_self m v hgram c).symm
    _ = ‖reflectionPositiveStateVector v c‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq _

/-- Real reflection-positive Gram data make the moment functional nonnegative on every square. -/
theorem momentFunctional_pow_two_nonneg_of_reflectionPositiveGram
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j))
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional m (p ^ (2 : ℕ)) := by
  rw [momentFunctional_pow_two_eq_reflectionPositiveStateVector_normSq m v hgram]
  positivity

/-- Linear independence of one finite reflected packet upgrades Hankel semidefiniteness to strict
positive definiteness.  This is the algebraic form of a state orbit having no polynomial
annihilator below degree `n`. -/
theorem momentHankelMatrix_posDef_of_reflectionPositiveGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j))
    (n : ℕ) (hli : LinearIndependent ℝ (fun i : Fin n => v (i : ℕ))) :
    (momentHankelMatrix m n).PosDef := by
  have hmatrix : momentHankelMatrix m n =
      Matrix.gram ℝ (fun i : Fin n => v (i : ℕ)) := by
    ext i j
    exact (hgram i j).symm
  rw [hmatrix]
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- Linear independence of a reflected packet makes its finite Hankel determinant strictly
positive. -/
theorem det_momentHankelMatrix_pos_of_reflectionPositiveGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j))
    (n : ℕ) (hli : LinearIndependent ℝ (fun i : Fin n => v (i : ℕ))) :
    0 < (momentHankelMatrix m n).det :=
  (momentHankelMatrix_posDef_of_reflectionPositiveGram m v hgram n hli).det_pos

/-! ## Complex reflection-positive packets -/

/-- The complex Hilbert-space packet with real polynomial coefficients. -/
def complexReflectionPositiveStateVector
    {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : ℕ → F) {n : ℕ} (c : Fin n → ℝ) : F :=
  ∑ i : Fin n, (c i : ℂ) • v (i : ℕ)

/-- The real part of the complex packet inner product is the real Hankel quadratic form. -/
theorem re_inner_complexReflectionPositiveStateVector_self
    {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
    (m : ℕ → ℝ) (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ))
    {n : ℕ} (c : Fin n → ℝ) :
    (inner ℂ (complexReflectionPositiveStateVector v c)
        (complexReflectionPositiveStateVector v c)).re =
      ∑ i : Fin n, ∑ j : Fin n, c i * c j * m ((i : ℕ) + (j : ℕ)) := by
  rw [complexReflectionPositiveStateVector, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, hgram,
    Complex.conj_ofReal]
  simp
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Complex reflection-positive norm-square law.**  This is the form consumed directly by the
complex Sonin and operator spaces in `RHTower`. -/
theorem momentFunctional_pow_two_eq_complexReflectionPositiveStateVector_normSq
    {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
    (m : ℕ → ℝ) (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ))
    (p : Polynomial ℝ) :
    momentFunctional m (p ^ (2 : ℕ)) =
      ‖complexReflectionPositiveStateVector v
        (Polynomial.toFn (p.natDegree + 1) p)‖ ^ (2 : ℕ) := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  change momentFunctional m (p ^ (2 : ℕ)) = ‖complexReflectionPositiveStateVector v c‖ ^ (2 : ℕ)
  calc
    momentFunctional m (p ^ (2 : ℕ)) =
        momentFunctional m ((∑ i : Fin N, c i • X ^ (i : ℕ)) ^ (2 : ℕ)) := by
      rw [sum_toFn_smul_X_pow_eq]
    _ = ∑ i : Fin N, ∑ j : Fin N,
        c i * c j * m ((i : ℕ) + (j : ℕ)) :=
      momentFunctional_sq_eq_hankelForm m c
    _ = (inner ℂ (complexReflectionPositiveStateVector v c)
        (complexReflectionPositiveStateVector v c)).re :=
      (re_inner_complexReflectionPositiveStateVector_self m v hgram c).symm
    _ = ‖complexReflectionPositiveStateVector v c‖ ^ (2 : ℕ) :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- Complex reflection-positive Gram data make the real moment functional nonnegative on every
square. -/
theorem momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram
    {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]
    (m : ℕ → ℝ) (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ))
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional m (p ^ (2 : ℕ)) := by
  rw [momentFunctional_pow_two_eq_complexReflectionPositiveStateVector_normSq m v hgram]
  positivity

/-! ## Bounded self-adjoint observables -/

/-- Powers of a bounded self-adjoint observable form a reflected Hankel orbit around every state:
`inner (A^i omega) (A^j omega) = inner omega (A^(i+j) omega)`. -/
theorem inner_selfAdjointObservableOrbit
    {𝕜 : Type*} [RCLike 𝕜]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : F →L[𝕜] F) (omega : F) (hA : IsSelfAdjoint A) (i j : ℕ) :
    inner 𝕜 ((A ^ i) omega) ((A ^ j) omega) =
      inner 𝕜 omega ((A ^ (i + j)) omega) := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.pow i)
  calc
    inner 𝕜 ((A ^ i) omega) ((A ^ j) omega) =
        inner 𝕜 omega ((A ^ i) ((A ^ j) omega)) := hsym omega ((A ^ j) omega)
    _ = inner 𝕜 omega (((A ^ i) * (A ^ j)) omega) := by
      rw [mul_apply_eq_comp]
    _ = inner 𝕜 omega ((A ^ (i + j)) omega) := by rw [pow_add]

/-- Vacuum moments of a real bounded self-adjoint observable are positive on polynomial squares. -/
theorem momentFunctional_pow_two_nonneg_of_selfAdjointObservable
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (m : ℕ → ℝ) (A : F →L[ℝ] F) (omega : F) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, m n = inner ℝ omega ((A ^ n) omega))
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional m (p ^ (2 : ℕ)) := by
  apply momentFunctional_pow_two_nonneg_of_reflectionPositiveGram m
    (fun n => (A ^ n) omega)
  intro i j
  rw [inner_selfAdjointObservableOrbit A omega hA, hmom]

/-- Vacuum moments of a complex bounded self-adjoint observable are positive on real polynomial
squares. -/
theorem momentFunctional_pow_two_nonneg_of_complexSelfAdjointObservable
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (m : ℕ → ℝ) (A : F →L[ℂ] F) (omega : F) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, inner ℂ omega ((A ^ n) omega) = (m n : ℂ))
    (p : Polynomial ℝ) :
    0 ≤ momentFunctional m (p ^ (2 : ℕ)) := by
  apply momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram m
    (fun n => (A ^ n) omega)
  intro i j
  rw [inner_selfAdjointObservableOrbit A omega hA, hmom]

end

end HTGeometry
