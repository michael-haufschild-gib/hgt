import GaloisForLFunctions.HTGeometry.EvolvedStateBundlePairing
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Schrödinger orbit in algebraic coordinates

The evolved state `e^{-itH}Ω` is a linear combination of the spectral phases
`exp(-i t E_j)` whose coefficient matrix is *algebraic* whenever `H` and `Ω` are: the `j`-th
coefficient vector is `ℓ_j(H) *ᵥ Ω`, where `ℓ_j` is the Lagrange interpolation basis polynomial at
the spectrum.  Individual eigenvectors are not algebraic in any canonical way -- they are only
defined up to a phase -- but the *rank-one projector* `ℓ_j(H)` is, and that is all the transcendence
argument needs.

## Main results

* `aeval_mulVec_of_eigenvector` — a polynomial in a matrix acts on an eigenvector by evaluation.
* `aeval_lagrangeBasis_mulVec` — `ℓ_j(H) *ᵥ Ω = ⟨e_j, Ω⟩ • e_j`.
* `unitaryEvolution_mulVec_apply_eq_sum_lagrange` — **the orbit is the spectral-phase combination
  with the Lagrange coefficient matrix.**
* `det_lagrangeStateMatrix_ne_zero` — **that matrix is invertible when `Ω` is cyclic.**
-/

open Matrix Polynomial ComplexConjugate
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace AlgebraicOrbit

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Polynomials in a matrix act on eigenvectors by evaluation -/

/-- Powers of a matrix act on an eigenvector by the power of the eigenvalue. -/
theorem matrixPow_mulVec_eigen {R : Type*} [CommRing R] {H : Matrix α α R} {v : α → R} {μ : R}
    (h : H *ᵥ v = μ • v) : ∀ n : ℕ, H ^ n *ᵥ v = μ ^ n • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- The scalar matrix acts by scalar multiplication. -/
theorem algebraMap_mulVec {R : Type*} [CommRing R] (a : R) (v : α → R) :
    (algebraMap R (Matrix α α R) a) *ᵥ v = a • v := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **A polynomial in a matrix acts on an eigenvector by its value at the eigenvalue.** -/
theorem aeval_mulVec_of_eigenvector {R : Type*} [CommRing R] {H : Matrix α α R} {v : α → R}
    {μ : R} (h : H *ᵥ v = μ • v) (p : R[X]) :
    (Polynomial.aeval H p) *ᵥ v = p.eval μ • v := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro q r hq hr
    rw [map_add, Matrix.add_mulVec, hq, hr, Polynomial.eval_add, add_smul]
  · intro n a
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Matrix.mulVec_mulVec,
      matrixPow_mulVec_eigen h n, Matrix.mulVec_smul, algebraMap_mulVec, smul_smul, mul_comm]

/-! ### The Lagrange coefficient matrix of the spectrum -/

/-- The Lagrange interpolation basis at the (complex) eigenvalues. -/
def spectralNodes (lam : α → ℝ) : α → ℂ := fun i => ((lam i : ℝ) : ℂ)

theorem injective_spectralNodes {lam : α → ℝ} (h : Function.Injective lam) :
    Function.Injective (spectralNodes lam) :=
  fun _ _ hab => h (Complex.ofReal_injective hab)

/-- **The Lagrange projector applied to a state is its spectral component.** -/
theorem aeval_lagrangeBasis_mulVec {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) (Ω : α → ℂ) (j : α) :
    (Polynomial.aeval H (Lagrange.basis Finset.univ (spectralNodes lam) j)) *ᵥ Ω
      = finiteComplexInner (e j) Ω • e j := by
  classical
  have hinjOn : Set.InjOn (spectralNodes lam) (Finset.univ : Finset α) :=
    fun _ _ _ _ hab => injective_spectralNodes hinj hab
  have heval : ∀ k : α,
      (Lagrange.basis Finset.univ (spectralNodes lam) j).eval (spectralNodes lam k)
        = if k = j then 1 else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl]
      exact Lagrange.eval_basis_self hinjOn (Finset.mem_univ k)
    · rw [if_neg hk]
      exact Lagrange.eval_basis_of_ne (fun hcon => hk hcon.symm) (Finset.mem_univ k)
  conv_lhs => rw [← heb.complete Ω]
  rw [Matrix.mulVec_sum]
  have hterm : ∀ k ∈ (Finset.univ : Finset α),
      (Polynomial.aeval H (Lagrange.basis Finset.univ (spectralNodes lam) j)) *ᵥ
          (finiteComplexInner (e k) Ω • e k)
        = if k = j then finiteComplexInner (e j) Ω • e j else 0 := by
    intro k _
    rw [Matrix.mulVec_smul,
      aeval_mulVec_of_eigenvector (μ := spectralNodes lam k) (heb.eigen k), heval k]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_pos rfl, one_smul]
    · rw [if_neg hk, if_neg hk, zero_smul, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ j
    (fun _ => finiteComplexInner (e j) Ω • e j), if_pos (Finset.mem_univ j)]

/-- The matrix whose `j`-th column is the `j`-th spectral component of `Ω`. -/
def lagrangeStateMatrix (H : Matrix α α ℂ) (lam : α → ℝ) (Ω : α → ℂ) : Matrix α α ℂ :=
  Matrix.of fun i j =>
    ((Polynomial.aeval H (Lagrange.basis Finset.univ (spectralNodes lam) j)) *ᵥ Ω) i

theorem lagrangeStateMatrix_apply (H : Matrix α α ℂ) (lam : α → ℝ) (Ω : α → ℂ) (i j : α) :
    lagrangeStateMatrix H lam Ω i j
      = ((Polynomial.aeval H (Lagrange.basis Finset.univ (spectralNodes lam) j)) *ᵥ Ω) i := rfl

/-- **The orbit is the spectral-phase combination with the Lagrange coefficient matrix.** -/
theorem unitaryEvolution_mulVec_apply_eq_sum_lagrange {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (Ω : α → ℂ) (t : ℝ) (i : α) :
    (unitaryEvolution H t *ᵥ Ω) i
      = ∑ j, lagrangeStateMatrix H lam Ω i j *
          Complex.exp (-(Complex.I * ((t : ℂ) * ((lam j : ℝ) : ℂ)))) := by
  classical
  rw [unitaryEvolution_mulVec_eq_sum heb Ω t]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lagrangeStateMatrix_apply, aeval_lagrangeBasis_mulVec heb hinj Ω j]
  show (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * ((t : ℂ) * ((lam j : ℝ) : ℂ)))))
      * e j i = (finiteComplexInner (e j) Ω * e j i) *
        Complex.exp (-(Complex.I * ((t : ℂ) * ((lam j : ℝ) : ℂ))))
  ring

/-! ### Invertibility of the coefficient matrix -/

/-- The eigenbasis as a matrix: its `j`-th column is `e j`. -/
def eigenColumnMatrix (e : α → α → ℂ) : Matrix α α ℂ := Matrix.of fun i j => e j i

theorem conjTranspose_mul_eigenColumnMatrix {e : α → α → ℂ}
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    (eigenColumnMatrix e)ᴴ * eigenColumnMatrix e = 1 := by
  classical
  ext j k
  rw [Matrix.mul_apply]
  have hj : ∀ i : α, (eigenColumnMatrix e)ᴴ j i * eigenColumnMatrix e i k
      = conj (e j i) * e k i := by
    intro i
    rw [Matrix.conjTranspose_apply]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hj i)]
  rw [show ∑ i, conj (e j i) * e k i = finiteComplexInner (e j) (e k) from rfl, horth j k,
    Matrix.one_apply]

theorem det_eigenColumnMatrix_ne_zero {e : α → α → ℂ}
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    (eigenColumnMatrix e).det ≠ 0 := by
  intro h0
  have hdet := congrArg Matrix.det (conjTranspose_mul_eigenColumnMatrix horth)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at hdet
  exact zero_ne_one hdet

theorem lagrangeStateMatrix_eq_mul_diagonal {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) (Ω : α → ℂ) :
    lagrangeStateMatrix H lam Ω
      = eigenColumnMatrix e * Matrix.diagonal (fun j => finiteComplexInner (e j) Ω) := by
  classical
  ext i j
  rw [lagrangeStateMatrix_apply, aeval_lagrangeBasis_mulVec heb hinj Ω j,
    Matrix.mul_diagonal]
  show finiteComplexInner (e j) Ω * e j i = e j i * finiteComplexInner (e j) Ω
  ring

/-- **The Lagrange coefficient matrix is invertible when no spectral component vanishes.** -/
theorem det_lagrangeStateMatrix_ne_zero {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam) (Ω : α → ℂ)
    (hc : ∀ j, finiteComplexInner (e j) Ω ≠ 0) :
    (lagrangeStateMatrix H lam Ω).det ≠ 0 := by
  rw [lagrangeStateMatrix_eq_mul_diagonal heb hinj Ω, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (det_eigenColumnMatrix_ne_zero heb.orth)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hc j)

/-! ### Cyclicity makes every spectral component nonzero -/

theorem finiteComplexInner_add_right (u x y : α → ℂ) :
    finiteComplexInner u (x + y) = finiteComplexInner u x + finiteComplexInner u y := by
  rw [finiteComplexInner, finiteComplexInner, finiteComplexInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring

/-- The spectral coordinate functional is an eigenfunctional of the Hamiltonian. -/
theorem finiteComplexInner_mulVec {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (j : α) (ψ : α → ℂ) :
    finiteComplexInner (e j) (H *ᵥ ψ) = ((lam j : ℝ) : ℂ) * finiteComplexInner (e j) ψ := by
  classical
  conv_lhs => rw [← heb.complete ψ]
  rw [Matrix.mulVec_sum]
  have hterm : ∀ k ∈ (Finset.univ : Finset α),
      finiteComplexInner (e j) (H *ᵥ (finiteComplexInner (e k) ψ • e k))
        = if k = j then ((lam j : ℝ) : ℂ) * finiteComplexInner (e j) ψ else 0 := by
    intro k _
    rw [Matrix.mulVec_smul, heb.eigen k, smul_smul, finiteComplexInner_smul_right, heb.orth j k]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_pos rfl, mul_one]
      ring
    · rw [if_neg hk, if_neg (fun hcon => hk hcon.symm), mul_zero]
  rw [finiteComplexInner_sum_right, Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' Finset.univ j (fun _ => ((lam j : ℝ) : ℂ) * finiteComplexInner (e j) ψ),
    if_pos (Finset.mem_univ j)]

theorem finiteComplexInner_pow_mulVec {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (j : α) (ψ : α → ℂ) (n : ℕ) :
    finiteComplexInner (e j) (H ^ n *ᵥ ψ)
      = ((lam j : ℝ) : ℂ) ^ n * finiteComplexInner (e j) ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, finiteComplexInner_mulVec heb j (H ^ n *ᵥ ψ), ih]
      ring

/-- **A cyclic vector has a nonzero component along every eigenvector.** -/
theorem finiteComplexInner_ne_zero_of_linearIndependent {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) {Ω : α → ℂ}
    (hind : LinearIndependent ℂ (fun k : Fin (Fintype.card α) => H ^ (k : ℕ) *ᵥ Ω)) (j : α) :
    finiteComplexInner (e j) Ω ≠ 0 := by
  classical
  intro hzero
  haveI : Nonempty α := ⟨j⟩
  have hcard : Fintype.card (Fin (Fintype.card α)) = Module.finrank ℂ (α → ℂ) := by simp
  have hspan : Submodule.span ℂ
      (Set.range fun k : Fin (Fintype.card α) => H ^ (k : ℕ) *ᵥ Ω) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank hcard
  have hker : ∀ v ∈ Submodule.span ℂ
      (Set.range fun k : Fin (Fintype.card α) => H ^ (k : ℕ) *ᵥ Ω),
      finiteComplexInner (e j) v = 0 := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, rfl⟩
      rw [finiteComplexInner_pow_mulVec heb j Ω, hzero, mul_zero]
    · rw [finiteComplexInner]
      simp
    · intro x y _ _ hx hy
      rw [finiteComplexInner_add_right, hx, hy, add_zero]
    · intro a x _ hx
      rw [finiteComplexInner_smul_right, hx, mul_zero]
  have hone : finiteComplexInner (e j) (e j) = 0 := by
    refine hker _ ?_
    rw [hspan]
    exact Submodule.mem_top
  rw [heb.orth j j, if_pos rfl] at hone
  exact one_ne_zero hone

end

end AlgebraicOrbit

end GaloisForLFunctions.HTGeometry
