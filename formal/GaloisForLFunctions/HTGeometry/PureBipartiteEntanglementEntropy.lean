import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Pure bipartite entanglement entropy

This module formalizes the exact statement following Eq. (12) of
Formicola--Di Bello--de Candia--De Filippis--Perroni,
*Discrete time crystals in disordered anisotropic Heisenberg chains*, arXiv:2609.04037:
the two reduced density matrices of a finite globally pure bipartite state have equal von Neumann
entropy.

The proof works for unequal subsystem dimensions.  The rectangular characteristic-polynomial
identity pads the spectra of `Ψ Ψ†` and `Ψ† Ψ` with zeros.  All nonzero eigenvalues therefore agree,
and the entropy contribution `-x log x` vanishes at zero.
-/

open scoped BigOperators Matrix
open Matrix Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Spectral von Neumann entropy of a finite Hermitian matrix. -/
def finiteMatrixVonNeumannEntropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, -(hρ.eigenvalues i * Real.log (hρ.eigenvalues i))

/-- Entropy of the uniform spectrum on a `d`-dimensional Hilbert space. -/
def finiteUniformSpectralEntropy (d : ℕ) : ℝ :=
  -∑ _i : Fin d, (d : ℝ)⁻¹ * Real.log (d : ℝ)⁻¹

/-- The paper's horizontal entropy reference for `k` qubits is exactly `k log 2`. -/
theorem finiteUniformSpectralEntropy_qubits (k : ℕ) :
    finiteUniformSpectralEntropy (2 ^ k) = (k : ℝ) * Real.log 2 := by
  rw [finiteUniformSpectralEntropy]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [Real.log_inv, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hne : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp

/-- Entropy contribution of one complex root of a Hermitian characteristic polynomial. -/
private def spectralEntropyRootContribution (z : ℂ) : ℝ :=
  -(z.re * Real.log z.re)

/-- Zero roots contribute no von Neumann entropy. -/
private theorem sum_spectralEntropyRootContribution_nsmul_zero (k : ℕ) :
    ((k • ({0} : Multiset ℂ)).map spectralEntropyRootContribution).sum = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul, Multiset.map_add, Multiset.sum_add, ih]
      simp [spectralEntropyRootContribution]

/-- Rectangular Gram matrices `Ψ Ψ†` and `Ψ† Ψ` have equal spectral entropy. -/
theorem finiteMatrixVonNeumannEntropy_mul_conjTranspose_eq_conjTranspose_mul
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (Ψ : Matrix ι κ ℂ) :
    finiteMatrixVonNeumannEntropy (Ψ * Ψᴴ)
        (Matrix.isHermitian_mul_conjTranspose_self Ψ) =
      finiteMatrixVonNeumannEntropy (Ψᴴ * Ψ)
        (Matrix.isHermitian_conjTranspose_mul_self Ψ) := by
  let hLeft := Matrix.isHermitian_mul_conjTranspose_self Ψ
  let hRight := Matrix.isHermitian_conjTranspose_mul_self Ψ
  have hprodLeft :
      Polynomial.X ^ Fintype.card κ * (Ψ * Ψᴴ).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero
  have hprodRight :
      Polynomial.X ^ Fintype.card ι * (Ψᴴ * Ψ).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero
  have hroots := congrArg Polynomial.roots
    (Matrix.charpoly_mul_comm' Ψ Ψᴴ)
  rw [Polynomial.roots_mul hprodLeft, Polynomial.roots_mul hprodRight,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow,
    hLeft.roots_charpoly_eq_eigenvalues,
    hRight.roots_charpoly_eq_eigenvalues] at hroots
  have hsum := congrArg
    (fun s : Multiset ℂ => (s.map spectralEntropyRootContribution).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [sum_spectralEntropyRootContribution_nsmul_zero,
    sum_spectralEntropyRootContribution_nsmul_zero,
    zero_add, zero_add] at hsum
  simpa [finiteMatrixVonNeumannEntropy, spectralEntropyRootContribution,
    Function.comp_def] using hsum

/-- Coefficient matrix of a finite bipartite pure state. -/
def bipartitePureStateMatrix
    {ι κ : Type*} (ψ : ι × κ → ℂ) : Matrix ι κ ℂ :=
  fun i k => ψ (i, k)

/-- Reduced density matrix on the left subsystem. -/
def pureStateReducedLeft
    {ι κ : Type*} [Fintype κ]
    (ψ : ι × κ → ℂ) : Matrix ι ι ℂ :=
  bipartitePureStateMatrix ψ * (bipartitePureStateMatrix ψ)ᴴ

/-- Reduced density matrix on the right subsystem. -/
def pureStateReducedRight
    {ι κ : Type*} [Fintype ι]
    (ψ : ι × κ → ℂ) : Matrix κ κ ℂ :=
  (bipartitePureStateMatrix ψ)ᴴ * bipartitePureStateMatrix ψ

/-- Left reduction is the partial contraction over right indices. -/
theorem pureStateReducedLeft_apply
    {ι κ : Type*} [Fintype κ]
    (ψ : ι × κ → ℂ) (i j : ι) :
    pureStateReducedLeft ψ i j = ∑ k, ψ (i, k) * star (ψ (j, k)) := by
  simp [pureStateReducedLeft, bipartitePureStateMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Right reduction is the partial contraction over left indices. -/
theorem pureStateReducedRight_apply
    {ι κ : Type*} [Fintype ι]
    (ψ : ι × κ → ℂ) (k l : κ) :
    pureStateReducedRight ψ k l = ∑ i, star (ψ (i, k)) * ψ (i, l) := by
  simp [pureStateReducedRight, bipartitePureStateMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Left reduced density matrices of pure states are Hermitian. -/
theorem pureStateReducedLeft_isHermitian
    {ι κ : Type*} [Fintype κ] (ψ : ι × κ → ℂ) :
    (pureStateReducedLeft ψ).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self _

/-- Right reduced density matrices of pure states are Hermitian. -/
theorem pureStateReducedRight_isHermitian
    {ι κ : Type*} [Fintype ι] (ψ : ι × κ → ℂ) :
    (pureStateReducedRight ψ).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_self _

/-- Both reductions of any finite globally pure bipartite state have equal entropy. -/
theorem pureStateReduced_entropies_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (ψ : ι × κ → ℂ) :
    finiteMatrixVonNeumannEntropy (pureStateReducedLeft ψ)
        (pureStateReducedLeft_isHermitian ψ) =
      finiteMatrixVonNeumannEntropy (pureStateReducedRight ψ)
        (pureStateReducedRight_isHermitian ψ) := by
  exact finiteMatrixVonNeumannEntropy_mul_conjTranspose_eq_conjTranspose_mul
    (bipartitePureStateMatrix ψ)

end

end GaloisForLFunctions.HTGeometry
