import GaloisForLFunctions.HTGeometry.PureBipartiteEntanglementEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Spectral entropy for finite fermion correlations

The entropy functional in equation (14) of arXiv:2611.13085 is the sum of
binary entropies of correlation eigenvalues. Expressing it through the roots
of the characteristic polynomial makes its invariance under changes of basis
and the rectangular Gram identity exact, with zero padding contributing nothing.
For Hermitian contractions this is the usual free-fermion entropy; the definition
also extends algebraically to arbitrary square matrices using real parts of roots.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix Polynomial
namespace GaloisForLFunctions.HilbertMetric

/-- Free-fermion spectral entropy, extended by real parts to arbitrary spectra. -/
def fermionSpectralEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  (A.charpoly.roots.map (fun z => Real.binEntropy z.re)).sum

/-- Each diagonal occupation contributes its binary entropy. -/
theorem fermionSpectralEntropy_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) :
    fermionSpectralEntropy (Matrix.diagonal (fun i => (p i : ℂ))) =
      ∑ i, Real.binEntropy (p i) := by
  unfold fermionSpectralEntropy
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp only [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero, implies_true]

/-- Empty and full occupations carry zero fermion entropy. -/
theorem fermionSpectralEntropy_projection_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (occupied : Finset ι) :
    fermionSpectralEntropy (Matrix.diagonal (fun i => if i ∈ occupied then (1 : ℂ) else 0)) = 0 := by
  have h := fermionSpectralEntropy_diagonal (fun i => if i ∈ occupied then (1 : ℝ) else 0)
  simpa only [Complex.ofReal_ite, Complex.ofReal_one, Complex.ofReal_zero,
    apply_ite Real.binEntropy, Real.binEntropy_one, Real.binEntropy_zero,
    ite_self, Finset.sum_const_zero] using h

/-- Multiplication in either order gives the same spectral entropy. -/
theorem fermionSpectralEntropy_mul_comm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    fermionSpectralEntropy (A * B) = fermionSpectralEntropy (B * A) := by
  unfold fermionSpectralEntropy
  rw [Matrix.charpoly_mul_comm]

private theorem binEntropy_zero_padding (k : ℕ) :
    ((k • ({0} : Multiset ℂ)).map (fun z => Real.binEntropy z.re)).sum = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, Multiset.map_add, Multiset.sum_add, ih]
    simp

/-- Rectangular Gram matrices have equal fermion entropy, even at unequal dimensions. -/
theorem fermionSpectralEntropy_gram
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    fermionSpectralEntropy (A * Aᴴ) = fermionSpectralEntropy (Aᴴ * A) := by
  have hl : Polynomial.X ^ Fintype.card κ * (A * Aᴴ).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have hr : Polynomial.X ^ Fintype.card ι * (Aᴴ * A).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have h := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A Aᴴ)
  rw [Polynomial.roots_mul hl, Polynomial.roots_mul hr,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at h
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map (fun z => Real.binEntropy z.re)).sum) h
  simpa only [Multiset.map_add, Multiset.sum_add, binEntropy_zero_padding, zero_add,
    fermionSpectralEntropy] using hs

/-- The corpus's two pure-state reductions also have equal fermion spectral entropy. -/
theorem pureStateReduced_fermionEntropies_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ψ : ι × κ → ℂ) :
    fermionSpectralEntropy (HTGeometry.pureStateReducedLeft ψ) =
      fermionSpectralEntropy (HTGeometry.pureStateReducedRight ψ) :=
  fermionSpectralEntropy_gram (HTGeometry.bipartitePureStateMatrix ψ)

end GaloisForLFunctions.HilbertMetric
