import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian determinant approximation implies RH

This module closes the finite spectral part of the Route-B implication chain.  A Hermitian matrix
has a real-rooted characteristic polynomial. Multiplication by a nowhere-zero entire normalization
does not change that zero locus. If such normalized characteristic polynomials converge locally
uniformly to `XiC`, the closed zero-locus transfer theorem gives RH.
-/

open Complex Filter Topology Polynomial

namespace RHTower

/-- Every zero of the characteristic polynomial of a finite Hermitian complex matrix is real. -/
theorem hermitian_charpoly_zero_im_eq_zero
    {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : A.charpoly.eval z = 0) : z.im = 0 := by
  have hmem : z ∈ A.charpoly.roots := by
    rw [Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero]
    exact hz
  rw [hA.roots_charpoly_eq_eigenvalues] at hmem
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, Function.comp_apply,
    true_and] at hmem
  obtain ⟨i, hi⟩ := hmem
  rw [← hi]
  exact Complex.ofReal_im _

/-- A characteristic polynomial multiplied by a possibly aperture-dependent normalization. -/
noncomputable def normalizedHermitianCharpoly
    (d : ℕ → ℕ) (A : ∀ n, Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (u : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  u n z * (A n).charpoly.eval z

/-- **Hermitian determinant chain to RH.** If finite Hermitian characteristic polynomials, after
multiplication by nowhere-zero entire normalizations, converge locally uniformly to `XiC`, then
the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly
    {d : ℕ → ℕ} {A : ∀ n, Matrix (Fin (d n)) (Fin (d n)) ℂ}
    {u : ℕ → ℂ → ℂ}
    (hA : ∀ n, (A n).IsHermitian)
    (hu : ∀ n, Differentiable ℂ (u n))
    (hu0 : ∀ n z, u n z ≠ 0)
    (hconv : TendstoLocallyUniformly (normalizedHermitianCharpoly d A u) XiC atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall fun n =>
      (hu n).mul (A n).charpoly.differentiable
  · apply Filter.Eventually.of_forall
    intro n z hz
    have hchar : (A n).charpoly.eval z = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left (hu0 n z)
    exact hermitian_charpoly_zero_im_eq_zero (hA n) hchar

end RHTower
