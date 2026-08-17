import Mathlib

/-!
# A symmetric form below a threshold, off the high eigenvectors

For a symmetric operator on a finite-dimensional real inner-product space, a vector orthogonal to
every eigenvector with eigenvalue above `θ` has quadratic form at most `θ‖x‖²`.

Expanding in an eigenvector basis, the coefficients along the eigenvectors above the threshold
vanish, so every surviving term of `⟨Tx, x⟩ = ∑ λ_i ⟨b_i, x⟩²` has `λ_i ≤ θ`.

This is the half of the min–max principle that a counting argument needs: it converts "the modes
above the threshold are exhausted" into a bound on the quadratic form, and mathlib's spectral theory
supplies the eigenvector basis only in finite dimension, which is exactly where it is used — on a
single eigenspace of a compact operator.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The quadratic form off the high eigenvectors.**  A vector orthogonal to every eigenvector
with eigenvalue above `θ` has quadratic form at most `θ‖x‖²`. -/
theorem inner_le_of_orthogonal_to_eigenvectors_above {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (θ : ℝ) (x : E)
    (hx : ∀ (μ : ℝ) (v : E), v ≠ 0 → T v = μ • v → θ < μ → (inner ℝ x v : ℝ) = 0) :
    (inner ℝ (T x) x : ℝ) ≤ θ * ‖x‖ ^ 2 := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  have hrank : Module.finrank ℝ E = n := rfl
  set b := hT.eigenvectorBasis hrank with hb
  set lam := hT.eigenvalues hrank with hlam
  have hTb : ∀ i, T (b i) = lam i • b i := fun i => hT.apply_eigenvectorBasis hrank i
  have hbne : ∀ i, b i ≠ 0 := by
    intro i
    have := b.orthonormal.ne_zero i
    exact this
  have hcoeff : ∀ i, θ < lam i → (inner ℝ (b i) x : ℝ) = 0 := by
    intro i hi
    have h := hx (lam i) (b i) (hbne i) (hTb i) hi
    rw [real_inner_comm] at h
    exact h
  have hTx : (inner ℝ (T x) x : ℝ) = ∑ i, lam i * (inner ℝ (b i) x : ℝ) ^ 2 := by
    have hpar := b.sum_inner_mul_inner (T x) x
    rw [← hpar]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmove : (inner ℝ (T x) (b i) : ℝ) = (inner ℝ x (T (b i)) : ℝ) := hT x (b i)
    rw [hmove, hTb i, real_inner_smul_right, real_inner_comm x (b i)]
    ring
  have hnorm : ‖x‖ ^ 2 = ∑ i, (inner ℝ (b i) x : ℝ) ^ 2 := by
    have hpar := b.sum_inner_mul_inner x x
    have hself : (inner ℝ x x : ℝ) = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
    rw [hself] at hpar
    rw [← hpar]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]
    ring
  rw [hTx, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt (lam i) θ with hle | hgt
  · exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · rw [hcoeff i hgt]
    simp

end GaloisForLFunctions.HTGeometry

end
