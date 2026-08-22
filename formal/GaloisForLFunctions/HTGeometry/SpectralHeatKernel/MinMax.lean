import GaloisForLFunctions.HTGeometry.GreedyCourantFischer
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The min–max principle for a spectral quadratic form

Section 6.2 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), bounds the small eigenvalues from above by exhibiting a
`k`-dimensional space of trial functions with small Dirichlet energy.  The principle it uses is the
easy half of Courant–Fischer in infinite dimensions:

> if the quadratic form of a nonnegative self-adjoint operator with eigenbasis `(φₙ)` and increasing
> eigenvalues `(λₙ)` is at most `M‖v‖²` on some subspace of dimension `> k`, then `λ_k ≤ M`.

The proof is the dimension count: such a subspace contains a nonzero vector orthogonal to the first
`k` eigenvectors, and on that vector the form is at least `λ_k ‖v‖²`.

Mathlib has the finite-dimensional Courant–Fischer for symmetric endomorphisms but nothing for a
spectral datum on an infinite-dimensional space; that is what this file supplies.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Parseval.**  The squared coefficients of a Hilbert basis sum to the squared norm. -/
theorem tsum_norm_inner_sq (b : HilbertBasis ℕ ℂ E) (v : E) :
    ∑' n, ‖(inner ℂ (b n) v : ℂ)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hkey := HilbertBasis.tsum_inner_mul_inner b v v
  have hterm : ∀ n : ℕ, (inner ℂ v (b n) : ℂ) * (inner ℂ (b n) v : ℂ)
      = ((‖(inner ℂ (b n) v : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    have h1 : (inner ℂ v (b n) : ℂ) = (starRingEnd ℂ) (inner ℂ (b n) v : ℂ) :=
      (inner_conj_symm (𝕜 := ℂ) v (b n)).symm
    rw [h1, mul_comm ((starRingEnd ℂ) (inner ℂ (b n) v : ℂ)) (inner ℂ (b n) v : ℂ),
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hterm] at hkey
  rw [← Complex.ofReal_tsum] at hkey
  have hre := congrArg Complex.re hkey
  simpa [Complex.ofReal_re, inner_self_eq_norm_sq, ← Complex.ofReal_pow] using hre

/-- The coefficient family of a Hilbert basis is square-summable. -/
theorem summable_norm_inner_sq (b : HilbertBasis ℕ ℂ E) (v : E) :
    Summable fun n => ‖(inner ℂ (b n) v : ℂ)‖ ^ 2 := by
  by_cases hv : v = 0
  · subst hv
    simp
  · by_contra hns
    have h0 := tsum_eq_zero_of_not_summable hns
    have hpar := tsum_norm_inner_sq b v
    rw [h0] at hpar
    exact hv (norm_eq_zero.mp (by nlinarith [norm_nonneg v, hpar]))

/-- The quadratic form attached to a spectral datum. -/
noncomputable def spectralQuadratic (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) (v : E) : ℝ :=
  ∑' n, lam n * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2

/-- **The min–max upper bound.**

A trial subspace of dimension exceeding `k` on which the spectral quadratic form is at most
`M‖v‖²` forces `λ_k ≤ M`. -/
theorem spectral_eigenvalue_le_of_trial
    (b : HilbertBasis ℕ ℂ E) {lam : ℕ → ℝ} (hmono : Monotone lam)
    {k : ℕ} {V : Submodule ℂ E} (hV : k < Module.finrank ℂ V) {M : ℝ}
    (hsum : ∀ v ∈ V, Summable fun n => lam n * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2)
    (hQ : ∀ v ∈ V, spectralQuadratic b lam v ≤ M * ‖v‖ ^ 2) :
    lam k ≤ M := by
  obtain ⟨v, hvV, hv0, hvorth⟩ :=
    ContinuousLinearMap.exists_mem_ne_zero_orthogonal_of_finrank_lt V (fun m => b m) k hV
  have hpar := tsum_norm_inner_sq b v
  have hsq : Summable fun n => ‖(inner ℂ (b n) v : ℂ)‖ ^ 2 := summable_norm_inner_sq b v
  have hlow : ∀ n : ℕ, lam k * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2
      ≤ lam n * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2 := by
    intro n
    rcases lt_or_ge n k with hn | hn
    · have hzero : (inner ℂ (b n) v : ℂ) = 0 := hvorth n hn
      rw [hzero]
      simp
    · exact mul_le_mul_of_nonneg_right (hmono hn) (by positivity)
  have hge : lam k * ‖v‖ ^ 2 ≤ spectralQuadratic b lam v := by
    rw [spectralQuadratic, ← hpar, ← tsum_mul_left]
    exact (hsq.mul_left (lam k)).tsum_le_tsum hlow (hsum v hvV)
  have hle := hQ v hvV
  have hvpos : (0 : ℝ) < ‖v‖ ^ 2 := by
    have : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
    positivity
  nlinarith [hge, hle, hvpos]

end GaloisForLFunctions.HTGeometry
