import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Fixed-central-zero obstruction to full-characteristic CCM limits

Any family of holomorphic approximants that vanishes at the centered origin can only converge
locally uniformly to a function that also vanishes there.  Since `XiC 0 ≠ 0`, no characteristic
polynomial family retaining a fixed zero eigenvector can converge to `XiC`, regardless of the
entire multipliers used for normalization.

This is the exact obstruction to using the *full* characteristic polynomial of a canonical CCM
boundary completion: the pinned radical vector is a zero eigenvector.  A viable determinant route
must first pass to a reduced determinant that cancels every forced central zero.
-/

noncomputable section

namespace RHTower

open Filter Matrix Topology

/-- A fixed central zero is closed under locally uniform convergence, so such a family cannot
converge to centered Xi, which is nonzero at the origin. -/
theorem not_tendstoLocallyUniformly_XiC_of_central_zero
    {f : ℕ → ℂ → ℂ} (hzero : ∀ k, f k 0 = 0) :
    ¬ TendstoLocallyUniformly f XiC atTop := by
  intro hconv
  have hvalue : Tendsto (fun k => f k 0) atTop (nhds (XiC 0)) :=
    hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ 0)
  have hzeroLimit : Tendsto (fun k => f k 0) atTop (nhds 0) := by
    simpa only [hzero] using tendsto_const_nhds
  exact XiC_zero_ne (tendsto_nhds_unique hvalue hzeroLimit)

/-- A square complex matrix with a specified nonzero zero eigenvector has characteristic
polynomial zero at the centered origin. -/
theorem charpoly_eval_zero_of_nontrivial_kernel
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : n → ℂ) (hc : c ≠ 0) (hAc : A *ᵥ c = 0) :
    A.charpoly.eval 0 = 0 := by
  have hdet : A.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hAc⟩
  rw [Matrix.eval_charpoly]
  have hscalar : Matrix.scalar n (0 : ℂ) = 0 := by
    ext i j
    simp [Matrix.scalar]
  rw [hscalar, zero_sub, Matrix.det_neg, hdet, mul_zero]

/-- Basis-free form of the fixed-zero law for an endomorphism of a finite-dimensional complex
space. -/
theorem linearMap_charpoly_eval_zero_of_nontrivial_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0) (hAv : A v = 0) :
    A.charpoly.eval 0 = 0 := by
  have hker : LinearMap.ker A ≠ ⊥ := by
    intro hbot
    have hvker : v ∈ LinearMap.ker A := LinearMap.mem_ker.mpr hAv
    rw [hbot] at hvker
    exact hv (by simpa using hvker)
  have hdet : A.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
  rw [LinearMap.eval_charpoly]
  have hzero : algebraMap ℂ (Module.End ℂ V) 0 - A = -A := by simp
  rw [hzero]
  rw [show -A = (-1 : ℂ) • A by simp, LinearMap.det_smul, hdet, mul_zero]

/-- Multiplication by an arbitrary entire or non-entire scalar factor cannot remove the value zero
from a characteristic polynomial at the centered origin. -/
theorem normalizedCharpoly_central_zero_of_nontrivial_kernel
    {d : ℕ → ℕ}
    (A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (c : ∀ k, Fin (d k) → ℂ) (u : ℕ → ℂ → ℂ)
    (hc : ∀ k, c k ≠ 0) (hAc : ∀ k, A k *ᵥ c k = 0) (k : ℕ) :
    u k 0 * (A k).charpoly.eval 0 = 0 := by
  rw [charpoly_eval_zero_of_nontrivial_kernel (A k) (c k) (hc k) (hAc k), mul_zero]

/-- **Full-characteristic fixed-zero no-go.** No scalar normalization of matrices carrying a
specified nontrivial zero mode can converge locally uniformly to centered Xi.  No regularity or
nonvanishing assumption on the normalizers is needed. -/
theorem not_normalizedCharpoly_tendstoLocallyUniformly_XiC_of_nontrivial_kernel
    {d : ℕ → ℕ}
    (A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (c : ∀ k, Fin (d k) → ℂ) (u : ℕ → ℂ → ℂ)
    (hc : ∀ k, c k ≠ 0) (hAc : ∀ k, A k *ᵥ c k = 0) :
    ¬ TendstoLocallyUniformly
      (fun k z => u k z * (A k).charpoly.eval z)
      XiC atTop := by
  apply not_tendstoLocallyUniformly_XiC_of_central_zero
  intro k
  exact normalizedCharpoly_central_zero_of_nontrivial_kernel A c u hc hAc k

end RHTower
