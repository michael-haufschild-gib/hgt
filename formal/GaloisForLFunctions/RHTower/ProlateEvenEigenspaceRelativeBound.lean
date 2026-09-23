import GaloisForLFunctions.RHTower.ProlateEvenEigenspaceQuadratic

/-!
# The prolate form on the complement of the high modes

On the even part of a live band eigenspace the prolate action is symmetric on a finite-dimensional
space, so its quadratic form is the eigenvalue-weighted sum of squared coordinates in an
eigenbasis.  A vector orthogonal to every eigenvector with eigenvalue above `−K` therefore has all
its mass on coordinates with eigenvalue at most `−K`, and the form is bounded by `−K` times the
squared norm.

This is the relative form of the eigenvalue detection theorem: the absolute version extracts a high
mode from a large form value, this version bounds the form once the high modes have been removed.
-/

noncomputable section

open Filter MeasureTheory Set

namespace RHTower

/-- **Relative form bound.**  A vector of the even band eigenspace orthogonal to every prolate
eigenvector with eigenvalue above `−K` has prolate form at most `−K` times its squared norm. -/
theorem prolate_form_le_of_orthogonal_high
    {c lam K : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {u : evenBandEigenspace c lam}
    (horth : ∀ (v : evenBandEigenspace c lam) (eta : ℝ), -K < eta →
      prolateOnEvenEigenspace hc hlam v = eta • v → (inner ℝ v u : ℝ) = 0) :
    (inner ℝ (prolateOnEvenEigenspace hc hlam u) u : ℝ) ≤ -K * ‖u‖ ^ (2 : ℕ) := by
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    finiteDimensional_evenBandEigenspace hlam
  set T := prolateOnEvenEigenspace hc hlam with hT
  have hsym : T.IsSymmetric := isSymmetric_prolateOnEvenEigenspace hc hlam
  set m : ℕ := Module.finrank ℝ (evenBandEigenspace c lam) with hm
  have hn : Module.finrank ℝ (evenBandEigenspace c lam) = m := rfl
  set b := hsym.eigenvectorBasis hn with hb
  set ev := hsym.eigenvalues hn with hev
  have hquad : (inner ℝ (T u) u : ℝ) = ∑ j : Fin m, ev j * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) := by
    have h1 := b.sum_inner_mul_inner (T u) u
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : (inner ℝ (T u) (b i) : ℝ) = ev i * (inner ℝ (b i) u : ℝ) := by
      rw [hsym u (b i), hsym.apply_eigenvectorBasis hn i, real_inner_smul_right,
        real_inner_comm]
      norm_cast
    rw [h2]
    ring
  have hnorm : ‖u‖ ^ (2 : ℕ) = ∑ j : Fin m, (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) := by
    have h := b.sum_sq_norm_inner_right u
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hle : ∑ j : Fin m, ev j * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ)
      ≤ ∑ j : Fin m, (-K) * (inner ℝ (b j) u : ℝ) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : -K < ev i
    · have heig : T (b i) = ev i • b i := by
        exact_mod_cast hsym.apply_eigenvectorBasis hn i
      have hz : (inner ℝ (b i) u : ℝ) = 0 := horth (b i) (ev i) hi heig
      rw [hz]
      simp
    · exact mul_le_mul_of_nonneg_right (not_lt.1 hi) (sq_nonneg _)
  rw [← Finset.mul_sum, ← hnorm] at hle
  linarith [hquad, hle]

end RHTower
