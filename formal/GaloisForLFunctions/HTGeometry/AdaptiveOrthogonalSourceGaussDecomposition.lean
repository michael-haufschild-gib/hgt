import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature

/-!
# Adaptive orthogonal source as visible Gauss bulk plus one Christoffel edge

The literal adaptive source has degree exactly one past Gaussian exactness.  Its complete invisible
part is the next monic norm, with multiplicity `n+1`; everything else is a strictly positive
source-selected Gaussian aggregate.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- Current source-selected finite observation.  Both nodes and weights come from the same admitted
moment form as the adaptive polynomial. -/
noncomputable def adaptiveOrthoGaussAggregate (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ gaussNodes s n,
    christoffel s n x * (adaptiveOrthoSourcePolynomial s n).eval x

theorem natDegree_adaptiveOrthoCompanion_le (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoCompanion s n).natDegree ≤ n + 2 := by
  unfold adaptiveOrthoCompanion
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_X_pow, natDegree_monicOrtho]
    omega
  · refine natDegree_mul_le.trans ?_
    have hd := natDegree_derivative_le (monicOrtho s n)
    rw [natDegree_monicOrtho] at hd
    rw [natDegree_X_pow]
    omega

/-- Top source coefficient.  It is the shifted-Euler multiplicity `n+1`, independent of all lower
Jacobi data. -/
theorem coeff_adaptiveOrthoSourcePolynomial_top (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoSourcePolynomial s n).coeff (2 * n + 2) = n + 1 := by
  rw [adaptiveOrthoSourcePolynomial_eq_mul_companion]
  have hPn : (monicOrtho s n).natDegree ≤ n := by
    rw [natDegree_monicOrtho]
  have hC := natDegree_adaptiveOrthoCompanion_le s hn
  rw [show 2 * n + 2 = n + (n + 2) by omega,
    coeff_mul_add_eq_of_natDegree_le hPn hC,
    coeff_monicOrtho_self, adaptiveOrthoCompanion_coeff_add_two]
  norm_num

theorem degree_adaptiveOrthoSourcePolynomial_lt (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoSourcePolynomial s n).degree <
      ((2 * n + 3 : ℕ) : WithBot ℕ) := by
  have hnat : (adaptiveOrthoSourcePolynomial s n).natDegree ≤ 2 * n + 2 := by
    rw [adaptiveOrthoSourcePolynomial_eq_mul_companion]
    refine natDegree_mul_le.trans ?_
    rw [natDegree_monicOrtho]
    have hC := natDegree_adaptiveOrthoCompanion_le s hn
    omega
  by_cases hzero : adaptiveOrthoSourcePolynomial s n = 0
  · rw [hzero, degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hzero]
    exact_mod_cast (lt_of_le_of_lt hnat (by omega : 2 * n + 2 < 2 * n + 3))

/-- Exact one-coordinate observer loss of the adaptive source. -/
theorem momentFunctional_adaptiveOrthoSourcePolynomial_sub_gaussAggregate_eq_nextNorm
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentFunctional s (adaptiveOrthoSourcePolynomial s n) -
        adaptiveOrthoGaussAggregate s n =
      (n + 1 : ℝ) * monicOrthoNormSq s (n + 1) := by
  rw [adaptiveOrthoGaussAggregate]
  have hdefect := momentFunctional_sub_gaussSum_eq_topCoeff_mul_nextNorm_below
    h n (by omega) (adaptiveOrthoSourcePolynomial s n)
      (degree_adaptiveOrthoSourcePolynomial_lt s hn)
  rw [coeff_adaptiveOrthoSourcePolynomial_top s hn] at hdefect
  simpa only [Nat.cast_add, Nat.cast_one, monicOrthoNormSq] using hdefect

theorem monicOrthoNormSq_mul_nextBeta {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 < N) :
    monicOrthoNormSq s n * monicOrthoBeta s (n + 1) =
      monicOrthoNormSq s (n + 1) := by
  have hnpos : 0 < monicOrthoNormSq s n :=
    monicOrtho_inner_self_pos_below h (by omega)
  unfold monicOrthoBeta monicOrthoNormSq
  exact mul_div_cancel₀ _ (ne_of_gt hnpos)

/-- Gaussian-visible source is exactly Jacobi energy with the sole next-edge defect removed. -/
theorem adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    adaptiveOrthoGaussAggregate s n =
      monicOrthoNormSq s n *
        (adaptiveOrthoJacobiEnergy s n -
          (n + 1 : ℝ) * monicOrthoBeta s (n + 1)) := by
  have hsource := momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
    h hn hnN
  have hdefect :=
    momentFunctional_adaptiveOrthoSourcePolynomial_sub_gaussAggregate_eq_nextNorm
      h hn hnN
  have hbeta := monicOrthoNormSq_mul_nextBeta h (by omega : n + 1 < N)
  nlinarith

/-- The visible Jacobi energy is strictly positive; pointwise source values may have either sign,
but their current positive Christoffel aggregate cannot vanish. -/
theorem adaptiveOrthoJacobiEnergy_sub_succ_mul_nextBeta_pos_below
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < adaptiveOrthoJacobiEnergy s n -
      (n + 1 : ℝ) * monicOrthoBeta s (n + 1) := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) * monicOrthoAlpha s n ^ (2 : ℕ) := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hbeta : 0 < monicOrthoBeta s n :=
    monicOrthoBeta_pos_below h hn (by omega)
  unfold adaptiveOrthoJacobiEnergy
  nlinarith

theorem adaptiveOrthoGaussAggregate_pos
    {s : ℕ → ℝ} {N n : ℕ} (h : PositiveMomentFormBelow s N)
    (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < adaptiveOrthoGaussAggregate s n := by
  rw [adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy h hn hnN]
  exact mul_pos
    (monicOrtho_inner_self_pos_below h (by omega))
    (adaptiveOrthoJacobiEnergy_sub_succ_mul_nextBeta_pos_below h hn hnN)

end HTGeometry
