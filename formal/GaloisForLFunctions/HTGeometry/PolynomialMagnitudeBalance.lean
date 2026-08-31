import Mathlib

/-!
# Magnitudes of polynomial values, and the balancing principle for a vanishing sum

Two elementary estimates that together read off the size of a root of an algebraic equation whose
coefficients are polynomials in a large parameter.

The first pair bounds `‖p(y)‖` above and below by `‖y‖^{deg p}` once `‖y‖` is large.

The second is the balancing principle: in a finite family of complex numbers summing to zero, the
largest member is within a factor of the cardinality of some *other* member.  Applied to the terms
`a_k(y)·w^k` of a vanishing polynomial equation, it says that the largest term is matched by a
second one — which pins `‖w‖` to a power of `‖y‖` read off from the two degrees involved.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Upper magnitude bound.**  Beyond the unit circle a polynomial is at most the sum of the norms
of its coefficients times the leading power. -/
theorem norm_eval_le_mul_pow (p : ℂ[X]) {y : ℂ} (hy : 1 ≤ ‖y‖) :
    ‖p.eval y‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖y‖ ^ p.natDegree := by
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine pow_le_pow_right₀ hy ?_
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

/-- **Lower magnitude bound.**  Beyond a radius depending on the coefficients a nonzero polynomial
is at least half its leading term. -/
theorem exists_le_norm_eval (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ y : ℂ, R ≤ ‖y‖ →
      ‖p.leadingCoeff‖ / 2 * ‖y‖ ^ p.natDegree ≤ ‖p.eval y‖ := by
  classical
  set d := p.natDegree with hd
  set B : ℝ := ∑ i ∈ Finset.range d, ‖p.coeff i‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hlc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)
  refine ⟨max 1 (2 * B / ‖p.leadingCoeff‖ + 1), le_max_left _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ ‖y‖ := le_trans (le_max_left _ _) hy
  have hy2 : 2 * B / ‖p.leadingCoeff‖ + 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
  have hypos : (0 : ℝ) < ‖y‖ := by linarith
  have hyd : (0 : ℝ) < ‖y‖ ^ d := by positivity
  set S : ℂ := ∑ i ∈ Finset.range d, p.coeff i * y ^ i with hS
  have hsplit : p.eval y = S + p.leadingCoeff * y ^ d := by
    rw [hS, eval_eq_sum_range, ← hd, Finset.sum_range_succ, Polynomial.leadingCoeff]
  have htail : ‖S‖ * ‖y‖ ≤ B * ‖y‖ ^ d := by
    rw [hS, hB, Finset.sum_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (norm_sum_le _ _) hypos.le) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hid : i + 1 ≤ d := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖y‖ ^ i * ‖y‖ = ‖y‖ ^ (i + 1) := (pow_succ _ _).symm
      _ ≤ ‖y‖ ^ d := pow_le_pow_right₀ hy1 hid
  have hBy : 2 * B ≤ ‖p.leadingCoeff‖ * ‖y‖ := by
    have := (div_le_iff₀ hlc).mp (by linarith : 2 * B / ‖p.leadingCoeff‖ ≤ ‖y‖)
    linarith
  have hhalf : ‖S‖ ≤ ‖p.leadingCoeff‖ / 2 * ‖y‖ ^ d := by
    refine le_of_mul_le_mul_right ?_ hypos
    nlinarith [htail, hBy, hyd, norm_nonneg S]
  have hrev : ‖p.leadingCoeff * y ^ d‖ - ‖S‖ ≤ ‖p.eval y‖ := by
    have h1 : ‖p.leadingCoeff * y ^ d‖ ≤ ‖p.eval y‖ + ‖S‖ := by
      calc ‖p.leadingCoeff * y ^ d‖ = ‖p.eval y - S‖ := by rw [hsplit]; ring_nf
        _ ≤ ‖p.eval y‖ + ‖S‖ := norm_sub_le _ _
    linarith
  rw [norm_mul, norm_pow] at hrev
  linarith

/-- **The balancing principle.**  In a finite family summing to zero, a largest member is within a
factor of the cardinality of some other member. -/
theorem exists_ne_norm_le_card_mul {ι : Type*} [DecidableEq ι] {s : Finset ι} {b : ι → ℂ}
    (hsum : ∑ i ∈ s, b i = 0) {k : ι} (hk : k ∈ s) (hne : b k ≠ 0) :
    ∃ j ∈ s, j ≠ k ∧ ‖b k‖ ≤ (s.card : ℝ) * ‖b j‖ := by
  classical
  have h0 : b k + ∑ i ∈ s.erase k, b i = 0 := by
    rw [Finset.add_sum_erase s b hk, hsum]
  have herase : b k = -∑ i ∈ s.erase k, b i := add_eq_zero_iff_eq_neg.mp h0
  have hle : ‖b k‖ ≤ ∑ i ∈ s.erase k, ‖b i‖ := by
    rw [herase, norm_neg]
    exact norm_sum_le _ _
  have hnonempty : (s.erase k).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (s.erase k) with hempty | hne'
    · rw [hempty] at hle
      simp only [Finset.sum_empty] at hle
      exact absurd (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))) hne
    · exact hne'
  obtain ⟨j, hjmem, hjmax⟩ := (s.erase k).exists_max_image (fun i => ‖b i‖) hnonempty
  refine ⟨j, Finset.mem_of_mem_erase hjmem, Finset.ne_of_mem_erase hjmem, ?_⟩
  have hsum_le : ∑ i ∈ s.erase k, ‖b i‖ ≤ ((s.erase k).card : ℝ) * ‖b j‖ := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun i hi => hjmax i hi
  have hcard : ((s.erase k).card : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hbj : 0 ≤ ‖b j‖ := norm_nonneg _
  nlinarith [hle, hsum_le, hcard, hbj]

end GaloisForLFunctions.HTGeometry
