import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum

/-!
# Higher moments are higher inertia

The census face of the theory: the number of positive and negative squares of a Hermitian Gram
matrix is bounded below by its odd trace moments.

**Higher inertia** (`sq_trace_pow_le_posIndex_mul`, `sq_trace_pow_le_negIndex_mul`). For a Hermitian
`H` and odd `k = 2m + 1`,

* if `tr H^k ≥ 0` then `(tr H^k)² ≤ κ₊(H) · tr H^{2k}`;
* if `tr H^k ≤ 0` then `(tr H^k)² ≤ κ₋(H) · tr H^{2k}`.

The odd power keeps the sign of each eigenvalue, so `tr H^k` is at most the sum of `λ^k` over the
positive eigenvalues; Cauchy–Schwarz over those `κ₊` eigenvalues and the even moment `tr H^{2k}`
finish. At `k = 1` this is the rank–trace inequality that gives the `2/3` census; the higher odd
moments carry the `n`-level correlations of the zeros into the same inequality.

**Kernel form** (`le_negIndex_of_trace_pow_neg`). A Hermitian kernel has a negative square as soon
as one finite Gram matrix has a negative odd moment.
-/

open Complex Matrix Finset
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem re_trace_pow_eq_sum {H : Matrix n n ℂ} (hH : H.IsHermitian) (k : ℕ) :
    (H ^ k).trace.re = ∑ i, hH.eigenvalues i ^ k := by
  rw [trace_pow_eq_sum_eigenvalues_pow hH, re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Higher inertia for the positive index.** -/
theorem sq_trace_pow_le_posIndex_mul {H : Matrix n n ℂ} (hH : H.IsHermitian) (m : ℕ)
    (h : 0 ≤ (H ^ (2 * m + 1)).trace.re) :
    ((H ^ (2 * m + 1)).trace.re) ^ 2 ≤
      hermPosIndex H * (H ^ (2 * (2 * m + 1))).trace.re := by
  set k := 2 * m + 1
  have hk : Odd k := odd_two_mul_add_one m
  set ev := hH.eigenvalues
  set P := univ.filter fun i => 0 < ev i
  rw [re_trace_pow_eq_sum hH, re_trace_pow_eq_sum hH, posIndex_eq_card_pos_eigenvalues hH] at *
  -- the odd moment is at most its positive part
  have hle : ∑ i, ev i ^ k ≤ ∑ i ∈ P, ev i ^ k := by
    rw [← sum_filter_add_sum_filter_not univ (fun i => 0 < ev i)]
    have : ∑ i ∈ univ.filter (fun i => ¬ 0 < ev i), ev i ^ k ≤ 0 :=
      sum_nonpos fun i hi => hk.pow_nonpos (not_lt.mp (mem_filter.mp hi).2)
    linarith
  -- Cauchy–Schwarz over the positive eigenvalues
  have hcs : (∑ i ∈ P, ev i ^ k) ^ 2 ≤ P.card * ∑ i ∈ P, (ev i ^ k) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hev : ∑ i ∈ P, (ev i ^ k) ^ 2 ≤ ∑ i, ev i ^ (2 * k) := by
    simp_rw [← pow_mul, mul_comm k 2]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
      (even_two_mul k).pow_nonneg _
  have hP : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  calc (∑ i, ev i ^ k) ^ 2 ≤ (∑ i ∈ P, ev i ^ k) ^ 2 := pow_le_pow_left₀ h hle 2
    _ ≤ P.card * ∑ i ∈ P, (ev i ^ k) ^ 2 := hcs
    _ ≤ P.card * ∑ i, ev i ^ (2 * k) := mul_le_mul_of_nonneg_left hev hP

/-- **Higher inertia for the negative index.** -/
theorem sq_trace_pow_le_negIndex_mul {H : Matrix n n ℂ} (hH : H.IsHermitian) (m : ℕ)
    (h : (H ^ (2 * m + 1)).trace.re ≤ 0) :
    ((H ^ (2 * m + 1)).trace.re) ^ 2 ≤
      hermNegIndex H * (H ^ (2 * (2 * m + 1))).trace.re := by
  have hH' : (-H).IsHermitian := hH.neg
  have hodd : (-H) ^ (2 * m + 1) = -(H ^ (2 * m + 1)) := (odd_two_mul_add_one m).neg_pow H
  have heven : (-H) ^ (2 * (2 * m + 1)) = H ^ (2 * (2 * m + 1)) := (even_two_mul _).neg_pow H
  have := sq_trace_pow_le_posIndex_mul hH' m (by rw [hodd, trace_neg, neg_re]; linarith)
  rwa [hodd, heven, trace_neg, neg_re, neg_sq] at this

/-- **A negative odd moment of one Gram matrix gives a negative square of the kernel.** -/
theorem le_negIndex_of_trace_pow_neg {G : Type*} [Group G] {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → G) (m : ℕ)
    (h : ((gram k x) ^ (2 * m + 1)).trace.re < 0) : 1 ≤ negIndex k := by
  have hG := gram_isHermitian hk x
  have hineq := sq_trace_pow_le_negIndex_mul hG m h.le
  have hpos : 0 < ((gram k x) ^ (2 * m + 1)).trace.re ^ 2 := by nlinarith
  have hne : hermNegIndex (gram k x) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_mul] at hineq
    linarith
  exact (Nat.cast_le.mpr (Nat.one_le_iff_ne_zero.mpr hne)).trans (hermNegIndex_gram_le_negIndex k x)

end GaloisForLFunctions.HeckeKreinToeplitz
