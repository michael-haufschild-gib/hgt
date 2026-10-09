import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Angle between a vector and a span, from pairwise angles

**Frame angle bound** (`abs_inner_le_of_frame`). Let `(h_k)` satisfy a lower frame bound
`‖Σ a_k h_k‖² ≥ μ Σ a_k² ‖h_k‖²`, where `μ > 0`. Then every `d ∈ span(h)` satisfies
`|⟪d, u⟫| ≤ √(Σ_k ⟪ĥ_k, u⟫²/μ)·‖d‖`, with `ĥ_k = h_k/‖h_k‖`. The angle of `u` to a span is
thus controlled by the angles of `u` to its generators.

**Gershgorin frame bound** (`frame_lower_of_rowSum`). If the off-diagonal row sums of the
normalised Gram matrix are at most `η`, i.e. `Σ_{l≠k} |⟪ĥ_k, ĥ_l⟫| ≤ η` for each `k`, then
`‖Σ a_k h_k‖² ≥ (1 − η) Σ a_k² ‖h_k‖²`.

Combined (`abs_inner_le_of_rowSum`): for `η < 1`, the span angle is at most
`√(Σ_k ⟪ĥ_k, u⟫²/(1 − η))`.
-/

open scoped RealInnerProductSpace
open Finset

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Frame angle bound.** -/
theorem abs_inner_le_of_frame {ι : Type*} [Fintype ι] (h : ι → V) {μ : ℝ} (hμ : 0 < μ)
    (hframe : ∀ a : ι → ℝ, μ * ∑ k, a k ^ 2 * ‖h k‖ ^ 2 ≤ ‖∑ k, a k • h k‖ ^ 2) (u : V) :
    ∀ d ∈ Submodule.span ℝ (Set.range h),
      |⟪d, u⟫| ≤ Real.sqrt ((∑ k, (⟪h k, u⟫ / ‖h k‖) ^ 2) / μ) * ‖d‖ := by
  intro d hd
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hd
  set S := ∑ k, (⟪h k, u⟫ / ‖h k‖) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hinner : ⟪∑ k, a k • h k, u⟫ = ∑ k, (a k * ‖h k‖) * (⟪h k, u⟫ / ‖h k‖) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left]
    rcases eq_or_ne (h k) 0 with hk | hk
    · simp [hk]
    · have : ‖h k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
      field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => a k * ‖h k‖)
    fun k => ⟪h k, u⟫ / ‖h k‖
  have hfr : ∑ k, (a k * ‖h k‖) ^ 2 ≤ ‖∑ k, a k • h k‖ ^ 2 / μ := by
    rw [le_div_iff₀ hμ, mul_comm]
    have := hframe a
    simp only [mul_pow] at this ⊢
    exact this
  have hsq : ⟪∑ k, a k • h k, u⟫ ^ 2 ≤ S / μ * ‖∑ k, a k • h k‖ ^ 2 := by
    rw [hinner]
    calc _ ≤ (∑ k, (a k * ‖h k‖) ^ 2) * S := hcs
      _ ≤ ‖∑ k, a k • h k‖ ^ 2 / μ * S := mul_le_mul_of_nonneg_right hfr hS0
      _ = S / μ * ‖∑ k, a k • h k‖ ^ 2 := by ring
  have := Real.abs_le_sqrt hsq
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- **Gershgorin frame bound.** -/
theorem frame_lower_of_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → V)
    (hh : ∀ k, h k ≠ 0) {η : ℝ}
    (hrow : ∀ k, ∑ l ∈ Finset.univ.erase k, |⟪h k, h l⟫| / (‖h k‖ * ‖h l‖) ≤ η)
    (a : ι → ℝ) :
    (1 - η) * ∑ k, a k ^ 2 * ‖h k‖ ^ 2 ≤ ‖∑ k, a k • h k‖ ^ 2 := by
  set x : ι → ℝ := fun k => |a k| * ‖h k‖ with hx
  set c : ι → ι → ℝ := fun k l => |⟪h k, h l⟫| / (‖h k‖ * ‖h l‖) with hc
  have hc0 : ∀ k l, 0 ≤ c k l := fun k l => by
    simp only [hc]; positivity
  have hcsymm : ∀ k l, c k l = c l k := fun k l => by
    simp only [hc]; rw [real_inner_comm, mul_comm ‖h k‖]
  have hx2 : ∀ k, x k ^ 2 = a k ^ 2 * ‖h k‖ ^ 2 := fun k => by
    simp only [hx]; rw [mul_pow, sq_abs]
  -- the Gram expansion
  have hG : ‖∑ k, a k • h k‖ ^ 2 = ∑ k, ∑ l, a k * a l * ⟪h k, h l⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  -- the off-diagonal terms
  have hoff : ∀ k l, -(x k ^ 2 * c k l + x l ^ 2 * c k l) / 2 ≤ a k * a l * ⟪h k, h l⟫ := by
    intro k l
    have hkn : ‖h k‖ ≠ 0 := norm_ne_zero_iff.mpr (hh k)
    have hln : ‖h l‖ ≠ 0 := norm_ne_zero_iff.mpr (hh l)
    have habs : |⟪h k, h l⟫| = c k l * (‖h k‖ * ‖h l‖) := by
      simp only [hc]; field_simp
    have h1 : |a k * a l * ⟪h k, h l⟫| = x k * x l * c k l := by
      rw [abs_mul, abs_mul, habs]; simp only [hx]; ring
    have h2 : 2 * x k * x l ≤ x k ^ 2 + x l ^ 2 := two_mul_le_add_sq _ _
    have h3 : x k * x l * c k l ≤ (x k ^ 2 * c k l + x l ^ 2 * c k l) / 2 := by
      nlinarith [hc0 k l]
    have := neg_abs_le (a k * a l * ⟪h k, h l⟫)
    linarith
  have hrow' : ∀ k, ∑ l, (if l = k then 0 else c k l) ≤ η := fun k => by
    have := hrow k
    rw [← Finset.filter_ne', Finset.sum_filter] at this
    convert this using 2 with l
    split_ifs <;> simp_all
  have hdiag : ∀ k, ∑ l, a k * a l * ⟪h k, h l⟫ =
      x k ^ 2 + ∑ l, (if l = k then 0 else a k * a l * ⟪h k, h l⟫) := fun k => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finset.filter_ne',
      Finset.sum_filter, hx2, real_inner_self_eq_norm_sq]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp_all
  have hlow : ∀ k, x k ^ 2 - (x k ^ 2 * η + ∑ l, (if l = k then 0 else x l ^ 2 * c k l)) / 2 ≤
      ∑ l, a k * a l * ⟪h k, h l⟫ := fun k => by
    rw [hdiag k]
    have h1 : ∑ l, (if l = k then 0 else -(x k ^ 2 * c k l + x l ^ 2 * c k l) / 2) ≤
        ∑ l, (if l = k then 0 else a k * a l * ⟪h k, h l⟫) :=
      Finset.sum_le_sum fun l _ => by split_ifs; exacts [le_rfl, hoff k l]
    have h2 : ∑ l, (if l = k then 0 else -(x k ^ 2 * c k l + x l ^ 2 * c k l) / 2) =
        -(x k ^ 2 * ∑ l, (if l = k then 0 else c k l) +
          ∑ l, (if l = k then 0 else x l ^ 2 * c k l)) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, neg_div, Finset.sum_div,
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by split_ifs <;> ring
    have h3 : x k ^ 2 * ∑ l, (if l = k then 0 else c k l) ≤ x k ^ 2 * η :=
      mul_le_mul_of_nonneg_left (hrow' k) (sq_nonneg _)
    linarith
  -- the second off-diagonal sum, by symmetry
  have hswap : ∑ k, ∑ l, (if l = k then 0 else x l ^ 2 * c k l) ≤ η * ∑ k, x k ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    have : ∑ k, (if l = k then 0 else x l ^ 2 * c k l) =
        x l ^ 2 * ∑ k, (if k = l then 0 else c l k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hkl : k = l
      · subst hkl; simp
      · rw [if_neg (Ne.symm hkl), if_neg hkl, hcsymm]
    rw [this, mul_comm η]
    exact mul_le_mul_of_nonneg_left (hrow' l) (sq_nonneg _)
  have htot := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hlow k
  rw [← hG] at htot
  have e1 : ∑ k, (x k ^ 2 - (x k ^ 2 * η + ∑ l, (if l = k then 0 else x l ^ 2 * c k l)) / 2) =
      (1 - η / 2) * ∑ k, x k ^ 2 - (∑ k, ∑ l, (if l = k then 0 else x l ^ 2 * c k l)) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e1] at htot
  have e2 : ∑ k, a k ^ 2 * ‖h k‖ ^ 2 = ∑ k, x k ^ 2 := Finset.sum_congr rfl fun k _ => (hx2 k).symm
  rw [e2]
  linarith

/-- **Span angle from pairwise angles.** If the normalised Gram matrix of nonzero `h_k` has
off-diagonal row sums at most `η < 1`, then `|⟪d, u⟫| ≤ √(Σ_k ⟪ĥ_k, u⟫²/(1 − η))·‖d‖` for every
`d ∈ span(h)`. -/
theorem abs_inner_le_of_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → V)
    (hh : ∀ k, h k ≠ 0) {η : ℝ} (hη : η < 1)
    (hrow : ∀ k, ∑ l ∈ Finset.univ.erase k, |⟪h k, h l⟫| / (‖h k‖ * ‖h l‖) ≤ η) (u : V) :
    ∀ d ∈ Submodule.span ℝ (Set.range h),
      |⟪d, u⟫| ≤ Real.sqrt ((∑ k, (⟪h k, u⟫ / ‖h k‖) ^ 2) / (1 - η)) * ‖d‖ :=
  abs_inner_le_of_frame h (by linarith) (frame_lower_of_rowSum h hh hrow) u

end GaloisForLFunctions.HilbertMetric
