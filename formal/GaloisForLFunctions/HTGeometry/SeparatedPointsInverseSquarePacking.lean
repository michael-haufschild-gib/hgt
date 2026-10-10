import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Inverse-square sums over separated points

**Theorem** (`exists_sum_inv_sq_le_of_separated`).  There is an absolute constant `A` with the
following property.  Let `P ⊂ ℝ` be finite with pairwise distances at least `δ > 0`, and let
`z ∈ ℂ` have distance at least `δ` from every point of `P`.  Then `Σ_{p ∈ P} 1/|z − p|² ≤ A/δ²`.

Label each `p` by `k(p) = ⌊(p − Re z)/δ⌋ ∈ ℤ`.  Separation makes `k` injective, and
`|z − p| ≥ δ · max(1, |k(p)| − 1)`.  Hence the sum is at most `δ⁻² Σ_{k ∈ ℤ} max(1, |k| − 1)⁻²`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The weight `max(1, |k| − 1)⁻²`. -/
def packWeight (k : ℤ) : ℝ := 1 / (max 1 (|(k : ℝ)| - 1)) ^ 2

theorem packWeight_nonneg (k : ℤ) : 0 ≤ packWeight k := by
  unfold packWeight
  positivity

theorem summable_packWeight : Summable packWeight := by
  have hg : Summable (fun k : ℤ => 4 * (1 / (k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left 4
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : ({k : ℤ | |k| < 2} : Set ℤ).Finite := by
    refine (Set.finite_Icc (-1 : ℤ) 1).subset fun k hk => ?_
    simp only [Set.mem_setOf_eq] at hk
    simp only [Set.mem_Icc]
    rw [abs_lt] at hk
    omega
  refine hfin.eventually_cofinite_notMem.mono fun k hk => ?_
  simp only [Set.mem_setOf_eq, not_lt] at hk
  have hk' : (2 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hk
  have hmax : max 1 (|(k : ℝ)| - 1) = |(k : ℝ)| - 1 := max_eq_right (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (packWeight_nonneg k), packWeight, hmax]
  have h1 : |(k : ℝ)| / 2 ≤ |(k : ℝ)| - 1 := by linarith
  have h2 : 0 < |(k : ℝ)| / 2 := by linarith
  calc 1 / (|(k : ℝ)| - 1) ^ 2 ≤ 1 / (|(k : ℝ)| / 2) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h2.le h1 2)
    _ = 4 * (1 / (k : ℝ) ^ 2) := by
        rw [div_pow, ← sq_abs (k : ℝ)]
        field_simp
        ring

/-- The packing constant. -/
def packConstant : ℝ := ∑' k : ℤ, packWeight k

theorem packConstant_pos : 0 < packConstant := by
  have h := summable_packWeight.le_tsum 0 (fun k _ => packWeight_nonneg k)
  have h0 : packWeight 0 = 1 := by simp [packWeight]
  unfold packConstant
  linarith

/-- **Inverse-square sums over separated points.** -/
theorem sum_inv_sq_le_of_separated {δ : ℝ} (hδ : 0 < δ) (P : Finset ℝ)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → δ ≤ |p - p'|) (z : ℂ)
    (hfar : ∀ p ∈ P, δ ≤ ‖z - p‖) :
    ∑ p ∈ P, 1 / ‖z - p‖ ^ 2 ≤ packConstant / δ ^ 2 := by
  classical
  set x : ℝ := z.re with hx
  set kf : ℝ → ℤ := fun p => ⌊(p - x) / δ⌋ with hkf
  have hinj : Set.InjOn kf P := by
    intro p hp p' hp' hpp
    by_contra hne
    have h := hsep p hp p' hp' hne
    have h1 := Int.floor_le ((p - x) / δ)
    have h2 := Int.lt_floor_add_one ((p - x) / δ)
    have h3 := Int.floor_le ((p' - x) / δ)
    have h4 := Int.lt_floor_add_one ((p' - x) / δ)
    simp only [hkf] at hpp
    rw [hpp] at h1 h2
    have h5 : |(p - x) / δ - (p' - x) / δ| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have h6 : (p - x) / δ - (p' - x) / δ = (p - p') / δ := by ring
    rw [h6, abs_div, abs_of_pos hδ, div_lt_one hδ] at h5
    linarith
  have hbound : ∀ p ∈ P, 1 / ‖z - p‖ ^ 2 ≤ packWeight (kf p) / δ ^ 2 := by
    intro p hp
    set k := kf p with hk
    have hk1 : (k : ℝ) ≤ (p - x) / δ := Int.floor_le _
    have hk2 : (p - x) / δ < k + 1 := Int.lt_floor_add_one _
    have habs : |(k : ℝ)| - 1 ≤ |p - x| / δ := by
      rw [show |p - x| / δ = |(p - x) / δ| by rw [abs_div, abs_of_pos hδ]]
      rcases le_or_gt 0 (k : ℝ) with hk0 | hk0
      · rw [abs_of_nonneg hk0]
        have : (k : ℝ) ≤ |(p - x) / δ| := hk1.trans (le_abs_self _)
        linarith
      · rw [abs_of_neg hk0]
        have : -((p - x) / δ) ≤ |(p - x) / δ| := neg_le_abs _
        linarith
    have hre : |p - x| ≤ ‖z - p‖ := by
      have := Complex.abs_re_le_norm (z - (p : ℂ))
      rw [Complex.sub_re, Complex.ofReal_re, ← hx, abs_sub_comm] at this
      exact this
    have hm : δ * max 1 (|(k : ℝ)| - 1) ≤ ‖z - p‖ := by
      rcases le_total 1 (|(k : ℝ)| - 1) with h | h
      · rw [max_eq_right h]
        have := mul_le_mul_of_nonneg_left habs hδ.le
        rw [mul_div_cancel₀ _ hδ.ne'] at this
        linarith
      · rw [max_eq_left h, mul_one]
        exact hfar p hp
    have hmpos : 0 < δ * max 1 (|(k : ℝ)| - 1) := mul_pos hδ (lt_max_of_lt_left one_pos)
    calc 1 / ‖z - p‖ ^ 2 ≤ 1 / (δ * max 1 (|(k : ℝ)| - 1)) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hmpos.le hm 2)
      _ = packWeight k / δ ^ 2 := by
          unfold packWeight
          rw [mul_pow]
          field_simp
  calc ∑ p ∈ P, 1 / ‖z - p‖ ^ 2 ≤ ∑ p ∈ P, packWeight (kf p) / δ ^ 2 :=
        Finset.sum_le_sum hbound
    _ = (∑ k ∈ P.image kf, packWeight k) / δ ^ 2 := by
        rw [Finset.sum_image hinj, Finset.sum_div]
    _ ≤ packConstant / δ ^ 2 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact summable_packWeight.sum_le_tsum _ (fun k _ => packWeight_nonneg k)

end

end GaloisForLFunctions.HTGeometry
