import GaloisForLFunctions.HTGeometry.AllDepthCompletenessCore

/-!
# The period span of a finite set of directions

`periodSpan τ t = ℤ + ∑_(i ∈ t) ℤ τ i` as an additive subgroup of `ℂ`.  Integral independence of
`1` and the parameters makes every direction outside `t` of infinite order modulo it.

* `periodSpan`, `mem_periodSpan_iff`, `tripticPeriodGroup_le_periodSpan`;
* **`periodSpan_free`**.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The subgroup `ℤ + ∑_(i ∈ t) ℤ τ i`. -/
def periodSpan (τ : ι → ℂ) (t : Finset ι) : AddSubgroup ℂ where
  carrier := {p | ∃ (a : ℤ) (n : ι → ℤ), p = (a : ℂ) + ∑ i ∈ t, (n i : ℂ) * τ i}
  zero_mem' := ⟨0, fun _ => 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, n, rfl⟩ ⟨b, m, rfl⟩
    refine ⟨a + b, fun i => n i + m i, ?_⟩
    have hs : ∑ i ∈ t, (((n i + m i : ℤ)) : ℂ) * τ i
        = (∑ i ∈ t, (n i : ℂ) * τ i) + ∑ i ∈ t, (m i : ℂ) * τ i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [hs]
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, n, rfl⟩
    refine ⟨-a, fun i => -n i, ?_⟩
    have hs : ∑ i ∈ t, (((-n i : ℤ)) : ℂ) * τ i = -∑ i ∈ t, (n i : ℂ) * τ i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [hs]
    push_cast
    ring

theorem mem_periodSpan_iff {τ : ι → ℂ} {t : Finset ι} {p : ℂ} :
    p ∈ periodSpan τ t ↔ ∃ (a : ℤ) (n : ι → ℤ), p = (a : ℂ) + ∑ i ∈ t, (n i : ℂ) * τ i := Iff.rfl

/-- **A direction outside the set has infinite order modulo the span.** -/
theorem periodSpan_free (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) {t : Finset ι} {k : ι}
    (hk : k ∉ t) (m : ℤ) (h : (m : ℂ) * τ k ∈ periodSpan τ t) : m = 0 := by
  classical
  obtain ⟨a, n, hrel⟩ := h
  set c : ι → ℤ := fun l => (if l = k then m else 0) - (if l ∈ t then n l else 0) with hc
  have hterm : ∀ l : ι, ((c l : ℤ) : ℂ) * τ l
      = (if l = k then (m : ℂ) * τ l else 0) - (if l ∈ t then (n l : ℂ) * τ l else 0) := by
    intro l
    simp only [hc]
    push_cast
    split_ifs <;> ring
  have hsum : ∑ l, ((c l : ℤ) : ℂ) * τ l = (m : ℂ) * τ k - ∑ i ∈ t, (n i : ℂ) * τ i := by
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ k (fun l => (m : ℂ) * τ l)]
    congr 1
    · simp
    · rw [Finset.sum_ite_mem]
      congr 1
      exact Finset.univ_inter t
  have hzero : (((-a : ℤ)) : ℂ) + ∑ l, ((c l : ℤ) : ℂ) * τ l = 0 := by
    rw [hsum]
    push_cast
    linear_combination hrel
  obtain ⟨-, hcl⟩ := hQ (-a) c hzero
  have hck := hcl k
  simp only [hc, if_pos, if_neg hk, sub_zero] at hck
  omega

theorem tripticPeriodGroup_le_periodSpan (τ : ι → ℂ) {t : Finset ι} {i j : ι}
    (hi : i ∈ t) (hj : j ∈ t) :
    tripticPeriodGroup (τ j) (τ i) ≤ periodSpan τ t := by
  classical
  rintro p ⟨u, v, w, rfl⟩
  refine ⟨u, fun l => (if l = j then v else 0) + (if l = i then w else 0), ?_⟩
  have hterm : ∀ l : ι,
      (((if l = j then v else 0) + (if l = i then w else 0) : ℤ) : ℂ) * τ l
        = (if l = j then (v : ℂ) * τ l else 0) + (if l = i then (w : ℂ) * τ l else 0) := by
    intro l
    push_cast
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib,
    Finset.sum_ite_eq' t j (fun l => (v : ℂ) * τ l),
    Finset.sum_ite_eq' t i (fun l => (w : ℂ) * τ l), if_pos hj, if_pos hi]
  ring

end

end GaloisForLFunctions
