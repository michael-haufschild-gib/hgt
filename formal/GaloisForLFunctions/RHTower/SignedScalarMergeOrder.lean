import GaloisForLFunctions.RHTower.UniformPrimeSubsetEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Sharp adaptive ordering for signed scalar leaves

Absorbing a leaf `a` into a scalar head `h` changes energy by `2*h*a`.
An opposite-sign leaf contracts energy; if none remains, the remaining
mergers increase energy toward the final endpoint. Strong induction supplies
a complete distinct order with every prefix below the larger endpoint.
-/

noncomputable section
open Finset
namespace RHTower
variable {α : Type*} [DecidableEq α]

/-- Energy of a scalar head after absorbing a subset of signed singleton leaves. -/
def scalarSubsetMergeEnergy (c : α → ℝ) (h : ℝ) (U P : Finset α) : ℝ :=
  (h+∑ p ∈ P,c p)^2+∑ p ∈ U \ P,(c p)^2

omit [DecidableEq α] in
private theorem scalar_nonneg_bound (c : α → ℝ) (h : ℝ) (U : Finset α)
    (hh : 0 ≤ h) (hc : ∀ p ∈ U,0 ≤ c p) :
    h^2+∑ p ∈ U,(c p)^2 ≤ (h+∑ p ∈ U,c p)^2 := by
  have hs := sum_sq_le_sq_sum_of_nonneg hc
  have hm := mul_nonneg hh (sum_nonneg hc)
  nlinarith only [hs,hm]

omit [DecidableEq α] in
private theorem scalar_nonpos_bound (c : α → ℝ) (h : ℝ) (U : Finset α)
    (hh : h ≤ 0) (hc : ∀ p ∈ U,c p ≤ 0) :
    h^2+∑ p ∈ U,(c p)^2 ≤ (h+∑ p ∈ U,c p)^2 := by
  have hb := scalar_nonneg_bound (fun p => -c p) (-h) U (by linarith)
    (fun p hp => by have := hc p hp; linarith)
  simpa only [neg_sq,sum_neg_distrib,← neg_add,neg_sq] using hb

/-- Absorbing one leaf gives the same scalar problem on the remaining leaves. -/
theorem scalarSubsetMergeEnergy_insert (c : α → ℝ) (h : ℝ) (U R : Finset α)
    (p : α) (hpR : p ∉ R) :
    scalarSubsetMergeEnergy c h U (insert p R) =
      scalarSubsetMergeEnergy c (h+c p) (U.erase p) R := by
  have he : U \ insert p R=U.erase p \ R := by ext q; simp; tauto
  simp only [scalarSubsetMergeEnergy,sum_insert hpR,he]
  ring

private theorem scalar_safe_first (c : α → ℝ) (h : ℝ) (U : Finset α) (hU : U.Nonempty) :
    ∃ p ∈ U,(h+c p)^2+∑ q ∈ U.erase p,(c q)^2 ≤
      max (h^2+∑ q ∈ U,(c q)^2) ((h+∑ q ∈ U,c q)^2) := by
  by_cases hx : ∃ p ∈ U,h*c p ≤ 0
  · obtain ⟨p,hp,hs⟩ := hx
    refine ⟨p,hp,le_trans ?_ (le_max_left _ _)⟩
    have he := sum_erase_add U (fun q => (c q)^2) hp
    nlinarith only [he,hs]
  · obtain ⟨p,hp⟩ := hU
    have hs : ∀ q ∈ U,0<h*c q := by
      intro q hq
      exact lt_of_not_ge (fun hn => hx ⟨q,hq,hn⟩)
    have he := sum_erase_add U c hp
    refine ⟨p,hp,le_trans ?_ (le_max_right _ _)⟩
    by_cases hh : 0 ≤ h
    · have hc : ∀ q ∈ U,0 ≤ c q := by
        intro q hq
        have hpos := hs q hq
        by_contra hn
        have hm := mul_nonpos_of_nonneg_of_nonpos hh (le_of_not_ge hn)
        linarith
      have hb := scalar_nonneg_bound c (h+c p) (U.erase p)
        (add_nonneg hh (hc p hp)) (fun q hq => hc q (mem_of_mem_erase hq))
      have ht : h+c p+∑ q ∈ U.erase p,c q=h+∑ q ∈ U,c q := by linarith only [he]
      rw [ht] at hb
      exact hb
    · have hh' : h ≤ 0 := le_of_not_ge hh
      have hc : ∀ q ∈ U,c q ≤ 0 := by
        intro q hq
        have hpos := hs q hq
        by_contra hn
        have hm := mul_nonpos_of_nonpos_of_nonneg hh' (le_of_not_ge hn)
        linarith
      have hb := scalar_nonpos_bound c (h+c p) (U.erase p)
        (add_nonpos hh' (hc p hp)) (fun q hq => hc q (mem_of_mem_erase hq))
      have ht : h+c p+∑ q ∈ U.erase p,c q=h+∑ q ∈ U,c q := by linarith only [he]
      rw [ht] at hb
      exact hb

/-- Signed scalar leaves admit a complete order bounded by the larger endpoint energy. -/
theorem exists_scalarSubsetMergeOrder (c : α → ℝ) (h : ℝ) (U : Finset α) :
    ∃ l : List α,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      scalarSubsetMergeEnergy c h U (l.take k).toFinset ≤
        max (h^2+∑ p ∈ U,(c p)^2) ((h+∑ p ∈ U,c p)^2) := by
  revert h
  refine Finset.strongInductionOn U ?_
  intro U ih h
  by_cases hU : U.Nonempty
  · obtain ⟨p,hp,hsafe⟩ := scalar_safe_first c h U hU
    obtain ⟨l,hl,hset,hbound⟩ := ih (U.erase p) (erase_ssubset hp) (h+c p)
    have hpL : p ∉ l := by
      intro hpl
      have hm : p ∈ l.toFinset := List.mem_toFinset.mpr hpl
      rw [hset] at hm
      exact notMem_erase p U hm
    have htotal : h+c p+∑ q ∈ U.erase p,c q=h+∑ q ∈ U,c q := by
      have := sum_erase_add U c hp
      linarith
    refine ⟨p::l,List.nodup_cons.mpr ⟨hpL,hl⟩,?_,?_⟩
    · simp [hset,insert_erase hp]
    · intro k
      cases k with
      | zero => simp [scalarSubsetMergeEnergy]
      | succ k =>
        have hpR : p ∉ (l.take k).toFinset := by
          simp only [List.mem_toFinset]
          exact fun hx => hpL (List.mem_of_mem_take hx)
        simp only [List.take_succ_cons,List.toFinset_cons]
        rw [scalarSubsetMergeEnergy_insert c h U _ p hpR]
        refine (hbound k).trans ?_
        rw [htotal]
        exact max_le hsafe (le_max_right _ _)
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    subst U
    exact ⟨[],by simp,by simp,by simp [scalarSubsetMergeEnergy]⟩

/-- A scalar terminal ceiling is attainable exactly when both endpoints satisfy it. -/
theorem exists_scalarSubsetMergeOrder_iff (c : α → ℝ) (h B : ℝ) (U : Finset α) :
    (∃ l : List α,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      scalarSubsetMergeEnergy c h U (l.take k).toFinset ≤ B) ↔
    h^2+∑ p ∈ U,(c p)^2 ≤ B ∧ (h+∑ p ∈ U,c p)^2 ≤ B := by
  constructor
  · rintro ⟨l,hl,hset,hbound⟩
    constructor
    · simpa [scalarSubsetMergeEnergy] using hbound 0
    · simpa [scalarSubsetMergeEnergy,hset] using hbound l.length
  · rintro ⟨hi,hf⟩
    obtain ⟨l,hl,hset,hbound⟩ := exists_scalarSubsetMergeOrder c h U
    exact ⟨l,hl,hset,fun k => (hbound k).trans (max_le hi hf)⟩

/-- A fibre field supported on empty and singleton labels has an exact linear-size sum. -/
theorem sum_powerset_of_card_le_one_support (U : Finset α) (f : Finset α → ℝ)
    (hf : ∀ R ⊆ U,1<R.card → f R=0) :
    (∑ R ∈ U.powerset,f R)=f ∅+∑ p ∈ U,f {p} := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert p U hpU ih =>
    rw [sum_powerset_insert hpU]
    have hi := ih (fun R hR => hf R (hR.trans (subset_insert p U)))
    rw [hi,sum_insert hpU]
    have he : (∑ R ∈ U.powerset,f (insert p R))=f {p} := by
      rw [sum_eq_single ∅]
      · simp
      · intro R hR hne
        apply hf (insert p R) (insert_subset_insert p (mem_powerset.mp hR))
        have hpR : p ∉ R := fun hm => hpU (mem_powerset.mp hR hm)
        rw [card_insert_of_notMem hpR]
        have := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
        omega
      · simp
    rw [he]
    ring
end RHTower
