import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Tactic.Linarith

/-! Finite product weights factor on coordinatewise events.
Subadditivity bounds unions of such events. -/

noncomputable section

namespace WindowedLandauTheory.ConcN.FiniteWeight

open Classical in
/-- Sum of the weights of the elements of a finite event. -/
def weight {α : Type*} [Fintype α] (μ : α → ℝ) (S : Set α) : ℝ :=
  ∑ x, S.indicator μ x

section aux
variable {α β : Type*} [Fintype α]

theorem weight_eq_filter (μ : α → ℝ) (p : α → Prop) [DecidablePred p] :
    weight μ {x | p x} = ∑ x ∈ Finset.univ.filter p, μ x := by
  unfold weight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : p x <;> simp [Set.indicator, h]

theorem weight_eq_filter' (μ : α → ℝ) (s : Finset α) (p : α → Prop) [DecidablePred p] :
    weight μ {x | x ∈ s ∧ p x} = ∑ x ∈ s.filter p, μ x := by
  unfold weight
  rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ s)]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases h : p x <;> simp [Set.indicator, h, hx]
  · intro x _ hx
    simp [Set.indicator, hx]

theorem weight_mono (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) {S T : Set α} (h : S ⊆ T) :
    weight μ S ≤ weight μ T := by
  unfold weight
  exact Finset.sum_le_sum (fun x _ => Set.indicator_le_indicator_of_subset h hμ x)

theorem weight_nonneg (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S : Set α) : 0 ≤ weight μ S := by
  unfold weight
  exact Finset.sum_nonneg (fun x _ => Set.indicator_nonneg (fun y _ => hμ y) x)

theorem weight_union_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S T : Set α) :
    weight μ (S ∪ T) ≤ weight μ S + weight μ T := by
  unfold weight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have := hμ x
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [Set.indicator, hS, hT] <;> linarith

theorem weight_biUnion_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (t : Finset β) (S : β → Set α) :
    weight μ (⋃ b ∈ t, S b) ≤ ∑ b ∈ t, weight μ (S b) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [weight]
  | insert b t hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (weight_union_le μ hμ _ _).trans (by linarith)

theorem weight_compl (μ : α → ℝ) (S : Set α) : weight μ Sᶜ = weight μ Set.univ - weight μ S := by
  simp only [weight, Set.indicator_compl, Set.indicator_univ, Pi.sub_apply, Finset.sum_sub_distrib]

theorem weight_univ (μ : α → ℝ) : weight μ Set.univ = ∑ x, μ x := by
  simp [weight]

end aux

section prod
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι]

theorem weight_pi (P : Ω → ℝ) (S : ι → Set Ω) :
    weight (fun x : ι → Ω => ∏ v, P (x v)) {x | ∀ v, x v ∈ S v} = ∏ v, weight P (S v) := by
  classical
  unfold weight
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : ∀ v, x v ∈ S v
  · rw [Set.indicator_of_mem (show x ∈ {x : ι → Ω | ∀ v, x v ∈ S v} from h)]
    exact Finset.prod_congr rfl (fun v _ => (Set.indicator_of_mem (h v) P).symm)
  · push Not at h
    obtain ⟨v, hv⟩ := h
    have h0 : x ∉ {x : ι → Ω | ∀ v, x v ∈ S v} := fun hx => hv (hx v)
    have h1 : Set.indicator (S v) P (x v) = 0 := by simp [Set.indicator, hv]
    rw [Set.indicator_apply, if_neg h0, Finset.prod_eq_zero (Finset.mem_univ v) h1]

theorem weight_one_place (P : Ω → ℝ) (hP : ∑ c, P c = 1) (S : Set Ω) (v₀ : ι) :
    weight (fun x : ι → Ω => ∏ v, P (x v)) {x | x v₀ ∈ S} = weight P S := by
  have hset : {x : ι → Ω | x v₀ ∈ S} =
      {x : ι → Ω | ∀ v, x v ∈ (if v = v₀ then S else Set.univ)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h v
      split_ifs with hv
      · subst hv
        exact h
      · exact Set.mem_univ _
    · intro h
      simpa using h v₀
  rw [hset, weight_pi, Finset.prod_eq_single v₀]
  · simp
  · intro v _ hv
    simp [hv, weight_univ, hP]
  · intro h
    exact absurd (Finset.mem_univ v₀) h

end prod

end WindowedLandauTheory.ConcN.FiniteWeight

#print axioms WindowedLandauTheory.ConcN.FiniteWeight.weight_pi
#print axioms WindowedLandauTheory.ConcN.FiniteWeight.weight_biUnion_le
