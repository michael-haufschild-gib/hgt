import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-!
# A trichotomy for factor lengths

Above total mass `2τ`, finite nonnegative weights have a large atom, a balanced
bipartition, or a partition into a singleton and two sets of mass below `τ`.
This is the combinatorial mechanism of Lemma 7.1 of arXiv:2610.09567, with no
normalization of the total mass. Absolute values make the statement apply to
every real weight family and threshold, including the degenerate cases.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

/-- Total magnitude of the logarithmic lengths of a set of factors. -/
def factorMass {ι : Type*} (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, |w i|

@[simp] theorem factorMass_empty {ι : Type*} (w : ι → ℝ) : factorMass w ∅ = 0 :=
  Finset.sum_empty

@[simp] theorem factorMass_singleton {ι : Type*} (w : ι → ℝ) (i : ι) :
    factorMass w {i} = |w i| := Finset.sum_singleton _ _

theorem factorMass_mono {ι : Type*} (w : ι → ℝ) {u s : Finset ι} (h : u ⊆ s) :
    factorMass w u ≤ factorMass w s :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => abs_nonneg (w i))

theorem factorMass_add_sdiff {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) {u s : Finset ι} (h : u ⊆ s) :
    factorMass w u + factorMass w (s \ u) = factorMass w s := by
  exact (add_comm _ _).trans (Finset.sum_sdiff h)

private theorem factorMass_insert {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) {u : Finset ι} {i : ι} (hi : i ∉ u) :
    factorMass w (insert i u) = factorMass w u + |w i| := by
  rw [factorMass, Finset.sum_insert hi, add_comm]
  rfl

/-- Maximal cardinality prevents any unused atom from enlarging a light set. -/
private theorem exists_maximal_light_subset {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (τ : ℝ) (s : Finset ι) (hτ : 0 < τ) :
    ∃ u ⊆ s, factorMass w u < τ ∧
      ∀ i ∈ s \ u, τ ≤ factorMass w u + |w i| := by
  classical
  let candidates := s.powerset.filter fun u => factorMass w u < τ
  have hc : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset,
      Finset.empty_subset, factorMass_empty, true_and]
    exact hτ
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image candidates Finset.card hc
  have hu' : u ⊆ s ∧ factorMass w u < τ := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset] using hu
  refine ⟨u, hu'.1, hu'.2, ?_⟩
  intro i hi
  obtain ⟨his, hiu⟩ := Finset.mem_sdiff.mp hi
  by_contra h
  have hlight : factorMass w (insert i u) < τ := by
    rw [factorMass_insert w hiu]
    exact lt_of_not_ge h
  have hc' : insert i u ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset his hu'.1, hlight⟩
  have hcard := hmax (insert i u) hc'
  rw [Finset.card_insert_of_notMem hiu] at hcard
  omega

/-- Two maximal light sets leave exactly one atom when no balanced split exists. -/
private theorem exceptional_split {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (τ : ℝ) (s : Finset ι) (hτ : 0 < τ)
    (htotal : 2 * τ < factorMass w s) (hcap : ∀ i ∈ s, |w i| ≤ τ)
    (hbalanced : ¬ ∃ u ⊆ s, τ ≤ factorMass w u ∧ τ ≤ factorMass w (s \ u)) :
    ∃ i u v, Disjoint u v ∧ i ∉ u ∧ i ∉ v ∧ insert i (u ∪ v) = s ∧
      |w i| ∈ Set.Ioc (factorMass w s - 2 * τ) τ ∧
      factorMass w u ∈ Set.Ioo (factorMass w s - 2 * τ) τ ∧
      factorMass w v ∈ Set.Ioo (factorMass w s - 2 * τ) τ := by
  obtain ⟨u, hus, hu, hmaxu⟩ := exists_maximal_light_subset w τ s hτ
  obtain ⟨v, hvs, hv, hmaxv⟩ := exists_maximal_light_subset w τ (s \ u) hτ
  have hsumu := factorMass_add_sdiff w hus
  have hsumv := factorMass_add_sdiff w hvs
  have hne : ((s \ u) \ v).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, factorMass_empty] at hsumv
    linarith only [hsumu, hsumv, hu, hv, htotal]
  obtain ⟨i, hi⟩ := hne
  obtain ⟨hir, hiv⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨his, hiu⟩ := Finset.mem_sdiff.mp hir
  have hone : (s \ u) \ v = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, ?_⟩
    intro j hj
    by_contra hji
    obtain ⟨hjr, hjv⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨hjs, hju⟩ := Finset.mem_sdiff.mp hjr
    have hA : insert i u ⊆ s := Finset.insert_subset his hus
    have hB : insert j v ⊆ s \ insert i u := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hkv
      · exact Finset.mem_sdiff.mpr ⟨hjs, by
          simpa only [Finset.mem_insert, not_or] using And.intro hji hju⟩
      · obtain ⟨hks, hku⟩ := Finset.mem_sdiff.mp (hvs hkv)
        have hki : k ≠ i := fun h => hiv (h ▸ hkv)
        exact Finset.mem_sdiff.mpr ⟨hks, by
          simpa only [Finset.mem_insert, not_or] using And.intro hki hku⟩
    have hAmass : τ ≤ factorMass w (insert i u) := by
      rw [factorMass_insert w hiu]
      exact hmaxu i hir
    have hBmass : τ ≤ factorMass w (insert j v) := by
      rw [factorMass_insert w hjv]
      exact hmaxv j hj
    exact hbalanced ⟨insert i u, hA, hAmass,
      hBmass.trans (factorMass_mono w hB)⟩
  have hdis : Disjoint u v := Finset.disjoint_left.mpr fun _ hku hkv =>
    (Finset.mem_sdiff.mp (hvs hkv)).2 hku
  have hcover : insert i (u ∪ v) = s := by
    have hc := Finset.union_sdiff_of_subset hvs
    rw [hone] at hc
    have hs := Finset.union_sdiff_of_subset hus
    rw [← hc] at hs
    calc
      insert i (u ∪ v) = u ∪ (v ∪ {i}) := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
          or_assoc, or_comm, or_left_comm]
      _ = s := hs
  rw [hone, factorMass_singleton] at hsumv
  have hwi := hcap i his
  refine ⟨i, u, v, hdis, hiu, hiv, hcover, ⟨?_, hwi⟩, ⟨?_, hu⟩, ⟨?_, hv⟩⟩
  · linarith only [hsumu, hsumv, hu, hv]
  · linarith only [hsumu, hsumv, hv, hwi]
  · linarith only [hsumu, hsumv, hu, hwi]

/-- Every finite family is small, has a large atom, splits into two heavy sets,
or splits into a singleton and two light sets with sharp lower bounds. -/
theorem factorMass_trichotomy {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (t : ℝ) (s : Finset ι) :
    factorMass w s ≤ 2 * |t| ∨
    (∃ i ∈ s, |t| < |w i|) ∨
    (∃ u ⊆ s, |t| ≤ factorMass w u ∧ |t| ≤ factorMass w (s \ u)) ∨
    ∃ i u v, Disjoint u v ∧ i ∉ u ∧ i ∉ v ∧ insert i (u ∪ v) = s ∧
      |w i| ∈ Set.Ioc (factorMass w s - 2 * |t|) |t| ∧
      factorMass w u ∈ Set.Ioo (factorMass w s - 2 * |t|) |t| ∧
      factorMass w v ∈ Set.Ioo (factorMass w s - 2 * |t|) |t| := by
  classical
  by_cases hsmall : factorMass w s ≤ 2 * |t|
  · exact Or.inl hsmall
  right
  by_cases hlarge : ∃ i ∈ s, |t| < |w i|
  · exact Or.inl hlarge
  right
  by_cases hbalanced : ∃ u ⊆ s, |t| ≤ factorMass w u ∧ |t| ≤ factorMass w (s \ u)
  · exact Or.inl hbalanced
  have hcap : ∀ i ∈ s, |w i| ≤ |t| := fun i hi =>
    le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)
  have hpos : 0 < |t| := by
    by_contra h
    have hnonpos : factorMass w s ≤ 0 :=
      Finset.sum_nonpos fun i hi => (hcap i hi).trans (le_of_not_gt h)
    exact hsmall (hnonpos.trans (mul_nonneg (by norm_num) (abs_nonneg t)))
  exact Or.inr (exceptional_split w |t| s hpos (lt_of_not_ge hsmall) hcap hbalanced)

#print axioms factorMass_trichotomy

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
