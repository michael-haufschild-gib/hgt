import GaloisForLFunctions.HTGeometry.ReplicaAmplitudeMoments

/-!
# Counting tuples with a prescribed histogram

The number of tuples `Fin m → I` realizing a prescribed multiplicity vector is the multinomial
coefficient of that vector.  The proof splits a tuple into its first entry and its tail, which turns
the count into the Pascal recursion for multinomial coefficients.

For a product alphabet the componentwise histograms are independent, so the number of tuples with
prescribed component histograms is the product of the component multinomials.  These two counts are
the bridge between tuple-indexed and multiplicity-vector-indexed replica sums.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The multiplicity vector of a finite tuple. -/
def tupleHistogram {m : ℕ} (f : Fin m → I) (i : I) : ℕ :=
  (Finset.univ.filter fun s => f s = i).card

theorem sum_tupleHistogram {m : ℕ} (f : Fin m → I) : ∑ i, tupleHistogram f i = m := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset I))
    (fun a _ => Finset.mem_univ (f a))
  simpa [tupleHistogram, eq_comm] using h.symm

omit [Fintype I] in
theorem tupleHistogram_cons {m : ℕ} (i : I) (g : Fin m → I) (j : I) :
    tupleHistogram (Fin.cons i g) j = tupleHistogram g j + (if i = j then 1 else 0) := by
  classical
  simp only [tupleHistogram, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_succ, Fin.cons_zero, add_comm]

/-- **The histogram fibre count.**  Exactly `multinomial k` tuples of length `m` realize the
multiplicity vector `k`. -/
theorem card_tupleHistogram_fiber :
    ∀ (m : ℕ) (k : I → ℕ), ∑ i, k i = m →
      (Finset.univ.filter fun f : Fin m → I => tupleHistogram f = k).card
        = Nat.multinomial Finset.univ k := by
  classical
  intro m
  induction m with
  | zero =>
      intro k hk
      have hk0 : k = fun _ => 0 := by
        funext i
        have := Finset.sum_eq_zero_iff.mp hk i (Finset.mem_univ i)
        exact this
      subst hk0
      have hfilter : (Finset.univ.filter
          fun f : Fin 0 → I => tupleHistogram f = fun _ => 0) = Finset.univ := by
        refine Finset.filter_true_of_mem fun f _ => ?_
        funext i
        simp [tupleHistogram]
      rw [hfilter]
      have hcard : (Finset.univ : Finset (Fin 0 → I)).card = 1 := by
        simp
      rw [hcard]
      have hspec := Nat.multinomial_spec (Finset.univ : Finset I) (fun _ : I => 0)
      simpa using hspec.symm
  | succ m ih =>
      intro k hk
      have hfiber : ∀ i : I,
          ((Finset.univ.filter fun f : Fin (m + 1) → I => tupleHistogram f = k).filter
              fun f => f 0 = i).card
            = if k i = 0 then 0 else Nat.multinomial Finset.univ (Function.update k i (k i - 1)) := by
        intro i
        by_cases hki : k i = 0
        · rw [if_pos hki]
          refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun f hf => ?_)
          rw [Finset.mem_filter, Finset.mem_filter] at hf
          obtain ⟨⟨-, hhist⟩, hf0⟩ := hf
          have hpos : 0 < tupleHistogram f i := by
            refine Finset.card_pos.mpr ⟨0, ?_⟩
            simp [hf0]
          rw [hhist] at hpos
          omega
        · rw [if_neg hki]
          have hupd : ∑ j, Function.update k i (k i - 1) j = m := by
            rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.erase_eq]
            have hsplit2 : ∑ j ∈ Finset.univ.erase i, k j + k i = ∑ j, k j :=
              Finset.sum_erase_add _ _ (Finset.mem_univ i)
            have hki' : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr hki
            omega
          rw [← ih (Function.update k i (k i - 1)) hupd]
          refine Finset.card_nbij' (fun f => Fin.tail f) (fun g => Fin.cons i g) ?_ ?_ ?_ ?_
          · intro f hf
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
            obtain ⟨hhist, hf0⟩ := hf
            funext j
            have hcons := tupleHistogram_cons (i := f 0) (g := Fin.tail f) (j := j)
            rw [Fin.cons_self_tail, hhist, hf0] at hcons
            by_cases hj : i = j
            · subst hj
              rw [if_pos rfl] at hcons
              rw [Function.update_self]
              omega
            · rw [if_neg hj] at hcons
              rw [Function.update_of_ne (fun h => hj h.symm)]
              omega
          · intro g hg
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
            refine ⟨?_, by simp⟩
            funext j
            rw [tupleHistogram_cons, hg]
            by_cases hj : i = j
            · subst hj
              rw [Function.update_self, if_pos rfl]
              omega
            · rw [Function.update_of_ne (fun h => hj h.symm), if_neg hj, Nat.add_zero]
          · intro f hf
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
            show Fin.cons i (Fin.tail f) = f
            rw [← hf.2]
            exact Fin.cons_self_tail f
          · intro g _
            simp
      have hsplit := Finset.card_eq_sum_card_fiberwise
        (f := fun f : Fin (m + 1) → I => f 0)
        (s := Finset.univ.filter fun f : Fin (m + 1) → I => tupleHistogram f = k)
        (t := (Finset.univ : Finset I)) (fun a _ => Finset.mem_univ _)
      rw [hsplit]
      have hsum : ∑ i : I, ((Finset.univ.filter
            fun f : Fin (m + 1) → I => tupleHistogram f = k).filter fun f => f 0 = i).card
          = ∑ i ∈ Finset.univ.filter fun i => k i ≠ 0,
              Nat.multinomial Finset.univ (Function.update k i (k i - 1)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hfiber i]
        by_cases hki : k i = 0 <;> simp [hki]
      rw [hsum]
      exact multinomial_sum_update_pred hk

/-! ## Product alphabets -/

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **Componentwise histogram fibre count.**  Over a product alphabet the componentwise
multiplicity vectors are independent, so the number of tuples realizing prescribed component
histograms is the product of the component multinomials. -/
theorem card_componentHistogram_fiber {J : C → Type*} [∀ c, Fintype (J c)]
    [∀ c, DecidableEq (J c)] (m : ℕ) (k : ∀ c, J c → ℕ) (hk : ∀ c, ∑ i, k c i = m) :
    (Finset.univ.filter fun f : Fin m → (∀ c, J c) =>
        ∀ c, tupleHistogram (fun s => f s c) = k c).card
      = ∏ c, Nat.multinomial Finset.univ (k c) := by
  classical
  have hcard : (Finset.univ.filter fun f : Fin m → (∀ c, J c) =>
      ∀ c, tupleHistogram (fun s => f s c) = k c).card
      = (Fintype.piFinset fun c =>
          Finset.univ.filter fun g : Fin m → J c => tupleHistogram g = k c).card := by
    refine Finset.card_nbij' (fun f c s => f s c) (fun F s c => F c s) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_filter]
      exact fun c => ⟨Finset.mem_univ _, hf.2 c⟩
    · intro F hF
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_filter] at hF
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨Finset.mem_univ _, fun c => (hF c).2⟩
    · intro f _
      rfl
    · intro F _
      rfl
  rw [hcard, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun c _ => card_tupleHistogram_fiber m (k c) (hk c)

end GaloisForLFunctions.HTGeometry
