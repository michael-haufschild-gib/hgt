/-
# Sign alternation and the arc count of a real branch polynomial

A real branch polynomial written as a positive factor times a product of distinct linear factors
has alternating sign on the complementary intervals of its real root set.  When the number of real
roots is odd, exactly half of the resulting intervals carry a positive sign.

This is the real-topology core of the hyperelliptic branch count: for a branch polynomial with
`2r + 1` simple real roots the real projective line is cut into `2r + 2` arcs, of which exactly
`r + 1` are arcs of positivity.
-/
import Mathlib

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- A product of negative factors is positive exactly when the number of factors is even. -/
theorem prod_neg_pos_iff {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → ℝ}
    (h : ∀ i ∈ s, x i < 0) : 0 < ∏ i ∈ s, x i ↔ Even s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hxa : x a < 0 := h a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, x i < 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hQ : ∏ i ∈ s, x i ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr (fun i hi => ne_of_lt (hrest i hi))
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.even_add_one, ← ih hrest]
      constructor
      · intro hpos hQpos
        nlinarith
      · intro hQnot
        have hQneg : ∏ i ∈ s, x i < 0 := lt_of_le_of_ne (not_lt.mp hQnot) hQ
        nlinarith

theorem card_filter_lt_fin (m j : ℕ) (hj : j ≤ m) :
    (univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  classical
  rw [← Finset.card_range j]
  refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  · intro i hi i' hi' h
    exact Fin.ext h
  · intro b hb
    have hb' : b < j := Finset.mem_range.mp hb
    exact ⟨⟨b, lt_of_lt_of_le hb' hj⟩, by simp [hb'], rfl⟩

variable {m : ℕ}

/-- The `j`-th complementary interval of a strictly increasing finite family. -/
def rootGap (a : Fin m → ℝ) (j : Fin (m + 1)) : Set ℝ :=
  {t | (∀ i : Fin m, (i : ℕ) < (j : ℕ) → a i < t) ∧ (∀ i : Fin m, (j : ℕ) ≤ (i : ℕ) → t < a i)}

/-- **Sign alternation.**  On the `j`-th complementary interval the product of the linear factors
is positive exactly when the number of roots to the right is even. -/
theorem prod_pos_on_rootGap_iff (a : Fin m → ℝ) (j : Fin (m + 1)) {t : ℝ}
    (ht : t ∈ rootGap a j) :
    0 < ∏ i, (t - a i) ↔ Even (m - (j : ℕ)) := by
  classical
  obtain ⟨hlt, hgt⟩ := ht
  have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.2
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (univ : Finset (Fin m)) (fun i => (i : ℕ) < (j : ℕ)) (fun i => t - a i)
  have hposs : 0 < ∏ i ∈ univ.filter (fun i : Fin m => (i : ℕ) < (j : ℕ)), (t - a i) := by
    refine Finset.prod_pos (fun i hi => ?_)
    have := (Finset.mem_filter.mp hi).2
    linarith [hlt i this]
  have hnegs : ∀ i ∈ univ.filter (fun i : Fin m => ¬ ((i : ℕ) < (j : ℕ))), t - a i < 0 := by
    intro i hi
    have hij : (j : ℕ) ≤ (i : ℕ) := by
      have := (Finset.mem_filter.mp hi).2
      omega
    linarith [hgt i hij]
  have hcard : (univ.filter (fun i : Fin m => ¬ ((i : ℕ) < (j : ℕ)))).card = m - (j : ℕ) := by
    have htot := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin m))) (p := fun i : Fin m => (i : ℕ) < (j : ℕ))
    rw [card_filter_lt_fin m (j : ℕ) hjm, Finset.card_univ, Fintype.card_fin] at htot
    omega
  rw [← hsplit]
  constructor
  · intro hpos
    have h2 : 0 < ∏ i ∈ univ.filter (fun i : Fin m => ¬ ((i : ℕ) < (j : ℕ))), (t - a i) := by
      nlinarith [hposs]
    rw [← hcard]
    exact (prod_neg_pos_iff hnegs).mp h2
  · intro heven
    have h2 : 0 < ∏ i ∈ univ.filter (fun i : Fin m => ¬ ((i : ℕ) < (j : ℕ))), (t - a i) :=
      (prod_neg_pos_iff hnegs).mpr (by rw [hcard]; exact heven)
    positivity

/-- **The arc count.**  With `2r + 1` real branch points the real line is cut into `2r + 2`
complementary intervals, of which exactly `r + 1` carry a positive sign. -/
theorem card_positive_rootGaps (r : ℕ) :
    (univ.filter (fun j : Fin (2 * r + 2) => Even ((2 * r + 1) - (j : ℕ)))).card = r + 1 := by
  classical
  have hiff : ∀ j : Fin (2 * r + 2), Even ((2 * r + 1) - (j : ℕ)) ↔ (j : ℕ) % 2 = 1 := by
    intro j
    have hj : (j : ℕ) ≤ 2 * r + 1 := Nat.lt_succ_iff.mp j.2
    rw [Nat.even_iff]
    omega
  rw [Finset.filter_congr (fun j _ => by rw [hiff j])]
  rw [← Finset.card_range (r + 1)]
  refine Finset.card_bij (fun j _ => ((j : ℕ) - 1) / 2) ?_ ?_ ?_
  · intro j hj
    have hj2 : (j : ℕ) < 2 * r + 2 := j.2
    have hodd : (j : ℕ) % 2 = 1 := (Finset.mem_filter.mp hj).2
    refine Finset.mem_range.mpr ?_
    omega
  · intro j hj j' hj' h
    have hodd : (j : ℕ) % 2 = 1 := (Finset.mem_filter.mp hj).2
    have hodd' : (j' : ℕ) % 2 = 1 := (Finset.mem_filter.mp hj').2
    refine Fin.ext ?_
    omega
  · intro b hb
    have hb' : b < r + 1 := Finset.mem_range.mp hb
    refine ⟨⟨2 * b + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, by simp⟩


/-! ## Nonempty gaps and the positivity arc count -/

theorem rootGap_nonempty {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a) (j : Fin (m + 1)) :
    (rootGap a j).Nonempty := by
  classical
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · refine ⟨0, ?_, ?_⟩
      · intro i _
        exact absurd i.2 (by omega)
      · intro i _
        exact absurd i.2 (by omega)
    · refine ⟨a ⟨0, hm⟩ - 1, ?_, ?_⟩
      · intro i hi
        omega
      · intro i _
        have hle : a ⟨0, hm⟩ ≤ a i := ha.monotone (Fin.le_def.mpr (Nat.zero_le _))
        linarith
  · rcases Nat.lt_or_ge (j : ℕ) m with hjm | hjm
    · have hprev : (j : ℕ) - 1 < m := by omega
      have hlt : a ⟨(j : ℕ) - 1, hprev⟩ < a ⟨(j : ℕ), hjm⟩ :=
        ha (Fin.lt_def.mpr (show (j : ℕ) - 1 < (j : ℕ) by omega))
      refine ⟨(a ⟨(j : ℕ) - 1, hprev⟩ + a ⟨(j : ℕ), hjm⟩) / 2, ?_, ?_⟩
      · intro i hi
        have hle : a i ≤ a ⟨(j : ℕ) - 1, hprev⟩ :=
          ha.monotone (Fin.le_def.mpr (show (i : ℕ) ≤ (j : ℕ) - 1 by omega))
        linarith
      · intro i hi
        have hle : a ⟨(j : ℕ), hjm⟩ ≤ a i :=
          ha.monotone (Fin.le_def.mpr (show (j : ℕ) ≤ (i : ℕ) by omega))
        linarith
    · have hm : 0 < m := by omega
      refine ⟨a ⟨m - 1, by omega⟩ + 1, ?_, ?_⟩
      · intro i _
        have hle : a i ≤ a ⟨m - 1, by omega⟩ :=
          ha.monotone (Fin.le_def.mpr (show (i : ℕ) ≤ m - 1 by omega))
        linarith
      · intro i hi
        exact absurd i.2 (by omega)

open scoped Classical in
/-- **The positivity arc count.**  A positive factor times the product of `2r + 1` distinct linear
factors is positive on exactly `r + 1` of the `2r + 2` complementary intervals. -/
theorem card_positive_arcs {r : ℕ} (a : Fin (2 * r + 1) → ℝ) (ha : StrictMono a)
    (P : ℝ → ℝ) (hP : ∀ t, 0 < P t) :
    (univ.filter (fun j : Fin (2 * r + 2) =>
        ∀ t ∈ rootGap a j, 0 < P t * ∏ i, (t - a i))).card = r + 1 := by
  have hsets : (univ.filter (fun j : Fin (2 * r + 2) =>
        ∀ t ∈ rootGap a j, 0 < P t * ∏ i, (t - a i)))
      = univ.filter (fun j : Fin (2 * r + 2) => Even ((2 * r + 1) - (j : ℕ))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      obtain ⟨t, ht⟩ := rootGap_nonempty a ha j
      have hval := hall t ht
      have hprod : 0 < ∏ i, (t - a i) := by
        by_contra hcon
        push Not at hcon
        nlinarith [hP t]
      exact (prod_pos_on_rootGap_iff a j ht).mp hprod
    · intro heven t ht
      exact mul_pos (hP t) ((prod_pos_on_rootGap_iff a j ht).mpr heven)
  rw [hsets, card_positive_rootGaps]


/-! ## The real double cover over a positivity arc -/

/-- **The real double cover of a positivity arc is one oval.**  Over a closed interval on which the
branch function is nonnegative and vanishes at the left endpoint, the real points of `y² = f t`
form a connected set: the two sheets are continuous images of the interval and meet at the branch
point. -/
theorem isConnected_realDoubleCover {f : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : ContinuousOn f (Set.Icc α β)) (hnn : ∀ t ∈ Set.Icc α β, 0 ≤ f t) (hα : f α = 0) :
    IsConnected {p : ℝ × ℝ | p.1 ∈ Set.Icc α β ∧ p.2 ^ 2 = f p.1} := by
  classical
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Set.Icc α β ∧ p.2 ^ 2 = f p.1} with hS
  set up : ℝ → ℝ × ℝ := fun t => (t, Real.sqrt (f t)) with hup
  set dn : ℝ → ℝ × ℝ := fun t => (t, -Real.sqrt (f t)) with hdn
  have hcup : ContinuousOn up (Set.Icc α β) :=
    continuousOn_id.prodMk (Real.continuous_sqrt.comp_continuousOn hf)
  have hcdn : ContinuousOn dn (Set.Icc α β) :=
    continuousOn_id.prodMk ((Real.continuous_sqrt.comp_continuousOn hf).neg)
  have hIcc : IsConnected (Set.Icc α β) := isConnected_Icc hαβ
  have hUp : IsConnected (up '' Set.Icc α β) := hIcc.image _ hcup
  have hDn : IsConnected (dn '' Set.Icc α β) := hIcc.image _ hcdn
  have hunion : S = up '' Set.Icc α β ∪ dn '' Set.Icc α β := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      have hsq : Real.sqrt (f p.1) ^ 2 = f p.1 := Real.sq_sqrt (hnn p.1 h1)
      have : (p.2 - Real.sqrt (f p.1)) * (p.2 + Real.sqrt (f p.1)) = 0 := by
        have : p.2 ^ 2 - Real.sqrt (f p.1) ^ 2 = 0 := by rw [h2, hsq]; ring
        linear_combination this
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl ⟨p.1, h1, by rw [hup]; exact Prod.ext rfl (by linarith)⟩
      · exact Or.inr ⟨p.1, h1, by rw [hdn]; exact Prod.ext rfl (by linarith)⟩
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨ht, by rw [hup]; exact Real.sq_sqrt (hnn t ht)⟩
      · refine ⟨ht, ?_⟩
        show (-Real.sqrt (f t)) ^ 2 = f t
        rw [neg_sq]
        exact Real.sq_sqrt (hnn t ht)
  have hmem : (α, (0 : ℝ)) ∈ up '' Set.Icc α β ∩ dn '' Set.Icc α β := by
    refine ⟨⟨α, Set.left_mem_Icc.mpr hαβ, ?_⟩, ⟨α, Set.left_mem_Icc.mpr hαβ, ?_⟩⟩
    · show (α, Real.sqrt (f α)) = (α, (0 : ℝ))
      rw [hα, Real.sqrt_zero]
    · show (α, -Real.sqrt (f α)) = (α, (0 : ℝ))
      rw [hα, Real.sqrt_zero, neg_zero]
  rw [hunion]
  exact ⟨⟨(α, (0 : ℝ)), Or.inl hmem.1⟩,
    IsPreconnected.union (α, (0 : ℝ)) hmem.1 hmem.2 hUp.isPreconnected hDn.isPreconnected⟩

end GaloisForLFunctions.HTGeometry
