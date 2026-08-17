import Mathlib

/-!
# Zero configurations with multiplicity, and the Rolle descent

A zero configuration of a smooth real function is recorded as a **sorted list with repetition**:
`l` is a zero list of `f` when `l` is sorted and `f` vanishes at each point to at least the order
with which that point is repeated.  The total order of the configuration is `l.length`.

The single structural fact about such configurations is the **Rolle descent**: from a zero list of
length `n + 1` for `f` one obtains a zero list of length `n` for `deriv f`, by taking one point from
each adjacent pair — the repeated point itself when the pair is equal (one order of vanishing is
consumed by differentiation) and a Rolle point strictly between when the pair is distinct.  Because
the extracted point always lies between the two members of its pair, the new list is automatically
sorted; and because a Rolle point is strictly larger than the left member of its pair, it never
collides with the tail, so the multiplicity bookkeeping closes.

This is the counting engine behind Descartes/Laguerre-type bounds for real analytic functions, for
which mathlib has no zero-counting-with-multiplicity.
-/

open List

namespace GaloisForLFunctions.HTGeometry

/-- `f` vanishes to order at least `n` at `x`. -/
def VanishesTo (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : Prop := ∀ j < n, iteratedDeriv j f x = 0

theorem vanishesTo_zero (f : ℝ → ℝ) (x : ℝ) : VanishesTo f 0 x := by
  intro j hj
  omega

theorem vanishesTo_mono {f : ℝ → ℝ} {m n : ℕ} {x : ℝ} (h : m ≤ n) (hv : VanishesTo f n x) :
    VanishesTo f m x := fun j hj => hv j (lt_of_lt_of_le hj h)

theorem apply_eq_zero_of_vanishesTo {f : ℝ → ℝ} {n : ℕ} {x : ℝ} (hn : 1 ≤ n)
    (hv : VanishesTo f n x) : f x = 0 := by
  have := hv 0 (by omega)
  rwa [iteratedDeriv_zero] at this

/-- A sorted list of zeros of `f`, with repetition recording multiplicity. -/
def IsZeroList (f : ℝ → ℝ) (l : List ℝ) : Prop :=
  l.Pairwise (· ≤ ·) ∧ ∀ x : ℝ, VanishesTo f (l.count x) x

theorem isZeroList_nil (f : ℝ → ℝ) : IsZeroList f [] :=
  ⟨List.pairwise_nil, fun x => by simpa using vanishesTo_zero f x⟩

theorem isZeroList_of_cons {f : ℝ → ℝ} {a : ℝ} {t : List ℝ} (h : IsZeroList f (a :: t)) :
    IsZeroList f t := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨(List.pairwise_cons.mp hs).2, fun x => ?_⟩
  refine vanishesTo_mono ?_ (hv x)
  rw [List.count_cons]
  omega

/-- **The Rolle descent.**  A zero list `a :: t` of `f` yields a zero list of `deriv f` of length
`t.length`, all of whose entries are at least `a`, and which uses each point of `a :: t` at least one
fewer time. -/
theorem exists_zeroList_deriv {f : ℝ → ℝ} (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) :
    ∀ (t : List ℝ) (a : ℝ), IsZeroList f (a :: t) →
      ∃ l' : List ℝ, IsZeroList (deriv f) l' ∧ l'.length = t.length ∧
        (∀ y ∈ l', a ≤ y) ∧ (∀ x : ℝ, 1 ≤ (a :: t).count x → l'.count x + 1 ≤ (a :: t).count x) := by
  have hcont : Continuous f := by
    have := hf 0
    rwa [iteratedDeriv_zero] at this
  intro t
  induction t with
  | nil =>
    intro a _
    refine ⟨[], isZeroList_nil _, rfl, by simp, ?_⟩
    intro x hx
    simp only [List.count_nil, zero_add]
    simpa using hx
  | cons b u ih =>
    intro a hl
    obtain ⟨hsorted, hvan⟩ := hl
    have hab : a ≤ b := (List.pairwise_cons.mp hsorted).1 b (by simp)
    have hbu : IsZeroList f (b :: u) := isZeroList_of_cons ⟨hsorted, hvan⟩
    obtain ⟨l'', h'' , hlen'', hge'', hcnt''⟩ := ih b hbu
    -- the count of `a` in the full list is at least one
    have hca : 1 ≤ (a :: b :: u).count a := by
      rw [List.count_cons]
      simp
    rcases eq_or_lt_of_le hab with hEq | hLt
    · -- equal pair: one order of vanishing is consumed by differentiating at `a`
      refine ⟨a :: l'', ⟨?_, ?_⟩, by simp [hlen''], ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨fun y hy => ?_, h''.1⟩
        exact hEq ▸ hge'' y hy
      · intro x
        rw [List.count_cons]
        by_cases hx : x = a
        · subst hx
          intro j hj
          simp only [if_pos rfl] at hj ⊢
          have hj' : j + 1 < (x :: b :: u).count x := by
            have hb : (b :: u).count x = 1 + u.count x := by
              rw [List.count_cons, ← hEq]
              simp [add_comm]
            have hcx : l''.count x + 1 ≤ (b :: u).count x := by
              refine hcnt'' x ?_
              rw [hb]
              omega
            rw [List.count_cons]
            simp only [if_pos rfl]
            omega
          have := hvan x (j + 1) (by simpa using hj')
          rw [iteratedDeriv_succ'] at this
          simpa using this
        · simp only [if_neg hx, add_zero]
          exact h''.2 x
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · exact le_of_eq h.symm
        · exact hEq ▸ hge'' y h
      · intro x hx
        rw [List.count_cons, List.count_cons]
        by_cases hxa : x = a
        · subst hxa
          have hb : (b :: u).count x = 1 + u.count x := by
            rw [List.count_cons, ← hEq]
            simp [add_comm]
          have hcx : l''.count x + 1 ≤ (b :: u).count x := by
            refine hcnt'' x ?_
            rw [hb]
            omega
          rw [hb] at hcx
          rw [List.count_cons, ← hEq]
          simp only [if_pos rfl]
          omega
        · simp only [if_neg hxa, add_zero]
          rw [List.count_cons, if_neg hxa, add_zero] at hx
          have := hcnt'' x hx
          omega
    · -- distinct pair: Rolle supplies an interior point, which cannot collide with the tail
      have hfa : f a = 0 := apply_eq_zero_of_vanishesTo hca (hvan a)
      have hcb : 1 ≤ (a :: b :: u).count b := by
        rw [List.count_cons, List.count_cons]
        simp only [if_pos rfl]
        omega
      have hfb : f b = 0 := apply_eq_zero_of_vanishesTo hcb (hvan b)
      obtain ⟨p, hp, hdp⟩ := exists_deriv_eq_zero hLt hcont.continuousOn (by rw [hfa, hfb])
      have hpb : p < b := hp.2
      have hpnot : p ∉ l'' := fun hmem => absurd (hge'' p hmem) (not_le.mpr hpb)
      have hpcount : l''.count p = 0 := List.count_eq_zero.mpr hpnot
      refine ⟨p :: l'', ⟨?_, ?_⟩, by simp [hlen''], ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨fun y hy => le_trans hpb.le (hge'' y hy), h''.1⟩
      · intro x
        rw [List.count_cons]
        by_cases hx : x = p
        · subst hx
          simp only [hpcount, zero_add]
          intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          rw [iteratedDeriv_zero]
          exact hdp
        · simp only [if_neg hx, add_zero]
          exact h''.2 x
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · exact h ▸ hp.1.le
        · exact le_trans hab (hge'' y h)
      · intro x hx
        rw [List.count_cons]
        by_cases hxp : x = p
        · subst hxp
          simp only [hpcount, zero_add]
          rw [List.count_cons, List.count_cons] at hx ⊢
          have hxa : x ≠ a := fun h => absurd (h ▸ hp.1) (lt_irrefl a)
          have hxb : x ≠ b := fun h => absurd (h ▸ hpb) (lt_irrefl b)
          simp only [if_neg hxa, if_neg hxb, add_zero] at hx ⊢
          have : (0 : ℕ) < u.count x := hx
          omega
        · simp only [if_neg hxp, add_zero]
          rw [List.count_cons] at hx ⊢
          by_cases hxa : x = a
          · subst hxa
            have hxb : x ≠ b := fun h => absurd (h ▸ hLt) (lt_irrefl x)
            have : l''.count x = 0 := by
              refine List.count_eq_zero.mpr fun hmem => ?_
              have := hge'' x hmem
              rw [List.sorted_cons] at h''
              exact absurd (le_trans hpb.le (hge'' x hmem)) (not_le.mpr (hp.1))
            omega
          · simp only [if_neg hxa, add_zero] at hx ⊢
            exact hcnt'' x hx

end GaloisForLFunctions.HTGeometry
