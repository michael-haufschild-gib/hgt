import Mathlib

/-!
# Zero configurations with multiplicity, and the Rolle descent

A zero configuration of a smooth real function is recorded as a **sorted list with repetition**:
`l` is a zero list of `f` when `l` is sorted and `f` vanishes at each point to at least the order
with which that point is repeated.  The total order of the configuration is `l.length`.

The structural fact about such configurations is the **Rolle descent**: from a zero list of length
`n + 1` for `f` one obtains a zero list of length `n` for `deriv f`, by taking one point from each
adjacent pair — the repeated point itself when the pair is equal (one order of vanishing is consumed
by differentiating) and a Rolle point strictly between when the pair is distinct.  The extracted
point always lies between the two members of its pair, so the new list is automatically sorted; and
a Rolle point is strictly below the whole tail, so it never collides with it and the multiplicity
bookkeeping closes.

This is the counting engine behind Descartes/Laguerre-type bounds for real analytic functions, for
which mathlib has no zero-counting-with-multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Counting helpers -/

theorem count_cons_self (a : ℝ) (l : List ℝ) : (a :: l).count a = l.count a + 1 := by
  simp

theorem count_cons_of_ne {a b : ℝ} (h : b ≠ a) (l : List ℝ) :
    (a :: l).count b = l.count b := by
  rw [List.count_cons]
  simp [Ne.symm h]

theorem count_le_count_cons (a b : ℝ) (l : List ℝ) : l.count b ≤ (a :: l).count b := by
  by_cases h : b = a
  · subst h
    rw [count_cons_self]
    omega
  · rw [count_cons_of_ne h]

/-! ## Vanishing to a given order -/

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

/-- Differentiating consumes one order of vanishing. -/
theorem vanishesTo_deriv {f : ℝ → ℝ} {n : ℕ} {x : ℝ} (hv : VanishesTo f (n + 1) x) :
    VanishesTo (deriv f) n x := by
  intro j hj
  have := hv (j + 1) (by omega)
  rwa [iteratedDeriv_succ'] at this

/-! ## Zero lists -/

/-- A sorted list of zeros of `f`, with repetition recording multiplicity. -/
def IsZeroList (f : ℝ → ℝ) (l : List ℝ) : Prop :=
  l.Pairwise (· ≤ ·) ∧ ∀ x : ℝ, VanishesTo f (l.count x) x

theorem isZeroList_nil (f : ℝ → ℝ) : IsZeroList f [] :=
  ⟨by simp, fun x => by simpa using vanishesTo_zero f x⟩

theorem isZeroList_of_cons {f : ℝ → ℝ} {a : ℝ} {t : List ℝ} (h : IsZeroList f (a :: t)) :
    IsZeroList f t := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨(List.pairwise_cons.mp hs).2, fun x => ?_⟩
  exact vanishesTo_mono (count_le_count_cons a x t) (hv x)

/-- **The Rolle descent.**  A zero list `a :: t` of `f` yields a zero list of `deriv f` of length
`t.length`, all of whose entries are at least `a`, and which uses each point of `a :: t` at least one
fewer time. -/
theorem exists_zeroList_deriv {f : ℝ → ℝ} (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) :
    ∀ (t : List ℝ) (a : ℝ), IsZeroList f (a :: t) →
      ∃ l' : List ℝ, IsZeroList (deriv f) l' ∧ l'.length = t.length ∧
        (∀ y ∈ l', a ≤ y) ∧
        (∀ x : ℝ, 1 ≤ (a :: t).count x → l'.count x + 1 ≤ (a :: t).count x) := by
  have hcont : Continuous f := by
    have := hf 0
    rwa [iteratedDeriv_zero] at this
  intro t
  induction t with
  | nil =>
    intro a _
    refine ⟨[], isZeroList_nil _, rfl, by simp, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      rw [count_cons_self]
    · rw [count_cons_of_ne hxa] at hx
      simp at hx
  | cons b u ih =>
    intro a hl
    obtain ⟨hsorted, hvan⟩ := hl
    have hab : a ≤ b := (List.pairwise_cons.mp hsorted).1 b (by simp)
    have hbu : IsZeroList f (b :: u) := isZeroList_of_cons ⟨hsorted, hvan⟩
    obtain ⟨l'', h'', hlen'', hge'', hcnt''⟩ := ih b hbu
    have hcb : 1 ≤ (b :: u).count b := by
      rw [count_cons_self]
      omega
    rcases eq_or_lt_of_le hab with hEq | hLt
    · -- equal pair: differentiating consumes one order at `a`
      subst hEq
      have hkey : l''.count a + 1 ≤ (a :: u).count a := hcnt'' a hcb
      have dA : (a :: u).count a = u.count a + 1 := count_cons_self a u
      have cA : (a :: a :: u).count a = u.count a + 2 := by
        rw [count_cons_self, count_cons_self]
      have cX : ∀ x : ℝ, x ≠ a → (a :: a :: u).count x = u.count x := by
        intro x hx
        rw [count_cons_of_ne hx, count_cons_of_ne hx]
      have hle : l''.count a ≤ u.count a := by omega
      refine ⟨a :: l'', ⟨?_, ?_⟩, by simp [hlen''], ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun y hy => hge'' y hy, h''.1⟩
      · intro x
        by_cases hx : x = a
        · subst hx
          rw [count_cons_self]
          refine vanishesTo_deriv (vanishesTo_mono ?_ (hvan x))
          omega
        · rw [count_cons_of_ne hx]
          exact h''.2 x
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · exact le_of_eq h.symm
        · exact hge'' y h
      · intro x hx
        by_cases hxa : x = a
        · subst hxa
          rw [count_cons_self]
          omega
        · rw [count_cons_of_ne hxa, cX x hxa]
          rw [cX x hxa] at hx
          have := hcnt'' x (by rw [count_cons_of_ne hxa]; exact hx)
          rw [count_cons_of_ne hxa] at this
          exact this
    · -- distinct pair: Rolle supplies an interior point below the whole tail
      have hca : 1 ≤ (a :: b :: u).count a := by
        rw [count_cons_self]
        omega
      have hfa : f a = 0 := apply_eq_zero_of_vanishesTo hca (hvan a)
      have hcb' : 1 ≤ (a :: b :: u).count b :=
        le_trans hcb (count_le_count_cons a b (b :: u))
      have hfb : f b = 0 := apply_eq_zero_of_vanishesTo hcb' (hvan b)
      obtain ⟨p, hp, hdp⟩ := exists_deriv_eq_zero hLt hcont.continuousOn (by rw [hfa, hfb])
      have hpb : p < b := hp.2
      have hap : a < p := hp.1
      have hpnot : p ∉ l'' := fun hmem => absurd (hge'' p hmem) (not_le.mpr hpb)
      have hpcount : l''.count p = 0 := List.count_eq_zero.mpr hpnot
      refine ⟨p :: l'', ⟨?_, ?_⟩, by simp [hlen''], ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun y hy => le_trans hpb.le (hge'' y hy), h''.1⟩
      · intro x
        by_cases hx : x = p
        · subst hx
          rw [count_cons_self, hpcount]
          intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          rw [iteratedDeriv_zero]
          exact hdp
        · rw [count_cons_of_ne hx]
          exact h''.2 x
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · exact h ▸ hap.le
        · exact le_trans hab (hge'' y h)
      · intro x hx
        have cA : (a :: b :: u).count a = (b :: u).count a + 1 := count_cons_self a (b :: u)
        by_cases hxp : x = p
        · subst hxp
          have hxa : x ≠ a := ne_of_gt hap
          have hxb : x ≠ b := ne_of_lt hpb
          have hub : ∀ y ∈ u, b ≤ y :=
            (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1
          have hxu : u.count x = 0 :=
            List.count_eq_zero.mpr fun hmem => absurd (hub x hmem) (not_le.mpr hpb)
          rw [count_cons_of_ne hxa, count_cons_of_ne hxb, hxu] at hx
          omega
        · rw [count_cons_of_ne hxp]
          by_cases hxa : x = a
          · subst hxa
            have hz0 : l''.count x = 0 :=
              List.count_eq_zero.mpr fun hmem => absurd (hge'' x hmem) (not_le.mpr hLt)
            rw [count_cons_self]
            omega
          · rw [count_cons_of_ne hxa] at hx ⊢
            exact hcnt'' x hx

/-! ## Iterating the descent -/

theorem continuous_iteratedDeriv_deriv {f : ℝ → ℝ}
    (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) :
    ∀ j : ℕ, Continuous (iteratedDeriv j (deriv f)) := by
  intro j
  have h : iteratedDeriv j (deriv f) = iteratedDeriv (j + 1) f := (iteratedDeriv_succ' ..).symm
  rw [h]
  exact hf (j + 1)

theorem continuous_iteratedDeriv_iterate {f : ℝ → ℝ}
    (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) :
    ∀ k j : ℕ, Continuous (iteratedDeriv j (iteratedDeriv k f)) := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ n ih =>
    intro j
    have h : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := iteratedDeriv_succ ..
    rw [h]
    exact continuous_iteratedDeriv_deriv ih j

theorem isZeroList_take {f : ℝ → ℝ} {l : List ℝ} (h : IsZeroList f l) (m : ℕ) :
    IsZeroList f (l.take m) := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨hs.sublist (List.take_sublist m l), fun x => ?_⟩
  exact vanishesTo_mono ((List.take_sublist m l).count_le x) (hv x)

/-- Iterating the Rolle descent: a zero configuration of total order `n + k` for `f` yields one of
total order `n` for the `k`-th derivative. -/
theorem exists_zeroList_iteratedDeriv {f : ℝ → ℝ}
    (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) :
    ∀ (k : ℕ) (l : List ℝ), IsZeroList f l → k ≤ l.length →
      ∃ l' : List ℝ, IsZeroList (iteratedDeriv k f) l' ∧ l'.length + k = l.length := by
  intro k
  induction k with
  | zero =>
    intro l hl _
    exact ⟨l, by simpa using hl, by simp⟩
  | succ n ih =>
    intro l hl hle
    obtain ⟨l', hl', hlen'⟩ := ih l hl (by omega)
    have hpos : 0 < l'.length := by omega
    obtain ⟨a, t, rfl⟩ : ∃ a t, l' = a :: t := by
      cases l' with
      | nil => simp at hpos
      | cons a t => exact ⟨a, t, rfl⟩
    obtain ⟨l'', h'', hlen'', _, _⟩ :=
      exists_zeroList_deriv (continuous_iteratedDeriv_iterate hf n) t a hl'
    refine ⟨l'', ?_, ?_⟩
    · have h : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := iteratedDeriv_succ ..
      rw [h]
      exact h''
    · simp only [List.length_cons] at hlen'
      omega

/-- **The counting theorem.**  If the `N`-th derivative of `f` never vanishes, then every zero
configuration of `f` has total order at most `N`. -/
theorem zeroList_length_le {f : ℝ → ℝ} (hf : ∀ j : ℕ, Continuous (iteratedDeriv j f)) {N : ℕ}
    (hN : ∀ x : ℝ, iteratedDeriv N f x ≠ 0) {l : List ℝ} (hl : IsZeroList f l) :
    l.length ≤ N := by
  by_contra hcon
  push Not at hcon
  have hlen : (l.take (N + 1)).length = N + 1 := by
    rw [List.length_take]
    omega
  obtain ⟨l', hl', hlen'⟩ :=
    exists_zeroList_iteratedDeriv hf N (l.take (N + 1)) (isZeroList_take hl (N + 1)) (by omega)
  have h1 : l'.length = 1 := by omega
  obtain ⟨x, rfl⟩ : ∃ x, l' = [x] := by
    match l', h1 with
    | [x], _ => exact ⟨x, rfl⟩
  have hx : iteratedDeriv N f x = 0 := by
    have := hl'.2 x
    refine apply_eq_zero_of_vanishesTo ?_ this
    simp
  exact hN x hx

end GaloisForLFunctions.HTGeometry
