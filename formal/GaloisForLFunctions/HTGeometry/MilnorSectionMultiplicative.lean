import GaloisForLFunctions.HTGeometry.MilnorLiftAtPlace
import GaloisForLFunctions.HTGeometry.MilnorDegreeReduction

/-!
# Multiplicativity of Milnor's section, modulo the lower filtration

Milnor's section sends a residue class to the symbol `{lift ȳ, …, π}`.  It is multiplicative only up
to the lower stage of the filtration: if `u`, `v`, `w` all have degree below `deg π = d` and
`u·v ≡ w` modulo `π`, then

`{u, π} + {v, π} − {w, π}`

is a combination of symbols whose two distinguished entries both have degree below `d`.  The proof
is the sum-splitting identity applied to `w + π·h = u·v`, after which every leftover symbol has both
entries of degree below `d`.

* `lowTwoSlot` : two-slot classes with both entries of degree below `d`.
* `twoSlot_lift_mul` : **multiplicativity of the section modulo the lower stage.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- Two-slot classes with both entries of degree below `d`. -/
noncomputable def lowTwoSlot (d : ℕ) (l₁ l₂ : List (RatFunc F)ˣ)
    (hn : (l₁ ++ l₂).length + 2 = n) : AddSubgroup (MilnorKDeg (RatFunc F) n) :=
  AddSubgroup.closure {x | ∃ a b : (RatFunc F)ˣ, polyDegLt (F := F) d a ∧ polyDegLt (F := F) d b
    ∧ x = twoSlot l₁ l₂ hn a b}

theorem mem_lowTwoSlot {d : ℕ} {l₁ l₂ : List (RatFunc F)ˣ} {hn : (l₁ ++ l₂).length + 2 = n}
    {a b : (RatFunc F)ˣ} (ha : polyDegLt (F := F) d a) (hb : polyDegLt (F := F) d b) :
    twoSlot l₁ l₂ hn a b ∈ lowTwoSlot d l₁ l₂ hn :=
  AddSubgroup.subset_closure ⟨a, b, ha, hb, rfl⟩

/-- **Multiplicativity of the section modulo the lower stage of the filtration.** -/
theorem twoSlot_lift_mul {d : ℕ} (hd : 1 ≤ d) (l₁ l₂ : List (RatFunc F)ˣ)
    (hn : (l₁ ++ l₂).length + 2 = n) {π u v w : Polynomial F}
    (hπ : π ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hπd : π.natDegree = d) (hud : u.natDegree < d) (hvd : v.natDegree < d)
    (hwd : w.natDegree < d) (hdvd : π ∣ (u * v - w)) :
    twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
      + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
      - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ)
      ∈ lowTwoSlot (F := F) d l₁ l₂ hn := by
  classical
  obtain ⟨h, hh⟩ := hdvd
  have huv : u * v ≠ 0 := mul_ne_zero hu hv
  have hmulsplit : polyUnit huv = polyUnit hu * polyUnit hv := polyUnit_mul hu hv
  by_cases hz : h = 0
  · have heq : u * v = w := by
      rw [hz, mul_zero, sub_eq_zero] at hh
      exact hh
    have hunit : polyUnit hu * polyUnit hv = polyUnit hw := by
      rw [← hmulsplit]
      refine Units.ext ?_
      show algebraMap (Polynomial F) (RatFunc F) (u * v)
        = algebraMap (Polynomial F) (RatFunc F) w
      rw [heq]
    have hcollapse : twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
        + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
        = twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ) := by
      rw [← hunit, twoSlot_mul_left]
    rw [hcollapse, sub_self]
    exact AddSubgroup.zero_mem _
  · have hπh : π * h ≠ 0 := mul_ne_zero hπ hz
    have hhd : h.natDegree < d := by
      have hdeg1 : (π * h).natDegree = d + h.natDegree := by
        rw [natDegree_mul hπ hz, hπd]
      have hsub : u * v - w ≠ 0 := by
        rw [hh]; exact hπh
      have hdeg2 : (u * v - w).natDegree ≤ max (u * v).natDegree w.natDegree :=
        natDegree_sub_le _ _
      have hdeg3 : (u * v).natDegree = u.natDegree + v.natDegree := natDegree_mul hu hv
      have hdeg4 : (π * h).natDegree = (u * v - w).natDegree := by rw [hh]
      omega
    have hsum : ((polyUnit hw : (RatFunc F)ˣ) : RatFunc F)
        + ((polyUnit hπh : (RatFunc F)ˣ) : RatFunc F)
        = ((polyUnit huv : (RatFunc F)ˣ) : RatFunc F) := by
      show algebraMap (Polynomial F) (RatFunc F) w + algebraMap (Polynomial F) (RatFunc F) (π * h)
        = algebraMap (Polynomial F) (RatFunc F) (u * v)
      rw [← map_add]
      congr 1
      rw [← hh]
      ring
    have hsplit := twoSlot_add_split l₁ l₂ hn (polyUnit hw) (polyUnit hπh) (polyUnit huv) hsum
    have hπhsplit : polyUnit hπh = polyUnit hπ * polyUnit hz := polyUnit_mul hπ hz
    have hneg : (-1 : Polynomial F) ≠ 0 := by
      intro hcon
      exact one_ne_zero (neg_eq_zero.mp hcon)
    have hnegdeg : (-1 : Polynomial F).natDegree < d := by
      have hz0 : (-1 : Polynomial F).natDegree = 0 := by simp
      omega
    have hnegunit : (-1 : (RatFunc F)ˣ) = polyUnit hneg := (polyUnit_neg_one hneg).symm
    have e1 : twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπh)
        = twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ)
          + twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hz) := by
      rw [hπhsplit, twoSlot_mul_right]
    have e2 : twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit huv)
        = twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hu)
          + twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hv) := by
      rw [hmulsplit, twoSlot_mul_right]
    have e3 : twoSlot l₁ l₂ hn (polyUnit huv) (polyUnit hπh)
        = twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
          + twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hz)
          + (twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
            + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hz)) := by
      rw [hmulsplit, twoSlot_mul_left, hπhsplit, twoSlot_mul_right, twoSlot_mul_right]
    have e4 : twoSlot l₁ l₂ hn (polyUnit huv) (polyUnit huv)
        = twoSlot l₁ l₂ hn (polyUnit hu) (-1) + twoSlot l₁ l₂ hn (polyUnit hv) (-1) := by
      rw [twoSlot_self, hmulsplit, twoSlot_mul_left]
    rw [e1, e2, e3, e4] at hsplit
    have hgoal : twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
        + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
        - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ)
        = twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hz)
          - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hu)
          - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hv)
          - twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hz)
          - twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hz)
          + twoSlot l₁ l₂ hn (polyUnit hu) (-1)
          + twoSlot l₁ l₂ hn (polyUnit hv) (-1) := by
      refine sub_eq_zero.mp ?_
      have habel : (twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
            + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
            - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ))
          - (twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hz)
            - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hu)
            - twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hv)
            - twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hz)
            - twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hz)
            + twoSlot l₁ l₂ hn (polyUnit hu) (-1)
            + twoSlot l₁ l₂ hn (polyUnit hv) (-1))
          = (twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hu)
              + twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hv)
              + (twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hπ)
                + twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit hz)
                + (twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hπ)
                  + twoSlot l₁ l₂ hn (polyUnit hv) (polyUnit hz)))
              - (twoSlot l₁ l₂ hn (polyUnit hu) (-1)
                + twoSlot l₁ l₂ hn (polyUnit hv) (-1)))
            - (twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hπ)
              + twoSlot l₁ l₂ hn (polyUnit hw) (polyUnit hz)) := by abel
      rw [habel, ← hsplit, sub_self]
    rw [hgoal, hnegunit]
    refine AddSubgroup.add_mem _ (AddSubgroup.add_mem _ ?_ ?_) ?_
    · refine AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _
        (AddSubgroup.sub_mem _ ?_ ?_) ?_) ?_) ?_
      · exact mem_lowTwoSlot ⟨w, hw, hwd, rfl⟩ ⟨h, hz, hhd, rfl⟩
      · exact mem_lowTwoSlot ⟨w, hw, hwd, rfl⟩ ⟨u, hu, hud, rfl⟩
      · exact mem_lowTwoSlot ⟨w, hw, hwd, rfl⟩ ⟨v, hv, hvd, rfl⟩
      · exact mem_lowTwoSlot ⟨u, hu, hud, rfl⟩ ⟨h, hz, hhd, rfl⟩
      · exact mem_lowTwoSlot ⟨v, hv, hvd, rfl⟩ ⟨h, hz, hhd, rfl⟩
    · exact mem_lowTwoSlot ⟨u, hu, hud, rfl⟩ ⟨(-1 : Polynomial F), hneg, hnegdeg, rfl⟩
    · exact mem_lowTwoSlot ⟨v, hv, hvd, rfl⟩ ⟨(-1 : Polynomial F), hneg, hnegdeg, rfl⟩

/-- **Two lifts below the degree of the place whose sum is `1` modulo `π` sum to `1` exactly.**
There is no room for a correction term: `u + t − 1` has degree below `deg π` and is divisible by
`π`. -/
theorem add_eq_one_of_dvd {π u t : Polynomial F} (hud : u.natDegree < π.natDegree)
    (htd : t.natDegree < π.natDegree) (hdvd : π ∣ (u + t - 1)) : u + t = 1 := by
  by_contra hne
  have hsub : u + t - 1 ≠ 0 := sub_ne_zero.2 hne
  have hge : π.natDegree ≤ (u + t - 1).natDegree := natDegree_le_of_dvd hdvd hsub
  have hlt : (u + t - 1).natDegree < π.natDegree := by
    calc (u + t - 1).natDegree ≤ max (u + t).natDegree (1 : Polynomial F).natDegree :=
          natDegree_sub_le _ _
      _ = (u + t).natDegree := by simp
      _ ≤ max u.natDegree t.natDegree := natDegree_add_le _ _
      _ < π.natDegree := max_lt hud htd
  omega

/-- **The Steinberg relation for Milnor's section.**  Lifts of `ȳ` and `1 − ȳ` below the degree of
the place sum to `1` on the nose, so their symbol vanishes. -/
theorem twoSlot_lift_steinberg (l₁ l₂ : List (RatFunc F)ˣ)
    (hn : (l₁ ++ l₂).length + 2 = n) {π u t : Polynomial F} (hu : u ≠ 0) (ht : t ≠ 0)
    (hud : u.natDegree < π.natDegree) (htd : t.natDegree < π.natDegree)
    (hdvd : π ∣ (u + t - 1)) :
    twoSlot l₁ l₂ hn (polyUnit hu) (polyUnit ht) = 0 := by
  have hsum : u + t = 1 := add_eq_one_of_dvd hud htd hdvd
  have hune : ((polyUnit hu : (RatFunc F)ˣ) : RatFunc F) ≠ 1 := by
    intro hcon
    have huval : algebraMap (Polynomial F) (RatFunc F) u = 1 := hcon
    have hu1 : u = 1 := by
      have := huval
      rw [show (1 : RatFunc F) = algebraMap (Polynomial F) (RatFunc F) 1 by rw [map_one]] at this
      exact IsFractionRing.injective (Polynomial F) (RatFunc F) this
    apply ht
    rw [hu1] at hsum
    have hzero : (1 : Polynomial F) + t = 1 + 0 := by
      rw [add_zero]
      exact hsum
    exact add_left_cancel hzero
  have hone : polyUnit ht = oneSubUnit hune := by
    refine Units.ext ?_
    rw [oneSubUnit_val]
    show algebraMap (Polynomial F) (RatFunc F) t = 1 - algebraMap (Polynomial F) (RatFunc F) u
    rw [eq_sub_iff_add_eq, ← map_add, add_comm, hsum, map_one]
  rw [hone]
  exact twoSlot_steinberg l₁ l₂ hn hune

/-- Two-slot classes with both entries of degree below `d`, surrounded by entries of degree below
`d`, lie in the previous stage of the filtration. -/
theorem lowTwoSlot_le_degreeFiltration {d : ℕ} (l₁ l₂ : List (RatFunc F)ˣ)
    (hn : (l₁ ++ l₂).length + 2 = n)
    (hl₁ : ∀ a ∈ l₁, polyDegLt (F := F) d a) (hl₂ : ∀ a ∈ l₂, polyDegLt (F := F) d a) :
    lowTwoSlot (F := F) d l₁ l₂ hn ≤ degreeFiltration (F := F) (d - 1) n := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro x ⟨a, b, ha, hb, rfl⟩
  refine AddSubgroup.subset_closure ⟨⟨l₁ ++ a :: b :: l₂, length_two_slot l₁ l₂ a b hn⟩, ?_, rfl⟩
  intro c hc
  have hshift : ∀ {u : (RatFunc F)ˣ}, polyDegLt (F := F) d u →
      ∃ (p : Polynomial F) (hp : p ≠ 0), p.natDegree ≤ d - 1 ∧ u = polyUnit hp := by
    rintro u ⟨p, hp, hlt, hu⟩
    exact ⟨p, hp, by omega, hu⟩
  rcases List.mem_append.1 hc with h1 | h2
  · exact hshift (hl₁ c h1)
  · rcases List.mem_cons.1 h2 with rfl | h3
    · exact hshift ha
    · rcases List.mem_cons.1 h3 with rfl | h4
      · exact hshift hb
      · exact hshift (hl₂ c h4)

end GaloisForLFunctions.HTGeometry
