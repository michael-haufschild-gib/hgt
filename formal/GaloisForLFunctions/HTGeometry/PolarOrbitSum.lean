import GaloisForLFunctions.HTGeometry.PolarParts
import Mathlib

/-!
# Orbit sums of polar data

The unit shift moves the pole at `a` to the pole at `a - 1`, so it acts on polar data by
translating the pole coordinate.  The invariants of that action are the *orbit sums*: for a shift
orbit `a + Z` and a pole order `j + 1`, the sum of the corresponding coefficients over the orbit.

Orbit sums annihilate every shift defect, and conversely a polar datum all of whose orbit sums
vanish is a shift defect.  Together with the derivative rule
`orbSum (deriv c) a (j+1) = -(j+1) * d * orbSum c a j` this makes the cokernel of the shift a
torsion-free module over the ring of constant-coefficient differential operators.
-/

open Polynomial
open scoped Classical

namespace HTGeometry

/-! ## The shift on polar data -/

/-- Translating the pole coordinate down by one. -/
noncomputable def polarShift (c : (ℂ × ℕ) →₀ ℂ) : (ℂ × ℕ) →₀ ℂ :=
  Finsupp.equivMapDomain ((Equiv.subRight (1 : ℂ)).prodCongr (Equiv.refl ℕ)) c

@[simp] theorem polarShift_apply (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) (j : ℕ) :
    polarShift c (β, j) = c (β + 1, j) := by
  simp [polarShift, Finsupp.equivMapDomain_apply, Equiv.prodCongr, Equiv.subRight]

theorem polarShift_add (c d : (ℂ × ℕ) →₀ ℂ) :
    polarShift (c + d) = polarShift c + polarShift d := by
  ext p
  obtain ⟨β, j⟩ := p
  simp

/-- The defect of a polar datum under the shift. -/
noncomputable def polarDefect (c : (ℂ × ℕ) →₀ ℂ) : (ℂ × ℕ) →₀ ℂ := polarShift c - c

@[simp] theorem polarShift_zero : polarShift (0 : (ℂ × ℕ) →₀ ℂ) = 0 := by
  ext p
  obtain ⟨β, j⟩ := p
  simp

@[simp] theorem polarDefect_apply (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) (j : ℕ) :
    polarDefect c (β, j) = c (β + 1, j) - c (β, j) := by
  simp [polarDefect]

/-! ## Orbit sums -/

/-- Membership in the shift orbit of `alpha`. -/
def inOrbit (α β : ℂ) : Prop := ∃ k : ℤ, β = α + (k : ℂ)

theorem inOrbit_refl (α : ℂ) : inOrbit α α := ⟨0, by simp⟩

theorem inOrbit_succ {α β : ℂ} (h : inOrbit α β) : inOrbit α (β + 1) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by push_cast; ring⟩

theorem inOrbit_pred {α β : ℂ} (h : inOrbit α (β + 1)) : inOrbit α β := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k - 1, ?_⟩
  push_cast
  linear_combination hk

/-- The sum of the order-`j+1` coefficients of `c` over the shift orbit of `alpha`. -/
noncomputable def orbSum (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) : ℂ :=
  ∑ p ∈ c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1), c p

theorem orbSum_eq_sum_over {c : (ℂ × ℕ) →₀ ℂ} {α : ℂ} {j : ℕ}
    {s : Finset (ℂ × ℕ)} (hs : c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1) ⊆ s)
    (hs' : ∀ p ∈ s, p.2 = j ∧ inOrbit α p.1) :
    orbSum c α j = ∑ p ∈ s, c p := by
  rw [orbSum]
  refine Finset.sum_subset hs fun p hp hnp => ?_
  obtain ⟨h2, h1⟩ := hs' p hp
  by_contra hne
  exact hnp (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, h2, h1⟩)

theorem orbSum_zero (α : ℂ) (j : ℕ) : orbSum 0 α j = 0 := by
  simp [orbSum]

theorem orbSum_add (c d : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (c + d) α j = orbSum c α j + orbSum d α j := by
  set s : Finset (ℂ × ℕ) :=
    ((c.support ∪ d.support).filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1)) with hs
  have hsub : ∀ e : (ℂ × ℕ) →₀ ℂ, e.support ⊆ c.support ∪ d.support →
      orbSum e α j = ∑ p ∈ s, e p := by
    intro e he
    refine orbSum_eq_sum_over ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨he hp1, hp2⟩
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  rw [hsub (c + d) Finsupp.support_add,
    hsub c Finset.subset_union_left, hsub d Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp

theorem orbSum_neg (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (-c) α j = -orbSum c α j := by
  have h := orbSum_add c (-c) α j
  rw [add_neg_cancel, orbSum_zero] at h
  linear_combination -h

theorem orbSum_sub (c d : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (c - d) α j = orbSum c α j - orbSum d α j := by
  rw [sub_eq_add_neg, orbSum_add, orbSum_neg, sub_eq_add_neg]

/-- **Orbit sums are shift invariants.** -/
theorem orbSum_polarShift (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (polarShift c) α j = orbSum c α j := by
  set e : (ℂ × ℕ) ≃ (ℂ × ℕ) := (Equiv.subRight (1 : ℂ)).prodCongr (Equiv.refl ℕ) with he
  have hsupp : (polarShift c).support = c.support.image e := by
    rw [polarShift, Finsupp.equivMapDomain_eq_mapDomain]
    exact Finsupp.mapDomain_support_of_injective e.injective c
  rw [orbSum, orbSum, hsupp]
  rw [Finset.filter_image]
  rw [Finset.sum_image (fun p _ q _ h => e.injective h)]
  refine Finset.sum_congr ?_ ?_
  · refine Finset.filter_congr fun p hp => ?_
    constructor
    · rintro ⟨h2, h1⟩
      refine ⟨h2, ?_⟩
      have : (e p).1 = p.1 - 1 := rfl
      rw [this] at h1
      have := inOrbit_succ h1
      simpa using this
    · rintro ⟨h2, h1⟩
      refine ⟨h2, ?_⟩
      have hfst : (e p).1 = p.1 - 1 := rfl
      rw [hfst]
      refine inOrbit_pred ?_
      simpa using h1
  · intro p _
    show polarShift c (e p) = c p
    obtain ⟨β, k⟩ := p
    show polarShift c (β - 1, k) = c (β, k)
    rw [polarShift_apply, show β - 1 + 1 = β from by ring]

/-- **Every shift defect has vanishing orbit sums.** -/
theorem orbSum_polarDefect (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (polarDefect c) α j = 0 := by
  rw [polarDefect, orbSum_sub, orbSum_polarShift, sub_self]


theorem polarDefect_add (c d : (ℂ × ℕ) →₀ ℂ) :
    polarDefect (c + d) = polarDefect c + polarDefect d := by
  ext p
  obtain ⟨β, j⟩ := p
  simp only [polarDefect_apply, Finsupp.add_apply]
  ring

theorem polarDefect_neg (c : (ℂ × ℕ) →₀ ℂ) : polarDefect (-c) = -polarDefect c := by
  ext p
  obtain ⟨β, j⟩ := p
  simp only [polarDefect_apply, Finsupp.neg_apply]
  ring

/-- One elementary telescoping step. -/
theorem polarDefect_single_step (β : ℂ) (j : ℕ) (t : ℂ) :
    polarDefect (Finsupp.single (β + 1, j) t)
      = Finsupp.single (β, j) t - Finsupp.single (β + 1, j) t := by
  ext p
  obtain ⟨γ, i⟩ := p
  simp only [polarDefect_apply, Finsupp.sub_apply, Finsupp.single_apply, Prod.mk.injEq]
  have h1 : ((β + 1 = γ + 1) ∧ j = i) ↔ ((β = γ) ∧ j = i) := by
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨by linear_combination ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨by rw [ha], hb⟩
  simp only [h1]

/-- Any two points of a shift orbit differ by a defect. -/
theorem exists_polarDefect_single_sub (j : ℕ) :
    ∀ (k : ℤ) (β t : ℂ), ∃ w : (ℂ × ℕ) →₀ ℂ,
      polarDefect w = Finsupp.single (β, j) t - Finsupp.single (β + (k : ℂ), j) t := by
  intro k
  induction k using Int.induction_on with
  | zero => intro β t; exact ⟨0, by simp [polarDefect]⟩
  | succ n ih =>
      intro β t
      obtain ⟨w, hw⟩ := ih β t
      refine ⟨w + Finsupp.single ((β + ((n : ℤ) : ℂ)) + 1, j) t, ?_⟩
      rw [polarDefect_add, hw, polarDefect_single_step]
      rw [show β + (((n : ℤ) + 1 : ℤ) : ℂ) = (β + ((n : ℤ) : ℂ)) + 1 from by push_cast; ring]
      abel
  | pred n ih =>
      intro β t
      obtain ⟨w, hw⟩ := ih β t
      refine ⟨w + -Finsupp.single ((β + ((-(n : ℤ) - 1 : ℤ) : ℂ)) + 1, j) t, ?_⟩
      rw [polarDefect_add, hw, polarDefect_neg, polarDefect_single_step]
      rw [show (β + ((-(n : ℤ) - 1 : ℤ) : ℂ)) + 1 = β + ((-(n : ℤ) : ℤ) : ℂ) from by
        push_cast; ring]
      abel

/-- **A polar datum with vanishing orbit sums is a shift defect.** -/
theorem exists_polarDefect_of_orbSum_eq_zero :
    ∀ (n : ℕ) (c : (ℂ × ℕ) →₀ ℂ), c.support.card ≤ n →
      (∀ α j, orbSum c α j = 0) → ∃ w, polarDefect w = c := by
  intro n
  induction n with
  | zero =>
      intro c hcard _
      have hc : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact ⟨0, by rw [hc]; simp [polarDefect]⟩
  | succ n ih =>
      intro c hcard horb
      rcases eq_or_ne c 0 with rfl | hc0
      · exact ⟨0, by simp [polarDefect]⟩
      obtain ⟨q, hq⟩ := Finsupp.support_nonempty_iff.mpr hc0
      obtain ⟨β, j⟩ := q
      set t : ℂ := c (β, j) with ht
      have htne : t ≠ 0 := Finsupp.mem_support_iff.mp hq
      -- the orbit sum vanishes, so another point of the orbit carries mass
      have hother : ∃ p ∈ c.support, p.2 = j ∧ inOrbit β p.1 ∧ p.1 ≠ β := by
        by_contra hno
        have hno' : ∀ p ∈ c.support, p.2 = j → inOrbit β p.1 → p.1 = β := by
          intro p hp h2 h1
          by_contra hne
          exact hno ⟨p, hp, h2, h1, hne⟩
        have hsingle : c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit β p.1)
            = {(β, j)} := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hp, hp2, hp1⟩
            have := hno' p hp hp2 hp1
            exact Prod.ext this hp2
          · rintro rfl
            exact ⟨hq, rfl, inOrbit_refl β⟩
        have := horb β j
        rw [orbSum, hsingle, Finset.sum_singleton] at this
        exact htne this
      obtain ⟨p, hpsupp, hp2, hp1, hpne⟩ := hother
      obtain ⟨k, hk⟩ := hp1
      have hkne : (k : ℂ) ≠ 0 := by
        intro h
        exact hpne (by rw [hk, h, add_zero])
      have hp_eq : p = (β + (k : ℂ), j) := Prod.ext hk hp2
      obtain ⟨w, hw⟩ := exists_polarDefect_single_sub j k β t
      set c₁ : (ℂ × ℕ) →₀ ℂ := c - polarDefect w with hc₁
      have horb₁ : ∀ α i, orbSum c₁ α i = 0 := by
        intro α i
        rw [hc₁, orbSum_sub, horb α i, orbSum_polarDefect, sub_zero]
      have hzero : c₁ (β, j) = 0 := by
        have hwβ : polarDefect w (β, j) = t := by
          rw [hw]
          simp only [Finsupp.sub_apply, Finsupp.single_apply, if_true]
          rw [if_neg, sub_zero]
          intro hcon
          have h1 := congrArg Prod.fst hcon
          simp only at h1
          exact hkne (by linear_combination h1)
        rw [hc₁, Finsupp.sub_apply, hwβ, ← ht, sub_self]
      have hsub : c₁.support ⊆ c.support.erase (β, j) := by
        intro r hr
        have hrne : r ≠ (β, j) := by
          intro hcon
          rw [hcon] at hr
          exact (Finsupp.mem_support_iff.mp hr) hzero
        refine Finset.mem_erase.mpr ⟨hrne, ?_⟩
        by_contra hnot
        have hcr : c r = 0 := Finsupp.notMem_support_iff.mp hnot
        have hdr : polarDefect w r = 0 := by
          rw [hw]
          simp only [Finsupp.sub_apply, Finsupp.single_apply]
          rw [if_neg, if_neg]
          · simp
          · intro hcon
            exact hnot (by rw [← hcon, ← hp_eq]; exact hpsupp)
          · intro hcon
            exact hnot (by rw [← hcon]; exact hq)
        exact (Finsupp.mem_support_iff.mp hr)
          (by rw [hc₁, Finsupp.sub_apply, hcr, hdr, sub_zero])
      have hcard₁ : c₁.support.card ≤ n := by
        have h1 : c₁.support.card ≤ (c.support.erase (β, j)).card := Finset.card_le_card hsub
        have h2 : (c.support.erase (β, j)).card = c.support.card - 1 :=
          Finset.card_erase_of_mem hq
        have h3 : 1 ≤ c.support.card := Finset.card_pos.mpr ⟨(β, j), hq⟩
        omega
      obtain ⟨w₁, hw₁⟩ := ih c₁ hcard₁ horb₁
      refine ⟨w + w₁, ?_⟩
      rw [polarDefect_add, hw₁, hc₁]
      abel

end HTGeometry
