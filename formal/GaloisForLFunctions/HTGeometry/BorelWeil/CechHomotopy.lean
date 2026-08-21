import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# The contracting homotopy of the Čech complex of a simplex

The Čech complex of a cover by `|T|` opens has, in each fixed multidegree, the shape of the
simplicial cochain complex of a simplex.  This file records the elementary combinatorial heart of
the computation: for any index `u₀` the operator

`(h ω) I = if u₀ ∈ I then 0 else (-1)^{#(I ∪ {u₀}) ∩ (· < u₀)} · ω (insert u₀ I)`

is a contracting homotopy for the Čech differential,

`d ∘ h + h ∘ d = id`.

Everything is stated for functions on `Finset T` with `T` a linearly ordered fintype; the grading
by cardinality and any support restrictions are imposed afterwards.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.cechSign`
* `GaloisForLFunctions.HTGeometry.BorelWeil.cechD`
* `GaloisForLFunctions.HTGeometry.BorelWeil.cechH`

## Main results

* `cechD_cechH_add` — the homotopy identity.
* `cechD_cechD` — the differential squares to zero.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

variable {T : Type*} [DecidableEq T] [LinearOrder T] {k : Type*} [CommRing k]

/-- The number of elements of `I` below `u`. -/
def belowCard (I : Finset T) (u : T) : ℕ := (I.filter (fun v => v < u)).card

/-- The Čech sign attached to removing `u` from `I`. -/
def cechSign (I : Finset T) (u : T) : k := (-1) ^ (belowCard I u)

theorem cechSign_mul_self (I : Finset T) (u : T) :
    (cechSign I u : k) * cechSign I u = 1 := by
  rw [cechSign, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem belowCard_insert_self (I : Finset T) (u₀ : T) :
    belowCard (insert u₀ I) u₀ = belowCard I u₀ := by
  classical
  rw [belowCard, belowCard, Finset.filter_insert, if_neg (lt_irrefl u₀)]

theorem belowCard_insert_of_lt {I : Finset T} {u₀ u : T} (h : u₀ < u) (hu₀ : u₀ ∉ I) :
    belowCard (insert u₀ I) u = belowCard I u + 1 := by
  classical
  rw [belowCard, belowCard, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem (fun hc => hu₀ (Finset.mem_filter.mp hc).1)]

theorem belowCard_insert_of_not_lt {I : Finset T} {u₀ u : T} (h : ¬ u₀ < u) :
    belowCard (insert u₀ I) u = belowCard I u := by
  classical
  rw [belowCard, belowCard, Finset.filter_insert, if_neg h]

theorem belowCard_erase_of_lt {I : Finset T} {u u₀ : T} (hu : u ∈ I) (h : u < u₀) :
    belowCard (I.erase u) u₀ + 1 = belowCard I u₀ := by
  classical
  rw [belowCard, belowCard, Finset.filter_erase,
    Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hu, h⟩)]
  have hpos : 0 < (I.filter (fun v => v < u₀)).card :=
    Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, h⟩⟩
  omega

theorem belowCard_erase_of_not_lt {I : Finset T} {u u₀ : T} (h : ¬ u < u₀) :
    belowCard (I.erase u) u₀ = belowCard I u₀ := by
  classical
  have hnot : u ∉ I.filter (fun v => v < u₀) := fun hc => h (Finset.mem_filter.mp hc).2
  rw [belowCard, belowCard, Finset.filter_erase, Finset.erase_eq_of_notMem hnot]

/-- The Čech differential on functions on subsets. -/
def cechD (ω : Finset T → k) : Finset T → k :=
  fun I => ∑ u ∈ I, cechSign I u * ω (I.erase u)

/-- The contracting homotopy attached to an index `u₀`. -/
def cechH (u₀ : T) (ω : Finset T → k) : Finset T → k :=
  fun I => if u₀ ∈ I then 0 else cechSign (insert u₀ I) u₀ * ω (insert u₀ I)

theorem cechD_add (ω₁ ω₂ : Finset T → k) : cechD (ω₁ + ω₂) = cechD ω₁ + cechD ω₂ := by
  funext I
  simp only [cechD, Pi.add_apply, mul_add, ← Finset.sum_add_distrib]

theorem cechH_add (u₀ : T) (ω₁ ω₂ : Finset T → k) :
    cechH u₀ (ω₁ + ω₂) = cechH u₀ ω₁ + cechH u₀ ω₂ := by
  funext I
  by_cases h : u₀ ∈ I <;> simp [cechH, h, mul_add]

/-- **The contracting homotopy identity.** -/
theorem cechD_cechH_add [Fintype T] (u₀ : T) (ω : Finset T → k) (I : Finset T) :
    cechD (cechH u₀ ω) I + cechH u₀ (cechD ω) I = ω I := by
  classical
  by_cases hu₀ : u₀ ∈ I
  · -- the homotopy term vanishes and only the `u₀` summand survives
    have hH : cechH u₀ (cechD ω) I = 0 := by rw [cechH, if_pos hu₀]
    rw [hH, add_zero, cechD, Finset.sum_eq_single u₀]
    · rw [cechH, if_neg (Finset.notMem_erase u₀ I), Finset.insert_erase hu₀,
        ← mul_assoc, cechSign_mul_self]
      rw [one_mul]
    · intro u hu hne
      have : u₀ ∈ I.erase u := Finset.mem_erase.mpr ⟨fun hc => hne hc.symm, hu₀⟩
      rw [cechH, if_pos this, mul_zero]
    · intro hcon; exact absurd hu₀ hcon
  · -- both terms contribute; the `u ∈ I` parts cancel
    have hins : ∀ u ∈ I, u₀ ∉ I.erase u := fun u _ hc => hu₀ (Finset.mem_of_mem_erase hc)
    have hD : cechD (cechH u₀ ω) I
        = ∑ u ∈ I, cechSign I u * (cechSign (insert u₀ (I.erase u)) u₀
            * ω (insert u₀ (I.erase u))) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [cechH, if_neg (hins u hu)]
    have hsplit : cechD ω (insert u₀ I)
        = cechSign (insert u₀ I) u₀ * ω I
          + ∑ u ∈ I, cechSign (insert u₀ I) u * ω ((insert u₀ I).erase u) := by
      rw [cechD, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self u₀ I),
        Finset.erase_insert hu₀]
    have hH : cechH u₀ (cechD ω) I
        = cechSign (insert u₀ I) u₀ * (cechSign (insert u₀ I) u₀ * ω I)
          + ∑ u ∈ I, cechSign (insert u₀ I) u₀
              * (cechSign (insert u₀ I) u * ω (insert u₀ (I.erase u))) := by
      rw [cechH, if_neg hu₀, hsplit, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      have hne : u ≠ u₀ := by
        intro hc
        exact hu₀ (hc ▸ hu)
      congr 2
      rw [Finset.erase_insert_of_ne (Ne.symm hne)]
    have hcancel : ∀ u ∈ I,
        cechSign (insert u₀ I) u₀ * ((cechSign (insert u₀ I) u : k)
            * ω (insert u₀ (I.erase u)))
          = -(cechSign I u * ((cechSign (insert u₀ (I.erase u)) u₀ : k)
              * ω (insert u₀ (I.erase u)))) := by
      intro u hu
      have hne : u ≠ u₀ := by
        intro hc
        exact hu₀ (hc ▸ hu)
      have hkey : (cechSign (insert u₀ I) u₀ : k) * cechSign (insert u₀ I) u
          = -(cechSign I u * cechSign (insert u₀ (I.erase u)) u₀) := by
        rw [cechSign, cechSign, cechSign, cechSign, ← pow_add, ← pow_add,
          belowCard_insert_self]
        have hexp : belowCard I u₀ + belowCard (insert u₀ I) u
            = belowCard I u + belowCard (insert u₀ (I.erase u)) u₀ + 1 := by
          have h1 : belowCard (insert u₀ (I.erase u)) u₀ = belowCard (I.erase u) u₀ :=
            belowCard_insert_self _ _
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · -- u < u₀
            have h2 : belowCard (insert u₀ I) u = belowCard I u :=
              belowCard_insert_of_not_lt (not_lt.mpr (le_of_lt hlt))
            have h3 := belowCard_erase_of_lt hu hlt
            omega
          · -- u₀ < u
            have h2 : belowCard (insert u₀ I) u = belowCard I u + 1 :=
              belowCard_insert_of_lt hgt hu₀
            have h3 : belowCard (I.erase u) u₀ = belowCard I u₀ :=
              belowCard_erase_of_not_lt (not_lt.mpr (le_of_lt hgt))
            omega
        rw [hexp, pow_succ]
        ring
      rw [← mul_assoc, ← mul_assoc, hkey]
      ring
    rw [hD, hH, Finset.sum_congr rfl hcancel, ← mul_assoc, cechSign_mul_self, one_mul]
    rw [Finset.sum_neg_distrib]
    ring

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

variable {T : Type*} [DecidableEq T] [LinearOrder T] {k : Type*} [CommRing k]

@[simp] theorem cechD_zero : cechD (0 : Finset T → k) = 0 := by
  funext I
  simp [cechD]

@[simp] theorem cechH_zero (u₀ : T) : cechH u₀ (0 : Finset T → k) = 0 := by
  funext I
  by_cases h : u₀ ∈ I <;> simp [cechH, h]

/-- **Exactness of the Čech complex of a simplex.**  Every cocycle is a coboundary. -/
theorem eq_cechD_cechH_of_cechD_eq_zero [Fintype T] (u₀ : T) {ω : Finset T → k}
    (h : cechD ω = 0) : ω = cechD (cechH u₀ ω) := by
  funext I
  have hid := cechD_cechH_add u₀ ω I
  rw [h, cechH_zero] at hid
  simpa using hid.symm

end GaloisForLFunctions.HTGeometry.BorelWeil
