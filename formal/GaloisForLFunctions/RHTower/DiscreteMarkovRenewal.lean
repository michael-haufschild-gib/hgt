import Mathlib

/-!
# Discounted path sums and the first-entrance decomposition

A time-homogeneous transition law on a countable state space assigns to every finite path a weight,
the product of its one-step transitions.  Discounting a path by the geometric factor of its length
and summing over all finite paths gives the discounted occupation mass; restricting to the paths
that reach a target set for the first time gives the discounted entrance mass.

Every path ending in the target splits uniquely at its first target time into an entrance segment
followed by a free continuation, and path weights multiply along that split.  This is the exact
first-entrance decomposition of discounted occupation: occupation equals entrance composed with
unrestricted continuation from the entrance point.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section Paths

variable {S : Type*}

/-- Endpoint of the finite path started at `x` and recorded by its successor states. -/
def pathEnd : S → List S → S
  | x, [] => x
  | _, y :: l => pathEnd y l

@[simp] theorem pathEnd_nil (x : S) : pathEnd x ([] : List S) = x := rfl

@[simp] theorem pathEnd_cons (x y : S) (l : List S) : pathEnd x (y :: l) = pathEnd y l := rfl

theorem pathEnd_append (x : S) (l m : List S) :
    pathEnd x (l ++ m) = pathEnd (pathEnd x l) m := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih => simpa using ih y

/-- Weight of the finite path started at `x`, the product of its one-step transitions. -/
noncomputable def pathWeight (P : S → S → ℝ≥0∞) : S → List S → ℝ≥0∞
  | _, [] => 1
  | x, y :: l => P x y * pathWeight P y l

@[simp] theorem pathWeight_nil (P : S → S → ℝ≥0∞) (x : S) :
    pathWeight P x ([] : List S) = 1 := rfl

@[simp] theorem pathWeight_cons (P : S → S → ℝ≥0∞) (x y : S) (l : List S) :
    pathWeight P x (y :: l) = P x y * pathWeight P y l := rfl

theorem pathWeight_append (P : S → S → ℝ≥0∞) (x : S) (l m : List S) :
    pathWeight P x (l ++ m) = pathWeight P x l * pathWeight P (pathEnd x l) m := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih => simp [ih y, mul_assoc]

theorem pathEnd_take_of_length_le {x : S} {l : List S} {j : ℕ} (hj : l.length ≤ j) :
    pathEnd x (l.take j) = pathEnd x l := by
  rw [List.take_of_length_le hj]

end Paths

section Entrance

variable {S : Type*}

/-- A finite path reaches the target set for the first time at its endpoint. -/
def FirstEntrance (A : Set S) (x : S) (l : List S) : Prop :=
  pathEnd x l ∈ A ∧ ∀ j < l.length, pathEnd x (l.take j) ∉ A

theorem firstEntrance_nil_iff (A : Set S) (x : S) :
    FirstEntrance A x ([] : List S) ↔ x ∈ A := by
  constructor
  · rintro ⟨h, -⟩; simpa using h
  · intro h; exact ⟨by simpa using h, by simp⟩

open Classical in
/-- The first time at which a path started at `x` meets the target set. -/
noncomputable def firstEntranceTime (A : Set S) (x : S) (l : List S) : ℕ :=
  if h : ∃ k, pathEnd x (l.take k) ∈ A then Nat.find h else l.length

theorem firstEntranceTime_spec {A : Set S} {x : S} {l : List S} (hl : pathEnd x l ∈ A) :
    pathEnd x (l.take (firstEntranceTime A x l)) ∈ A ∧
      ∀ j < firstEntranceTime A x l, pathEnd x (l.take j) ∉ A := by
  classical
  have hex : ∃ k, pathEnd x (l.take k) ∈ A :=
    ⟨l.length, by rwa [pathEnd_take_of_length_le (le_refl _)]⟩
  rw [firstEntranceTime, dif_pos hex]
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

theorem firstEntranceTime_le {A : Set S} {x : S} {l : List S} (hl : pathEnd x l ∈ A) :
    firstEntranceTime A x l ≤ l.length := by
  classical
  have hex : ∃ k, pathEnd x (l.take k) ∈ A :=
    ⟨l.length, by rwa [pathEnd_take_of_length_le (le_refl _)]⟩
  rw [firstEntranceTime, dif_pos hex]
  exact Nat.find_le (by rwa [pathEnd_take_of_length_le (le_refl _)])

theorem firstEntrance_take {A : Set S} {x : S} {l : List S} (hl : pathEnd x l ∈ A) :
    FirstEntrance A x (l.take (firstEntranceTime A x l)) := by
  obtain ⟨hmem, hmin⟩ := firstEntranceTime_spec hl
  have hle := firstEntranceTime_le hl
  refine ⟨hmem, fun j hj => ?_⟩
  rw [List.length_take, min_eq_left hle] at hj
  rw [List.take_take, min_eq_left hj.le]
  exact hmin j hj

theorem firstEntranceTime_append {A : Set S} {x : S} {p q : List S}
    (hp : FirstEntrance A x p) : firstEntranceTime A x (p ++ q) = p.length := by
  classical
  have hend : pathEnd x (p ++ q) ∈ A ∨ True := Or.inr trivial
  have hex : ∃ k, pathEnd x ((p ++ q).take k) ∈ A := by
    refine ⟨p.length, ?_⟩
    rw [List.take_left]
    exact hp.1
  rw [firstEntranceTime, dif_pos hex]
  refine le_antisymm (Nat.find_le (by rw [List.take_left]; exact hp.1)) ?_
  refine Nat.le_of_not_lt fun hlt => ?_
  have hspec := Nat.find_spec hex
  have hj : Nat.find hex < p.length := hlt
  have : (p ++ q).take (Nat.find hex) = p.take (Nat.find hex) := by
    rw [List.take_append_of_le_length hj.le]
  rw [this] at hspec
  exact hp.2 _ hj hspec

end Entrance

section GreenMass

variable {S : Type*} [Countable S]

/-- Discounted occupation mass of a target set. -/
noncomputable def greenMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (x : S) (B : Set S) : ℝ≥0∞ :=
  ∑' l : List S, Set.indicator {l : List S | pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l) l

/-- Discounted first-entrance mass of a target set. -/
noncomputable def entranceMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S) (B : Set S) :
    ℝ≥0∞ :=
  ∑' l : List S, Set.indicator {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l) l

/-- Splitting a path at its first target time is a bijection onto entrance-continuation pairs. -/
noncomputable def firstEntranceSplit (A B : Set S) (hBA : B ⊆ A) (x : S) :
    {pq : List S × List S //
        FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B} ≃
      {l : List S // pathEnd x l ∈ B} where
  toFun pq := ⟨pq.1.1 ++ pq.1.2, by
    rw [pathEnd_append]
    exact pq.2.2⟩
  invFun l := ⟨(l.1.take (firstEntranceTime A x l.1), l.1.drop (firstEntranceTime A x l.1)), by
    refine ⟨firstEntrance_take (hBA l.2), ?_⟩
    rw [← pathEnd_append, List.take_append_drop]
    exact l.2⟩
  left_inv := by
    rintro ⟨⟨p, q⟩, hp, hq⟩
    have hlen : firstEntranceTime A x (p ++ q) = p.length := firstEntranceTime_append hp
    refine Subtype.ext ?_
    simp only [hlen, List.take_left, List.drop_left]
  right_inv := by
    rintro ⟨l, hl⟩
    exact Subtype.ext (List.take_append_drop _ _)

/-- Weight of an entrance-continuation pair. -/
noncomputable def splitWeight (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S) (x : S)
    (pq : List S × List S) : ℝ≥0∞ :=
  Set.indicator {pq : List S × List S |
      FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B}
    (fun pq => a ^ pq.1.length * pathWeight P x pq.1 *
      (a ^ pq.2.length * pathWeight P (pathEnd x pq.1) pq.2)) pq

theorem greenMass_eq_tsum_subtype (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (x : S) (B : Set S) :
    greenMass P a x B =
      ∑' l : {l : List S // pathEnd x l ∈ B},
        a ^ (l : List S).length * pathWeight P x (l : List S) :=
  (tsum_subtype {l : List S | pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l)).symm

theorem entranceMass_eq_tsum_subtype (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S)
    (B : Set S) :
    entranceMass P a A x B =
      ∑' l : {l : List S // FirstEntrance A x l ∧ pathEnd x l ∈ B},
        a ^ (l : List S).length * pathWeight P x (l : List S) :=
  (tsum_subtype {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l)).symm

theorem tsum_splitWeight_eq_greenMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S) (hBA : B ⊆ A)
    (x : S) :
    (∑' pq : List S × List S, splitWeight P a A B x pq) = greenMass P a x B := by
  classical
  have hsub : (∑' pq : List S × List S, splitWeight P a A B x pq) =
      ∑' pq : {pq : List S × List S //
          FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B},
        a ^ (pq : List S × List S).1.length * pathWeight P x (pq : List S × List S).1 *
          (a ^ (pq : List S × List S).2.length *
            pathWeight P (pathEnd x (pq : List S × List S).1) (pq : List S × List S).2) :=
    (tsum_subtype {pq : List S × List S |
        FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B}
      (fun pq => a ^ pq.1.length * pathWeight P x pq.1 *
        (a ^ pq.2.length * pathWeight P (pathEnd x pq.1) pq.2))).symm
  have hval : ∀ pq : {pq : List S × List S //
        FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B},
      a ^ (pq : List S × List S).1.length * pathWeight P x (pq : List S × List S).1 *
          (a ^ (pq : List S × List S).2.length *
            pathWeight P (pathEnd x (pq : List S × List S).1) (pq : List S × List S).2) =
        a ^ ((firstEntranceSplit A B hBA x pq : {l : List S // pathEnd x l ∈ B}) :
              List S).length *
          pathWeight P x ((firstEntranceSplit A B hBA x pq :
            {l : List S // pathEnd x l ∈ B}) : List S) := by
    rintro ⟨⟨p, q⟩, hpq⟩
    show a ^ p.length * pathWeight P x p * (a ^ q.length * pathWeight P (pathEnd x p) q) =
      a ^ (p ++ q).length * pathWeight P x (p ++ q)
    rw [List.length_append, pow_add, pathWeight_append]
    ring
  rw [hsub, tsum_congr hval,
    (firstEntranceSplit A B hBA x).tsum_eq
      (fun l : {l : List S // pathEnd x l ∈ B} =>
        a ^ (l : List S).length * pathWeight P x (l : List S)),
    greenMass_eq_tsum_subtype]

theorem tsum_splitWeight_eq_tsum_entranceMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S)
    (x : S) :
    (∑' pq : List S × List S, splitWeight P a A B x pq) =
      ∑' z : S, entranceMass P a A x {z} * greenMass P a z B := by
  classical
  have hinner : ∀ p : List S,
      (∑' q : List S, splitWeight P a A B x (p, q)) =
        Set.indicator {p : List S | FirstEntrance A x p}
          (fun p => a ^ p.length * pathWeight P x p) p *
          greenMass P a (pathEnd x p) B := by
    intro p
    by_cases hp : FirstEntrance A x p
    · rw [Set.indicator_of_mem (show p ∈ {p : List S | FirstEntrance A x p} from hp)]
      have hterm : ∀ q : List S, splitWeight P a A B x (p, q) =
          (a ^ p.length * pathWeight P x p) *
            Set.indicator {q : List S | pathEnd (pathEnd x p) q ∈ B}
              (fun q => a ^ q.length * pathWeight P (pathEnd x p) q) q := by
        intro q
        by_cases hq : pathEnd (pathEnd x p) q ∈ B
        · rw [splitWeight,
            Set.indicator_of_mem (show (p, q) ∈ {pq : List S × List S |
              FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B} from ⟨hp, hq⟩),
            Set.indicator_of_mem
              (show q ∈ {q : List S | pathEnd (pathEnd x p) q ∈ B} from hq)]
        · rw [splitWeight,
            Set.indicator_of_notMem (show (p, q) ∉ {pq : List S × List S |
              FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B} from
              fun hc => hq hc.2),
            Set.indicator_of_notMem
              (show q ∉ {q : List S | pathEnd (pathEnd x p) q ∈ B} from hq), mul_zero]
      rw [tsum_congr hterm, ENNReal.tsum_mul_left, greenMass]
    · have hterm : ∀ q : List S, splitWeight P a A B x (p, q) = 0 := by
        intro q
        rw [splitWeight, Set.indicator_of_notMem (show (p, q) ∉ {pq : List S × List S |
          FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B} from fun hc => hp hc.1)]
      rw [tsum_congr hterm, tsum_zero,
        Set.indicator_of_notMem (show p ∉ {p : List S | FirstEntrance A x p} from hp), zero_mul]
  have hright : ∀ z : S, entranceMass P a A x {z} * greenMass P a z B =
      ∑' p : List S, Set.indicator {p : List S | FirstEntrance A x p ∧ pathEnd x p ∈ ({z} : Set S)}
        (fun p => a ^ p.length * pathWeight P x p) p * greenMass P a z B := by
    intro z
    rw [entranceMass, ENNReal.tsum_mul_right]
  have hprod : (∑' pq : List S × List S, splitWeight P a A B x pq) =
      ∑' p : List S, ∑' q : List S, splitWeight P a A B x (p, q) := by
    rw [← ENNReal.tsum_prod (f := fun p q => splitWeight P a A B x (p, q))]
  rw [hprod, tsum_congr hinner, tsum_congr hright, ENNReal.tsum_comm]
  refine tsum_congr fun p => ?_
  by_cases hp : FirstEntrance A x p
  · rw [Set.indicator_of_mem (show p ∈ {p : List S | FirstEntrance A x p} from hp)]
    have hsingle : (∑' z : S, Set.indicator {p : List S |
          FirstEntrance A x p ∧ pathEnd x p ∈ ({z} : Set S)}
          (fun p => a ^ p.length * pathWeight P x p) p * greenMass P a z B) =
        Set.indicator {p : List S |
          FirstEntrance A x p ∧ pathEnd x p ∈ ({pathEnd x p} : Set S)}
          (fun p => a ^ p.length * pathWeight P x p) p * greenMass P a (pathEnd x p) B := by
      refine tsum_eq_single (pathEnd x p) fun z hz => ?_
      rw [Set.indicator_of_notMem (show p ∉ {p : List S |
        FirstEntrance A x p ∧ pathEnd x p ∈ ({z} : Set S)} from fun hc => hz hc.2.symm),
        zero_mul]
    rw [hsingle, Set.indicator_of_mem (show p ∈ {p : List S |
      FirstEntrance A x p ∧ pathEnd x p ∈ ({pathEnd x p} : Set S)} from ⟨hp, rfl⟩)]
  · rw [Set.indicator_of_notMem (show p ∉ {p : List S | FirstEntrance A x p} from hp), zero_mul]
    refine (ENNReal.tsum_eq_zero.mpr fun z => ?_).symm
    rw [Set.indicator_of_notMem (show p ∉ {p : List S |
      FirstEntrance A x p ∧ pathEnd x p ∈ ({z} : Set S)} from fun hc => hp hc.1), zero_mul]

/-- **First-entrance decomposition.**  Discounted occupation of a target inside `A` is discounted
entrance into `A` followed by unrestricted discounted continuation. -/
theorem greenMass_eq_tsum_entranceMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S) (hBA : B ⊆ A)
    (x : S) :
    greenMass P a x B = ∑' z : S, entranceMass P a A x {z} * greenMass P a z B := by
  rw [← tsum_splitWeight_eq_greenMass P a A B hBA x,
    tsum_splitWeight_eq_tsum_entranceMass P a A B x]

end GreenMass

section ConsSplit

variable {S : Type*} [Countable S]

/-- Nonempty finite paths are exactly a first step followed by a path. -/
def listConsEquiv (S : Type*) : S × List S ≃ {l : List S // l ≠ []} where
  toFun p := ⟨p.1 :: p.2, by simp⟩
  invFun l := (l.1.head l.2, l.1.tail)
  left_inv := by rintro ⟨y, l⟩; rfl
  right_inv := by
    rintro ⟨l, hl⟩
    cases l with
    | nil => exact absurd rfl hl
    | cons y l => rfl

theorem tsum_list_split (f : List S → ℝ≥0∞) :
    (∑' l : List S, f l) = f [] + ∑' p : S × List S, f (p.1 :: p.2) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite (f := f) []]
  congr 1
  have hR : (∑' p : S × List S, f (p.1 :: p.2)) =
      ∑' l : {l : List S // l ≠ []}, f (l : List S) :=
    (listConsEquiv S).tsum_eq (fun l : {l : List S // l ≠ []} => f (l : List S))
  rw [hR, tsum_subtype {l : List S | l ≠ []} f]
  refine tsum_congr fun l => ?_
  by_cases hl : l = []
  · rw [if_pos hl,
      Set.indicator_of_notMem (show l ∉ {l : List S | l ≠ []} from by simp [hl])]
  · rw [if_neg hl, Set.indicator_of_mem (show l ∈ {l : List S | l ≠ []} from hl)]

end ConsSplit

section EntranceRecursion

variable {S : Type*} [Countable S]

theorem firstEntrance_cons_iff (A : Set S) (x y : S) (l : List S) :
    FirstEntrance A x (y :: l) ↔ x ∉ A ∧ FirstEntrance A y l := by
  constructor
  · rintro ⟨hend, hmin⟩
    refine ⟨by simpa using hmin 0 (by simp), by simpa using hend, fun j hj => ?_⟩
    have := hmin (j + 1) (by simpa using hj)
    simpa using this
  · rintro ⟨hx, hend, hmin⟩
    refine ⟨by simpa using hend, fun j hj => ?_⟩
    cases j with
    | zero => simpa using hx
    | succ j =>
        have hj' : j < l.length := by simpa using hj
        simpa using hmin j hj'

/-- At the target the discounted entrance mass stops. -/
theorem entranceMass_of_mem (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A : Set S} {x : S} (B : Set S)
    (hx : x ∈ A) : entranceMass P a A x B = Set.indicator B 1 x := by
  classical
  rw [entranceMass, tsum_list_split]
  have hnil : Set.indicator {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l) [] = Set.indicator B 1 x := by
    by_cases hB : x ∈ B
    · rw [Set.indicator_of_mem (show ([] : List S) ∈ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from
          ⟨(firstEntrance_nil_iff A x).mpr hx, by simpa using hB⟩),
        Set.indicator_of_mem hB]
      simp
    · rw [Set.indicator_of_notMem (show ([] : List S) ∉ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from fun hc => hB (by simpa using hc.2)),
        Set.indicator_of_notMem hB]
  have hcons : ∀ p : S × List S, Set.indicator {l : List S |
      FirstEntrance A x l ∧ pathEnd x l ∈ B}
        (fun l => a ^ l.length * pathWeight P x l) (p.1 :: p.2) = 0 := by
    intro p
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact ((firstEntrance_cons_iff A x p.1 p.2).mp hc.1).1 hx
  rw [hnil, tsum_congr hcons, tsum_zero, add_zero]

/-- Off the target the discounted entrance mass takes one discounted step. -/
theorem entranceMass_of_notMem (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A : Set S} {x : S} (B : Set S)
    (hx : x ∉ A) :
    entranceMass P a A x B = a * ∑' y : S, P x y * entranceMass P a A y B := by
  classical
  rw [entranceMass, tsum_list_split]
  have hnil : Set.indicator {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l) [] = 0 := by
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact hx ((firstEntrance_nil_iff A x).mp hc.1)
  have hcons : ∀ p : S × List S, Set.indicator {l : List S |
      FirstEntrance A x l ∧ pathEnd x l ∈ B}
        (fun l => a ^ l.length * pathWeight P x l) (p.1 :: p.2) =
      a * (P x p.1 * Set.indicator {l : List S |
        FirstEntrance A p.1 l ∧ pathEnd p.1 l ∈ B}
        (fun l => a ^ l.length * pathWeight P p.1 l) p.2) := by
    rintro ⟨y, l⟩
    by_cases hFE : FirstEntrance A y l ∧ pathEnd y l ∈ B
    · rw [Set.indicator_of_mem (show (y :: l) ∈ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from
          ⟨(firstEntrance_cons_iff A x y l).mpr ⟨hx, hFE.1⟩, by simpa using hFE.2⟩),
        Set.indicator_of_mem (show l ∈ {l : List S |
          FirstEntrance A y l ∧ pathEnd y l ∈ B} from hFE)]
      simp only [List.length_cons, pathWeight_cons, pow_succ]
      ring
    · rw [Set.indicator_of_notMem (show (y :: l) ∉ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from fun hc =>
          hFE ⟨((firstEntrance_cons_iff A x y l).mp hc.1).2, by simpa using hc.2⟩),
        Set.indicator_of_notMem (show l ∉ {l : List S |
          FirstEntrance A y l ∧ pathEnd y l ∈ B} from hFE), mul_zero, mul_zero]
  rw [hnil, zero_add, tsum_congr hcons, ENNReal.tsum_mul_left]
  congr 1
  refine tsum_congr fun y => ?_
  rw [entranceMass, ← tsum_subtype, ENNReal.tsum_mul_left, tsum_subtype]

end EntranceRecursion

end GaloisForLFunctions.RHTower
