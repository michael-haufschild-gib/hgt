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
  rw [hR]
  refine Eq.trans ?_ (tsum_subtype {l : List S | l ≠ []} f).symm
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
  have hprod : (∑' p : S × List S, P x p.1 *
      Set.indicator {l : List S | FirstEntrance A p.1 l ∧ pathEnd p.1 l ∈ B}
        (fun l => a ^ l.length * pathWeight P p.1 l) p.2) =
      ∑' y : S, ∑' l : List S, P x y *
        Set.indicator {l : List S | FirstEntrance A y l ∧ pathEnd y l ∈ B}
          (fun l => a ^ l.length * pathWeight P y l) l := by
    rw [← ENNReal.tsum_prod (f := fun y l => P x y *
      Set.indicator {l : List S | FirstEntrance A y l ∧ pathEnd y l ∈ B}
        (fun l => a ^ l.length * pathWeight P y l) l)]
  rw [hprod]
  exact tsum_congr fun y => by rw [ENNReal.tsum_mul_left, entranceMass]

end EntranceRecursion

section Stochastic

variable {S : Type*} [Countable S]

/-- Total weight of the paths of a fixed length. -/
noncomputable def levelMass (P : S → S → ℝ≥0∞) (x : S) (n : ℕ) : ℝ≥0∞ :=
  ∑' l : List S, Set.indicator {l : List S | l.length = n} (fun l => pathWeight P x l) l

theorem levelMass_zero (P : S → S → ℝ≥0∞) (x : S) : levelMass P x 0 = 1 := by
  classical
  rw [levelMass, tsum_list_split]
  have hnil : Set.indicator {l : List S | l.length = 0} (fun l => pathWeight P x l) [] = 1 := by
    rw [Set.indicator_of_mem (show ([] : List S) ∈ {l : List S | l.length = 0} from rfl)]
    simp
  have hcons : ∀ p : S × List S,
      Set.indicator {l : List S | l.length = 0} (fun l => pathWeight P x l) (p.1 :: p.2) = 0 := by
    intro p
    exact Set.indicator_of_notMem (by simp) _
  rw [hnil, tsum_congr hcons, tsum_zero, add_zero]

theorem levelMass_succ (P : S → S → ℝ≥0∞) (x : S) (n : ℕ) :
    levelMass P x (n + 1) = ∑' y : S, P x y * levelMass P y n := by
  classical
  rw [levelMass, tsum_list_split]
  have hnil : Set.indicator {l : List S | l.length = n + 1}
      (fun l => pathWeight P x l) [] = 0 :=
    Set.indicator_of_notMem (by simp) _
  have hcons : ∀ p : S × List S,
      Set.indicator {l : List S | l.length = n + 1} (fun l => pathWeight P x l) (p.1 :: p.2) =
        P x p.1 * Set.indicator {l : List S | l.length = n}
          (fun l => pathWeight P p.1 l) p.2 := by
    rintro ⟨y, l⟩
    by_cases hl : l.length = n
    · rw [Set.indicator_of_mem (show (y :: l) ∈ {l : List S | l.length = n + 1} from by
        simp [hl]), Set.indicator_of_mem (show l ∈ {l : List S | l.length = n} from hl)]
      simp
    · rw [Set.indicator_of_notMem (show (y :: l) ∉ {l : List S | l.length = n + 1} from by
        simpa using hl), Set.indicator_of_notMem
          (show l ∉ {l : List S | l.length = n} from hl), mul_zero]
  rw [hnil, zero_add, tsum_congr hcons]
  have hprod : (∑' p : S × List S, P x p.1 * Set.indicator {l : List S | l.length = n}
      (fun l => pathWeight P p.1 l) p.2) =
      ∑' y : S, ∑' l : List S, P x y * Set.indicator {l : List S | l.length = n}
        (fun l => pathWeight P y l) l := by
    rw [← ENNReal.tsum_prod (f := fun y l => P x y * Set.indicator {l : List S | l.length = n}
      (fun l => pathWeight P y l) l)]
  rw [hprod]
  exact tsum_congr fun y => by rw [ENNReal.tsum_mul_left, levelMass]

theorem levelMass_eq_one (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1) (x : S) (n : ℕ) :
    levelMass P x n = 1 := by
  induction n generalizing x with
  | zero => exact levelMass_zero P x
  | succ n ih =>
      rw [levelMass_succ]
      calc (∑' y : S, P x y * levelMass P y n) = ∑' y : S, P x y := by
            exact tsum_congr fun y => by rw [ih y, mul_one]
        _ = 1 := hP x

/-- Discounted entrance mass truncated to paths shorter than a bound. -/
noncomputable def entranceMassTrunc (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S)
    (B : Set S) (n : ℕ) : ℝ≥0∞ :=
  ∑' l : List S, Set.indicator
    {l : List S | (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n}
    (fun l => a ^ l.length * pathWeight P x l) l

theorem entranceMassTrunc_zero (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S) (B : Set S) :
    entranceMassTrunc P a A x B 0 = 0 := by
  rw [entranceMassTrunc]
  refine (ENNReal.tsum_eq_zero).mpr fun l => ?_
  exact Set.indicator_of_notMem (by simp) _

theorem entranceMassTrunc_succ_of_mem (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A : Set S} {x : S}
    (B : Set S) (hx : x ∈ A) (n : ℕ) :
    entranceMassTrunc P a A x B (n + 1) = Set.indicator B 1 x := by
  classical
  rw [entranceMassTrunc, tsum_list_split]
  have hnil : Set.indicator {l : List S | (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1}
      (fun l => a ^ l.length * pathWeight P x l) [] = Set.indicator B 1 x := by
    by_cases hB : x ∈ B
    · rw [Set.indicator_of_mem (show ([] : List S) ∈ {l : List S |
        (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1} from
          ⟨⟨(firstEntrance_nil_iff A x).mpr hx, by simpa using hB⟩, by simp⟩),
        Set.indicator_of_mem hB]
      simp
    · rw [Set.indicator_of_notMem (show ([] : List S) ∉ {l : List S |
        (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1} from
          fun hc => hB (by simpa using hc.1.2)), Set.indicator_of_notMem hB]
  have hcons : ∀ p : S × List S, Set.indicator {l : List S |
      (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1}
        (fun l => a ^ l.length * pathWeight P x l) (p.1 :: p.2) = 0 := by
    intro p
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact ((firstEntrance_cons_iff A x p.1 p.2).mp hc.1.1).1 hx
  rw [hnil, tsum_congr hcons, tsum_zero, add_zero]

theorem entranceMassTrunc_succ_of_notMem (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A : Set S} {x : S}
    (B : Set S) (hx : x ∉ A) (n : ℕ) :
    entranceMassTrunc P a A x B (n + 1) =
      a * ∑' y : S, P x y * entranceMassTrunc P a A y B n := by
  classical
  rw [entranceMassTrunc, tsum_list_split]
  have hnil : Set.indicator {l : List S |
      (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1}
      (fun l => a ^ l.length * pathWeight P x l) [] = 0 := by
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact hx ((firstEntrance_nil_iff A x).mp hc.1.1)
  have hcons : ∀ p : S × List S, Set.indicator {l : List S |
      (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1}
        (fun l => a ^ l.length * pathWeight P x l) (p.1 :: p.2) =
      a * (P x p.1 * Set.indicator {l : List S |
        (FirstEntrance A p.1 l ∧ pathEnd p.1 l ∈ B) ∧ l.length < n}
        (fun l => a ^ l.length * pathWeight P p.1 l) p.2) := by
    rintro ⟨y, l⟩
    by_cases hFE : (FirstEntrance A y l ∧ pathEnd y l ∈ B) ∧ l.length < n
    · rw [Set.indicator_of_mem (show (y :: l) ∈ {l : List S |
        (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1} from
          ⟨⟨(firstEntrance_cons_iff A x y l).mpr ⟨hx, hFE.1.1⟩, by simpa using hFE.1.2⟩,
            by simpa using hFE.2⟩),
        Set.indicator_of_mem (show l ∈ {l : List S |
          (FirstEntrance A y l ∧ pathEnd y l ∈ B) ∧ l.length < n} from hFE)]
      simp only [List.length_cons, pathWeight_cons, pow_succ]
      ring
    · rw [Set.indicator_of_notMem (show (y :: l) ∉ {l : List S |
        (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n + 1} from fun hc =>
          hFE ⟨⟨((firstEntrance_cons_iff A x y l).mp hc.1.1).2, by simpa using hc.1.2⟩,
            by simpa using hc.2⟩),
        Set.indicator_of_notMem (show l ∉ {l : List S |
          (FirstEntrance A y l ∧ pathEnd y l ∈ B) ∧ l.length < n} from hFE), mul_zero, mul_zero]
  rw [hnil, zero_add, tsum_congr hcons, ENNReal.tsum_mul_left]
  congr 1
  have hprod : (∑' p : S × List S, P x p.1 * Set.indicator {l : List S |
      (FirstEntrance A p.1 l ∧ pathEnd p.1 l ∈ B) ∧ l.length < n}
        (fun l => a ^ l.length * pathWeight P p.1 l) p.2) =
      ∑' y : S, ∑' l : List S, P x y * Set.indicator {l : List S |
        (FirstEntrance A y l ∧ pathEnd y l ∈ B) ∧ l.length < n}
          (fun l => a ^ l.length * pathWeight P y l) l := by
    rw [← ENNReal.tsum_prod (f := fun y l => P x y * Set.indicator {l : List S |
      (FirstEntrance A y l ∧ pathEnd y l ∈ B) ∧ l.length < n}
        (fun l => a ^ l.length * pathWeight P y l) l)]
  rw [hprod]
  exact tsum_congr fun y => by rw [ENNReal.tsum_mul_left, entranceMassTrunc]

theorem entranceMassTrunc_le_one (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1)
    {a : ℝ≥0∞} (ha : a ≤ 1) (A : Set S) (B : Set S) (n : ℕ) (x : S) :
    entranceMassTrunc P a A x B n ≤ 1 := by
  induction n generalizing x with
  | zero => rw [entranceMassTrunc_zero]; exact zero_le_one
  | succ n ih =>
      by_cases hx : x ∈ A
      · rw [entranceMassTrunc_succ_of_mem P a B hx n]
        by_cases hB : x ∈ B
        · rw [Set.indicator_of_mem hB, Pi.one_apply]
        · rw [Set.indicator_of_notMem hB]; exact zero_le_one
      · rw [entranceMassTrunc_succ_of_notMem P a B hx n]
        calc a * ∑' y : S, P x y * entranceMassTrunc P a A y B n
            ≤ 1 * ∑' y : S, P x y * 1 := by
              refine mul_le_mul' ha (ENNReal.tsum_le_tsum fun y => mul_le_mul_right (ih y) _)
          _ = 1 := by simp [hP x]

/-- **Entrance total mass.**  A discounted first-entrance family is a subprobability. -/
theorem entranceMass_le_one (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1)
    {a : ℝ≥0∞} (ha : a ≤ 1) (A : Set S) (x : S) (B : Set S) :
    entranceMass P a A x B ≤ 1 := by
  classical
  rw [entranceMass, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set n : ℕ := (s.sup List.length) + 1 with hn
  have hbound : ∀ l ∈ s, Set.indicator {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l) l ≤
      Set.indicator {l : List S | (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n}
        (fun l => a ^ l.length * pathWeight P x l) l := by
    intro l hl
    by_cases hFE : FirstEntrance A x l ∧ pathEnd x l ∈ B
    · have hlen : l.length < n := by
        have := Finset.le_sup (f := List.length) hl
        omega
      rw [Set.indicator_of_mem (show l ∈ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from hFE),
        Set.indicator_of_mem (show l ∈ {l : List S |
          (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n} from ⟨hFE, hlen⟩)]
    · rw [Set.indicator_of_notMem (show l ∉ {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ B} from hFE)]
      exact bot_le
  calc (∑ l ∈ s, Set.indicator {l : List S | FirstEntrance A x l ∧ pathEnd x l ∈ B}
        (fun l => a ^ l.length * pathWeight P x l) l)
      ≤ ∑ l ∈ s, Set.indicator {l : List S |
          (FirstEntrance A x l ∧ pathEnd x l ∈ B) ∧ l.length < n}
          (fun l => a ^ l.length * pathWeight P x l) l := Finset.sum_le_sum hbound
    _ ≤ entranceMassTrunc P a A x B n := ENNReal.sum_le_tsum s
    _ ≤ 1 := entranceMassTrunc_le_one P hP ha A B n x

end Stochastic

section GreenBounds

variable {S : Type*} [Countable S]

theorem tsum_list_regroup (g : List S → ℝ≥0∞) :
    (∑' l : List S, g l) = ∑' n : ℕ, ∑' l : {l : List S // l.length = n}, g (l : List S) := by
  rw [← (Equiv.sigmaFiberEquiv (List.length : List S → ℕ)).tsum_eq g, ENNReal.tsum_sigma']
  rfl

/-- Discounted occupation takes one discounted step after recording the present state. -/
theorem greenMass_step (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (x : S) (B : Set S) :
    greenMass P a x B = Set.indicator B 1 x + a * ∑' y : S, P x y * greenMass P a y B := by
  classical
  rw [greenMass, tsum_list_split]
  have hnil : Set.indicator {l : List S | pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l) [] = Set.indicator B 1 x := by
    by_cases hB : x ∈ B
    · rw [Set.indicator_of_mem (show ([] : List S) ∈ {l : List S | pathEnd x l ∈ B} from
        by simpa using hB), Set.indicator_of_mem hB]
      simp
    · rw [Set.indicator_of_notMem (show ([] : List S) ∉ {l : List S | pathEnd x l ∈ B} from
        by simpa using hB), Set.indicator_of_notMem hB]
  have hcons : ∀ p : S × List S, Set.indicator {l : List S | pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l) (p.1 :: p.2) =
      a * (P x p.1 * Set.indicator {l : List S | pathEnd p.1 l ∈ B}
        (fun l => a ^ l.length * pathWeight P p.1 l) p.2) := by
    rintro ⟨y, l⟩
    by_cases hB : pathEnd y l ∈ B
    · rw [Set.indicator_of_mem (show (y :: l) ∈ {l : List S | pathEnd x l ∈ B} from
        by simpa using hB),
        Set.indicator_of_mem (show l ∈ {l : List S | pathEnd y l ∈ B} from hB)]
      simp only [List.length_cons, pathWeight_cons, pow_succ]
      ring
    · rw [Set.indicator_of_notMem (show (y :: l) ∉ {l : List S | pathEnd x l ∈ B} from
        by simpa using hB),
        Set.indicator_of_notMem (show l ∉ {l : List S | pathEnd y l ∈ B} from hB),
        mul_zero, mul_zero]
  have hprod : (∑' p : S × List S, P x p.1 * Set.indicator {l : List S | pathEnd p.1 l ∈ B}
      (fun l => a ^ l.length * pathWeight P p.1 l) p.2) =
      ∑' y : S, ∑' l : List S, P x y * Set.indicator {l : List S | pathEnd y l ∈ B}
        (fun l => a ^ l.length * pathWeight P y l) l := by
    rw [← ENNReal.tsum_prod (f := fun y l => P x y * Set.indicator {l : List S | pathEnd y l ∈ B}
      (fun l => a ^ l.length * pathWeight P y l) l)]
  have hinner : (∑' y : S, ∑' l : List S, P x y * Set.indicator {l : List S | pathEnd y l ∈ B}
      (fun l => a ^ l.length * pathWeight P y l) l) =
      ∑' y : S, P x y * greenMass P a y B :=
    tsum_congr fun y => by rw [ENNReal.tsum_mul_left, greenMass]
  rw [hnil, tsum_congr hcons, ENNReal.tsum_mul_left, hprod, hinner]

theorem one_le_greenMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {x : S} {B : Set S} (hx : x ∈ B) :
    1 ≤ greenMass P a x B := by
  classical
  rw [greenMass]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ([] : List S))
  rw [Set.indicator_of_mem (show ([] : List S) ∈ {l : List S | pathEnd x l ∈ B} from
    by simpa using hx)]
  simp

/-- Discounted occupation is bounded by the geometric series of the discount. -/
theorem greenMass_le_geometric (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1) (a : ℝ≥0∞)
    (x : S) (B : Set S) : greenMass P a x B ≤ ∑' n : ℕ, a ^ n := by
  classical
  have hle : greenMass P a x B ≤ ∑' l : List S, a ^ l.length * pathWeight P x l := by
    rw [greenMass]
    refine ENNReal.tsum_le_tsum fun l => ?_
    by_cases hB : pathEnd x l ∈ B
    · rw [Set.indicator_of_mem (show l ∈ {l : List S | pathEnd x l ∈ B} from hB)]
    · rw [Set.indicator_of_notMem (show l ∉ {l : List S | pathEnd x l ∈ B} from hB)]
      exact bot_le
  refine le_trans hle (le_of_eq ?_)
  rw [tsum_list_regroup (fun l => a ^ l.length * pathWeight P x l)]
  refine tsum_congr fun n => ?_
  have hval : ∀ l : {l : List S // l.length = n},
      a ^ (l : List S).length * pathWeight P x (l : List S) =
        a ^ n * pathWeight P x (l : List S) := by
    rintro ⟨l, rfl⟩; rfl
  have hlevel : (∑' l : {l : List S // l.length = n}, pathWeight P x (l : List S)) =
      levelMass P x n := tsum_subtype {l : List S | l.length = n} (fun l => pathWeight P x l)
  rw [tsum_congr hval, ENNReal.tsum_mul_left, hlevel, levelMass_eq_one P hP, mul_one]

/-- The discounted entrance mass is countably additive over the target points. -/
theorem tsum_entranceMass_singleton (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S)
    (B : Set S) :
    (∑' z : S, entranceMass P a A x ({z} ∩ B)) = entranceMass P a A x B := by
  classical
  have hswap : (∑' z : S, entranceMass P a A x ({z} ∩ B)) =
      ∑' l : List S, ∑' z : S, Set.indicator {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ ({z} ∩ B)}
        (fun l => a ^ l.length * pathWeight P x l) l := by
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun z => by rw [entranceMass]
  rw [hswap, entranceMass]
  refine tsum_congr fun l => ?_
  by_cases hFE : FirstEntrance A x l ∧ pathEnd x l ∈ B
  · rw [Set.indicator_of_mem (show l ∈ {l : List S |
      FirstEntrance A x l ∧ pathEnd x l ∈ B} from hFE)]
    have hsingle : (∑' z : S, Set.indicator {l : List S |
        FirstEntrance A x l ∧ pathEnd x l ∈ (({z} : Set S) ∩ B)}
        (fun l => a ^ l.length * pathWeight P x l) l) =
        Set.indicator {l : List S |
          FirstEntrance A x l ∧ pathEnd x l ∈ (({pathEnd x l} : Set S) ∩ B)}
          (fun l => a ^ l.length * pathWeight P x l) l :=
      tsum_eq_single (pathEnd x l) fun z hz =>
        Set.indicator_of_notMem (fun hc => hz hc.2.1.symm) _
    rw [hsingle, Set.indicator_of_mem (show l ∈ {l : List S |
      FirstEntrance A x l ∧ pathEnd x l ∈ (({pathEnd x l} : Set S) ∩ B)} from
        ⟨hFE.1, rfl, hFE.2⟩)]
  · rw [Set.indicator_of_notMem (show l ∉ {l : List S |
      FirstEntrance A x l ∧ pathEnd x l ∈ B} from hFE)]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    exact Set.indicator_of_notMem (fun hc => hFE ⟨hc.1, hc.2.2⟩) _

end GreenBounds

section Sandwich

variable {S : Type*} [Countable S]

theorem entranceMass_singleton_eq_zero (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S)
    {z : S} (hz : z ∉ A) : entranceMass P a A x {z} = 0 := by
  classical
  rw [entranceMass]
  refine ENNReal.tsum_eq_zero.mpr fun l => ?_
  refine Set.indicator_of_notMem (fun hc => ?_) _
  exact hz (hc.2 ▸ hc.1.1)

theorem tsum_entranceMass_singleton_self (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (x : S) :
    (∑' z : S, entranceMass P a A x {z}) = entranceMass P a A x A := by
  classical
  rw [← tsum_entranceMass_singleton P a A x A]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ A
  · congr 1
    exact (Set.inter_eq_left.mpr (by simpa using hz)).symm
  · rw [entranceMass_singleton_eq_zero P a A x hz]
    refine (ENNReal.tsum_eq_zero.mpr fun l => ?_).symm
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact hz (hc.2.1 ▸ hc.1.1)

/-- **Stopped occupation upper bound.**  A uniform bound on the occupation from the target
transfers to the occupation from any state through the entrance mass. -/
theorem greenMass_le_mul_entranceMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A B : Set S} (hBA : B ⊆ A)
    (x : S) {g : ℝ≥0∞} (hg : ∀ z ∈ A, greenMass P a z B ≤ g) :
    greenMass P a x B ≤ g * entranceMass P a A x A := by
  rw [greenMass_eq_tsum_entranceMass P a A B hBA x, ← tsum_entranceMass_singleton_self,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ A
  · rw [mul_comm g]
    exact mul_le_mul_right (hg z hz) _
  · rw [entranceMass_singleton_eq_zero P a A x hz, zero_mul, mul_zero]

/-- **Stopped occupation lower bound.** -/
theorem mul_entranceMass_le_greenMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A B : Set S} (hBA : B ⊆ A)
    (x : S) {g : ℝ≥0∞} (hg : ∀ z ∈ A, g ≤ greenMass P a z B) :
    g * entranceMass P a A x A ≤ greenMass P a x B := by
  rw [greenMass_eq_tsum_entranceMass P a A B hBA x, ← tsum_entranceMass_singleton_self,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : z ∈ A
  · rw [mul_comm g]
    exact mul_le_mul_right (hg z hz) _
  · rw [entranceMass_singleton_eq_zero P a A x hz, zero_mul, mul_zero]

/-- **Green--entrance equivalence.**  Discounted occupation of a target is squeezed between the
discounted entrance mass and its geometric multiple. -/
theorem entranceMass_le_greenMass_le (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1)
    (a : ℝ≥0∞) (A : Set S) (x : S) :
    entranceMass P a A x A ≤ greenMass P a x A ∧
      greenMass P a x A ≤ (∑' n : ℕ, a ^ n) * entranceMass P a A x A := by
  constructor
  · have := mul_entranceMass_le_greenMass P a (subset_refl A) x
      (g := 1) (fun z hz => one_le_greenMass P a hz)
    simpa using this
  · exact greenMass_le_mul_entranceMass P a (subset_refl A) x
      (fun z _ => greenMass_le_geometric P hP a z A)

end Sandwich

section ReturnKernel

variable {S : Type*} [Countable S]

/-- Discounted first positive return kernel of the target set. -/
noncomputable def returnMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (z : S) (B : Set S) :
    ℝ≥0∞ :=
  a * ∑' y : S, P z y * entranceMass P a A y B

/-- **Return contraction.**  The discounted return kernel has total mass at most the discount. -/
theorem returnMass_le (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1) {a : ℝ≥0∞} (ha : a ≤ 1)
    (A : Set S) (z : S) : returnMass P a A z A ≤ a := by
  rw [returnMass]
  calc a * ∑' y : S, P z y * entranceMass P a A y A
      ≤ a * ∑' y : S, P z y * 1 := by
        refine mul_le_mul_right (ENNReal.tsum_le_tsum fun y => ?_) _
        exact mul_le_mul_right (entranceMass_le_one P hP ha A y A) _
    _ = a := by simp [hP z]

/-- **Entrance--return resolvent equation.**  From the target, discounted occupation is the present
visit plus one discounted return followed by occupation. -/
theorem greenMass_eq_add_tsum_returnMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) {A B : Set S}
    (hBA : B ⊆ A) (z : S) :
    greenMass P a z B =
      Set.indicator B 1 z + ∑' w : S, returnMass P a A z {w} * greenMass P a w B := by
  classical
  rw [greenMass_step P a z B]
  congr 1
  have hstep : ∀ y : S, greenMass P a y B =
      ∑' w : S, entranceMass P a A y {w} * greenMass P a w B := fun y =>
    greenMass_eq_tsum_entranceMass P a A B hBA y
  have h1 : (∑' y : S, P z y * greenMass P a y B) =
      ∑' y : S, ∑' w : S, P z y * entranceMass P a A y {w} * greenMass P a w B := by
    refine tsum_congr fun y => ?_
    rw [hstep y, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun w => by ring
  have h2 : (∑' y : S, ∑' w : S, P z y * entranceMass P a A y {w} * greenMass P a w B) =
      ∑' w : S, ∑' y : S, P z y * entranceMass P a A y {w} * greenMass P a w B :=
    ENNReal.tsum_comm
  have h3 : ∀ w : S, (a * ∑' y : S, P z y * entranceMass P a A y {w}) * greenMass P a w B =
      a * ∑' y : S, P z y * entranceMass P a A y {w} * greenMass P a w B := by
    intro w
    rw [mul_assoc, ← ENNReal.tsum_mul_right]
  have hswap : (a * ∑' y : S, P z y * greenMass P a y B) =
      ∑' w : S, (a * ∑' y : S, P z y * entranceMass P a A y {w}) * greenMass P a w B := by
    rw [h1, h2, tsum_congr h3, ← ENNReal.tsum_mul_left]
  rw [hswap]
  exact tsum_congr fun w => by rw [returnMass]

end ReturnKernel

section Singleton

variable {S : Type*} [Countable S]

theorem returnMass_singleton_eq_zero (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A : Set S) (z : S)
    {w : S} (hw : w ∉ A) : returnMass P a A z {w} = 0 := by
  rw [returnMass]
  refine mul_eq_zero.mpr (Or.inr ?_)
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  rw [entranceMass_singleton_eq_zero P a A y hw, mul_zero]

/-- **Preparation--recurrence factorization.**  Occupation of a single target point is entrance
into it times occupation from it. -/
theorem greenMass_singleton_eq (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (x y : S) :
    greenMass P a x {y} = entranceMass P a {y} x {y} * greenMass P a y {y} := by
  rw [greenMass_eq_tsum_entranceMass P a {y} {y} (subset_refl _) x]
  refine tsum_eq_single y fun z hz => ?_
  rw [entranceMass_singleton_eq_zero P a {y} x (show z ∉ ({y} : Set S) from hz), zero_mul]

/-- The occupation of a single target point from itself satisfies the exact return equation. -/
theorem greenMass_self_eq (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (y : S) :
    greenMass P a y {y} = 1 + returnMass P a {y} y {y} * greenMass P a y {y} := by
  classical
  have hsingle : (∑' w : S, returnMass P a {y} y {w} * greenMass P a w {y}) =
      returnMass P a {y} y {y} * greenMass P a y {y} :=
    tsum_eq_single y fun w hw => by
      rw [returnMass_singleton_eq_zero P a {y} y (show w ∉ ({y} : Set S) from hw), zero_mul]
  have hind : Set.indicator ({y} : Set S) (1 : S → ℝ≥0∞) y = 1 := by
    rw [Set.indicator_of_mem (show y ∈ ({y} : Set S) from rfl)]
    simp
  conv_lhs => rw [greenMass_eq_add_tsum_returnMass P a (subset_refl ({y} : Set S)) y]
  rw [hsingle, hind]

/-- **Closed preparation--recurrence product.**  Below the dependence radius the occupation of a
single point is entrance divided by one minus the return mass. -/
theorem greenMass_singleton_eq_div (P : S → S → ℝ≥0∞) (hP : ∀ x, ∑' y : S, P x y = 1)
    {a : ℝ≥0∞} (ha : a < 1) (x y : S) :
    greenMass P a x {y} =
      entranceMass P a {y} x {y} / (1 - returnMass P a {y} y {y}) := by
  have hgeom : (∑' n : ℕ, a ^ n) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt ha).ne'
  have hfin : greenMass P a y {y} ≠ ⊤ :=
    ne_top_of_le_ne_top hgeom (greenMass_le_geometric P hP a y {y})
  have hR : returnMass P a {y} y {y} ≤ a := returnMass_le P hP ha.le {y} y
  have hRlt : returnMass P a {y} y {y} < 1 := lt_of_le_of_lt hR ha
  have hRtop : returnMass P a {y} y {y} ≠ ⊤ := ne_top_of_lt hRlt
  have hRG : returnMass P a {y} y {y} * greenMass P a y {y} ≠ ⊤ :=
    ENNReal.mul_ne_top hRtop hfin
  have hself := greenMass_self_eq P a y
  have hmul : greenMass P a y {y} * (1 - returnMass P a {y} y {y}) = 1 := by
    rw [ENNReal.mul_sub (fun _ _ => hfin), mul_one, mul_comm (greenMass P a y {y})]
    nth_rewrite 1 [hself]
    exact ENNReal.add_sub_cancel_right hRG
  have hsolve : greenMass P a y {y} = (1 - returnMass P a {y} y {y})⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left hmul
  rw [greenMass_singleton_eq, hsolve, div_eq_mul_inv]

end Singleton

end GaloisForLFunctions.RHTower
