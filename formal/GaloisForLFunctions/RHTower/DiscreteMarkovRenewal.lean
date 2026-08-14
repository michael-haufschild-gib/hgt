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
def pathWeight (P : S → S → ℝ≥0∞) : S → List S → ℝ≥0∞
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

theorem tsum_splitWeight_eq_greenMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S) (hBA : B ⊆ A)
    (x : S) :
    (∑' pq : List S × List S, splitWeight P a A B x pq) = greenMass P a x B := by
  classical
  have hsub : (∑' pq : List S × List S, splitWeight P a A B x pq) =
      ∑' pq : {pq : List S × List S //
          FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B},
        a ^ (pq : List S × List S).1.length * pathWeight P x (pq : List S × List S).1 *
          (a ^ (pq : List S × List S).2.length *
            pathWeight P (pathEnd x (pq : List S × List S).1) (pq : List S × List S).2) := by
    rw [splitWeight]
    exact (tsum_subtype _ _).symm
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
    greenMass, tsum_subtype]

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
    · rw [Set.indicator_of_mem hp]
      have hterm : ∀ q : List S, splitWeight P a A B x (p, q) =
          (a ^ p.length * pathWeight P x p) *
            Set.indicator {q : List S | pathEnd (pathEnd x p) q ∈ B}
              (fun q => a ^ q.length * pathWeight P (pathEnd x p) q) q := by
        intro q
        by_cases hq : pathEnd (pathEnd x p) q ∈ B
        · rw [splitWeight, Set.indicator_of_mem (show (p, q) ∈ _ from ⟨hp, hq⟩),
            Set.indicator_of_mem hq]
        · rw [splitWeight, Set.indicator_of_notMem (fun hc => hq hc.2),
            Set.indicator_of_notMem hq, mul_zero]
      rw [tsum_congr hterm, ENNReal.tsum_mul_left, greenMass]
    · have hterm : ∀ q : List S, splitWeight P a A B x (p, q) = 0 := by
        intro q
        rw [splitWeight, Set.indicator_of_notMem (fun hc => hp hc.1)]
      rw [tsum_congr hterm, tsum_zero, Set.indicator_of_notMem hp, zero_mul]
  have hright : ∀ z : S, entranceMass P a A x {z} * greenMass P a z B =
      ∑' p : List S, Set.indicator {p : List S | FirstEntrance A x p ∧ pathEnd x p = z}
        (fun p => a ^ p.length * pathWeight P x p) p * greenMass P a z B := by
    intro z
    rw [entranceMass, ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_prod, tsum_congr hinner, tsum_congr hright, ENNReal.tsum_comm]
  refine tsum_congr fun p => ?_
  by_cases hp : FirstEntrance A x p
  · rw [Set.indicator_of_mem hp,
      tsum_eq_single (pathEnd x p) (fun z hz => ?_)]
    · rw [Set.indicator_of_mem (show p ∈ _ from ⟨hp, rfl⟩)]
    · rw [Set.indicator_of_notMem (fun hc => hz (hc.2.symm)), zero_mul]
  · rw [Set.indicator_of_notMem hp, zero_mul]
    refine (tsum_eq_zero_iff ENNReal.summable).mpr fun z => ?_
    rw [Set.indicator_of_notMem (fun hc => hp hc.1), zero_mul]

/-- **First-entrance decomposition.**  Discounted occupation of a target inside `A` is discounted
entrance into `A` followed by unrestricted discounted continuation. -/
theorem greenMass_eq_tsum_entranceMass (P : S → S → ℝ≥0∞) (a : ℝ≥0∞) (A B : Set S) (hBA : B ⊆ A)
    (x : S) :
    greenMass P a x B = ∑' z : S, entranceMass P a A x {z} * greenMass P a z B := by
  rw [← tsum_splitWeight_eq_greenMass P a A B hBA x,
    tsum_splitWeight_eq_tsum_entranceMass P a A B x]

end GreenMass

end GaloisForLFunctions.RHTower
