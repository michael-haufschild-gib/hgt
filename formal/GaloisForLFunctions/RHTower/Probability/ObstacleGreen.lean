import GaloisForLFunctions.RHTower.DiscreteMarkovRenewal

/-!
# Obstacle removal and unrestricted first-entrance renewal

A path ending anywhere either avoids an obstacle or splits uniquely at its
first visit to that obstacle. Consequently the full Green mass is the sum of
the killed Green mass and entrance mass composed with the unrestricted Green
mass. This extends the existing renewal identity beyond targets contained in
the entrance set. It is the discrete path-sum counterpart of the strong Markov
and obstacle comparison arguments of Ammari–Thalhammer
(https://arxiv.org/abs/2611.16978, §6). All identities hold for arbitrary
nonnegative kernels, including infinite masses, without stochastic assumptions.
-/

open scoped ENNReal

namespace GaloisForLFunctions.RHTower

variable {S : Type*}

/-- The path visits the obstacle at some time, including its initial time. -/
def PathHits (A : Set S) (x : S) (l : List S) : Prop :=
  ∃ k ≤ l.length, pathEnd x (l.take k) ∈ A

private theorem firstEntranceTime_spec_of_hits {A : Set S} {x : S} {l : List S}
    (h : PathHits A x l) :
    firstEntranceTime A x l ≤ l.length ∧
      FirstEntrance A x (l.take (firstEntranceTime A x l)) := by
  classical
  obtain ⟨k, hk, hm⟩ := h
  have hex : ∃ j, pathEnd x (l.take j) ∈ A := ⟨k, hm⟩
  have hle : Nat.find hex ≤ l.length := (Nat.find_le hm).trans hk
  rw [firstEntranceTime, dif_pos hex]
  refine ⟨hle, Nat.find_spec hex, ?_⟩
  intro j hj
  rw [List.length_take, min_eq_left hle] at hj
  rw [List.take_take, min_eq_left hj.le]
  exact Nat.find_min hex hj

/-- First-entrance splitting remains bijective when the endpoint lies outside the obstacle. -/
noncomputable def entranceHitSplit (A B : Set S) (x : S) :
    {pq : List S × List S //
        FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B} ≃
      {l : List S // PathHits A x l ∧ pathEnd x l ∈ B} where
  toFun pq := ⟨pq.1.1 ++ pq.1.2, by
    constructor
    · refine ⟨pq.1.1.length, by simp, ?_⟩
      rw [List.take_left]
      exact pq.2.1.1
    · rw [pathEnd_append]
      exact pq.2.2⟩
  invFun l := ⟨(l.1.take (firstEntranceTime A x l.1), l.1.drop (firstEntranceTime A x l.1)), by
    refine ⟨(firstEntranceTime_spec_of_hits l.2.1).2, ?_⟩
    rw [← pathEnd_append, List.take_append_drop]
    exact l.2.2⟩
  left_inv := by
    rintro ⟨⟨p, q⟩, hp, hq⟩
    have hlen := firstEntranceTime_append (q := q) hp
    apply Subtype.ext
    simp only [hlen, List.take_left, List.drop_left]
  right_inv := by
    rintro ⟨l, hl⟩
    exact Subtype.ext (List.take_append_drop _ _)

/-- Occupation contributed by paths surviving the obstacle for their entire duration. -/
noncomputable def avoidingGreen (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) : ℝ≥0∞ :=
  ∑' l : List S, Set.indicator {l : List S | ¬PathHits A x l ∧ pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l) l

/-- Occupation contributed by paths which have visited the obstacle. -/
noncomputable def visitingGreen (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) : ℝ≥0∞ :=
  ∑' l : List S, Set.indicator {l : List S | PathHits A x l ∧ pathEnd x l ∈ B}
    (fun l => a ^ l.length * pathWeight P x l) l

/-- The obstacle partitions the full occupation without subtracting infinite masses. -/
theorem greenMass_eq_avoiding_add_visiting (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) :
    greenMass P a x B = avoidingGreen P a A x B + visitingGreen P a A x B := by
  classical
  rw [greenMass, avoidingGreen, visitingGreen, ← ENNReal.tsum_add]
  apply tsum_congr
  intro l
  by_cases hh : PathHits A x l <;> by_cases hb : pathEnd x l ∈ B <;>
    simp [Set.indicator, hh, hb]

/-- Visiting occupation factors through the first entrance point. -/
theorem visitingGreen_eq_entrance [Countable S] (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) :
    visitingGreen P a A x B =
      ∑' z : S, entranceMass P a A x {z} * greenMass P a z B := by
  have hsrc : (∑' pq : List S × List S, splitWeight P a A B x pq) =
      ∑' pq : {pq : List S × List S //
          FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B},
        a ^ pq.1.1.length * pathWeight P x pq.1.1 *
          (a ^ pq.1.2.length * pathWeight P (pathEnd x pq.1.1) pq.1.2) :=
    (tsum_subtype {pq : List S × List S |
      FirstEntrance A x pq.1 ∧ pathEnd (pathEnd x pq.1) pq.2 ∈ B}
      (fun pq => a ^ pq.1.length * pathWeight P x pq.1 *
        (a ^ pq.2.length * pathWeight P (pathEnd x pq.1) pq.2))).symm
  have htgt : visitingGreen P a A x B =
      ∑' l : {l : List S // PathHits A x l ∧ pathEnd x l ∈ B},
        a ^ l.1.length * pathWeight P x l.1 :=
    (tsum_subtype {l : List S | PathHits A x l ∧ pathEnd x l ∈ B}
      (fun l => a ^ l.length * pathWeight P x l)).symm
  rw [← tsum_splitWeight_eq_tsum_entranceMass, hsrc, htgt,
    ← (entranceHitSplit A B x).tsum_eq
      (fun l : {l : List S // PathHits A x l ∧ pathEnd x l ∈ B} =>
        a ^ l.1.length * pathWeight P x l.1)]
  apply tsum_congr
  rintro ⟨⟨p, q⟩, hp, hq⟩
  change a ^ (p ++ q).length * pathWeight P x (p ++ q) =
    a ^ p.length * pathWeight P x p * (a ^ q.length * pathWeight P (pathEnd x p) q)
  rw [List.length_append, pow_add, pathWeight_append]
  ring

/-- Exact obstacle-removal identity for arbitrary endpoints and arbitrary nonnegative kernels. -/
theorem greenMass_obstacle_decomposition [Countable S] (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) :
    greenMass P a x B = avoidingGreen P a A x B +
      ∑' z : S, entranceMass P a A x {z} * greenMass P a z B := by
  rw [greenMass_eq_avoiding_add_visiting P a A, visitingGreen_eq_entrance]

/-- Killing more paths can only decrease occupation. -/
theorem avoidingGreen_union_le (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A C : Set S) (x : S) (B : Set S) :
    avoidingGreen P a (A ∪ C) x B ≤ avoidingGreen P a A x B := by
  classical
  apply ENNReal.tsum_le_tsum
  intro l
  by_cases h : ¬PathHits (A ∪ C) x l ∧ pathEnd x l ∈ B
  · have hA : ¬PathHits A x l := by
      rintro ⟨k, hk, hm⟩
      exact h.1 ⟨k, hk, Or.inl hm⟩
    simp [Set.indicator, h, hA]
  · simp [Set.indicator, h]

/-- Occupation after the first entrance is always bounded by total occupation. -/
theorem entrance_green_le_greenMass [Countable S] (P : S → S → ℝ≥0∞) (a : ℝ≥0∞)
    (A : Set S) (x : S) (B : Set S) :
    (∑' z : S, entranceMass P a A x {z} * greenMass P a z B) ≤ greenMass P a x B := by
  rw [greenMass_obstacle_decomposition P a A]
  exact le_add_left le_rfl

#print axioms greenMass_obstacle_decomposition
#print axioms avoidingGreen_union_le
#print axioms entrance_green_le_greenMass

end GaloisForLFunctions.RHTower
