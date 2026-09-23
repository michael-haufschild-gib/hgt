import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.AdditiveEnergy

/-!
# Grynkiewicz's Kneser-type extension of Pollard's theorem: statement and first reductions

Grynkiewicz's theorem (*On extending Pollard's theorem for `t`-representable sums*,
Israel J. Math. 177 (2010) 413–439) states that for finite nonempty `A, B` in a commutative group
with `#A, #B ≥ t`, either the *weak Pollard bound* `PollardWeak` holds, or there are large subsets
`A' ⊆ A`, `B' ⊆ B` with `A' ·_t B' = A' · B' = A ·_t B` together with a Kneser-type stabiliser
bound — the alternative `PollardStruct`.

This file fixes the statement, records the elementary evaluations of `repSum` that the induction
needs, and defines the lexicographic measure
`(repSum, 2·repSum − (#A + #B), min (#A) (#B))` on which the induction runs.  The middle component
is a natural number because `#A + #B ≤ 2·#(A · B) ≤ 2·repSum`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The number of elements discarded when passing from `(A, B)` to subsets `(A', B')`. -/
def defect (A A' B B' : Finset G) : ℕ := (A \ A').card + (B \ B').card

/-- The number of `H`-holes in `A'` and `B'`. -/
def holes (H A' B' : Finset G) : ℕ := ((A' * H) \ A').card + ((B' * H) \ B').card

/-- The weak Pollard bound `∑_{i=1}^t #(A ·_i B) ≥ t#A + t#B − 2t² + 1`. -/
def PollardWeak (A B : Finset G) (t : ℕ) : Prop :=
  t * A.card + t * B.card + 1 ≤ repSum A B t + 2 * t ^ (2 : ℕ)

/-- The structural alternative of Grynkiewicz's theorem. -/
def PollardStruct (A B : Finset G) (t : ℕ) : Prop :=
  ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧ defect A A' B B' + 1 ≤ t
    ∧ repSet A' B' t = A' * B' ∧ A' * B' = repSet A B t
    ∧ t * A.card + t * B.card
        + (t - defect A A' B B') * holes (mulStab (repSet A B t)) A' B'
      ≤ repSum A B t + (t - defect A A' B B') * (mulStab (repSet A B t)).card
        + t * defect A A' B B'

/-! ### Basic evaluations of `repSum` -/

/-- When no element has more than `t` representations, `∑_{i=1}^t #(A ·_i B) = #A · #B`. -/
theorem repSum_eq_of_rep_le (A B : Finset G) (t : ℕ) (h : ∀ c : G, rep A B c ≤ t) :
    repSum A B t = A.card * B.card := by
  rw [repSum_eq_sum_min, ← sum_rep A B]
  exact Finset.sum_congr rfl (fun c _ => min_eq_left (h c))

/-- The base case of Grynkiewicz's induction: if `#B = t` the weak bound holds. -/
theorem pollardWeak_of_card_eq (A B : Finset G) (t : ℕ) (ht : 1 ≤ t) (hB : B.card = t) :
    PollardWeak A B t := by
  have hle : ∀ c : G, rep A B c ≤ t := by
    intro c
    have := rep_le_card_right A B c
    omega
  have hval : repSum A B t = A.card * B.card := repSum_eq_of_rep_le A B t hle
  rw [PollardWeak, hval, hB]
  nlinarith [ht]

/-- `repSum` is monotone in the sets. -/
theorem repSum_mono {A A' B B' : Finset G} (hA : A' ⊆ A) (hB : B' ⊆ B) (t : ℕ) :
    repSum A' B' t ≤ repSum A B t := by
  rw [repSum, repSum]
  refine Finset.sum_le_sum (fun i _ => Finset.card_le_card ?_)
  intro g hg
  rw [mem_repSet] at hg ⊢
  exact le_trans hg (rep_mono hA hB g)

/-- For `t ≥ 1`, the product set is one of the summands, so `#(A · B) ≤ repSum`. -/
theorem card_mul_le_repSum (A B : Finset G) (t : ℕ) (ht : 1 ≤ t) :
    (A * B).card ≤ repSum A B t := by
  rw [repSum]
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_refl 1, ht⟩
  calc (A * B).card = (repSet A B 1).card := by rw [repSet_one]
    _ ≤ ∑ i ∈ Finset.Icc 1 t, (repSet A B i).card :=
        Finset.single_le_sum (f := fun i => (repSet A B i).card) (fun i _ => Nat.zero_le _) hmem

omit [Fintype G] in
/-- `#A + #B ≤ 2 · #(A · B)`, so the sum of the cardinalities is bounded by twice `repSum`. -/
theorem card_add_card_le_two_mul_card_mul {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ 2 * (A * B).card := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have h1 : A.card ≤ (A * B).card := by
    have : A * {b} ⊆ A * B := mul_subset_mul_left (Finset.singleton_subset_iff.2 hb)
    calc A.card = (A * ({b} : Finset G)).card := (Finset.card_mul_singleton A b).symm
      _ ≤ (A * B).card := Finset.card_le_card this
  have h2 : B.card ≤ (A * B).card := by
    have : ({a} : Finset G) * B ⊆ A * B := mul_subset_mul_right (Finset.singleton_subset_iff.2 ha)
    calc B.card = (({a} : Finset G) * B).card := by
          rw [Finset.singleton_mul, Finset.card_smul_finset]
      _ ≤ (A * B).card := Finset.card_le_card this
  omega


/-- Every one of the `t` summands dominates the `t`-representable set, so
`t · #(A ·_t B) ≤ ∑_{i=1}^t #(A ·_i B)`. -/
theorem mul_card_repSet_le_repSum (A B : Finset G) (t : ℕ) :
    t * (repSet A B t).card ≤ repSum A B t := by
  rw [repSum]
  calc t * (repSet A B t).card
      = ∑ _i ∈ Finset.Icc 1 t, (repSet A B t).card := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        simp
    _ ≤ ∑ i ∈ Finset.Icc 1 t, (repSet A B i).card := by
        refine Finset.sum_le_sum (fun i hi => Finset.card_le_card ?_)
        exact repSet_antitone A B (Finset.mem_Icc.1 hi).2

/-- The middle component of Grynkiewicz's induction measure is a natural number. -/
theorem card_add_card_le_two_mul_repSum {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (t : ℕ) (ht : 1 ≤ t) : A.card + B.card ≤ 2 * repSum A B t := by
  have h1 := card_add_card_le_two_mul_card_mul hA hB
  have h2 := card_mul_le_repSum A B t ht
  omega

/-- Grynkiewicz's induction measure: `repSum` first, then `#A + #B` increasing, then
`min (#A) (#B)` decreasing. -/
def pollardMeasure (A B : Finset G) (t : ℕ) : ℕ × ℕ × ℕ :=
  (repSum A B t, 2 * repSum A B t - (A.card + B.card), min A.card B.card)

end GaloisForLFunctions.HTGeometry.AddComb
