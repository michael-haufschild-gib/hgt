import Mathlib

open scoped BigOperators

noncomputable section

namespace HTGeometry

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A computational-basis Rydberg configuration certified to satisfy the blockade graph. -/
structure RydbergIndependentConfiguration where
  sites : Finset V
  independent : G.IsIndepSet (sites : Set V)

noncomputable instance : Fintype (RydbergIndependentConfiguration G) :=
  Fintype.ofInjective (fun C => C.sites) (by
    intro C D h
    cases C
    cases D
    simp_all)

namespace RydbergIndependentConfiguration

variable {G}

/-- Occupied atoms of a certified blockade configuration. -/
abbrev OccupiedAtom (C : RydbergIndependentConfiguration G) :=
  {v : V // v ∈ C.sites}

/-- Delete one atom. Independence is preserved by construction. -/
def delete (C : RydbergIndependentConfiguration G) (v : V) :
    RydbergIndependentConfiguration G where
  sites := C.sites.erase v
  independent := by
    apply Set.Pairwise.mono _ C.independent
    intro x hx
    exact Finset.erase_subset v C.sites hx

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem sites_delete (C : RydbergIndependentConfiguration G) (v : V) :
    (C.delete v).sites = C.sites.erase v := rfl

omit [Fintype V] [DecidableRel G.Adj] in
theorem delete_subset (C : RydbergIndependentConfiguration G) (v : V) :
    (C.delete v).sites ⊆ C.sites := by
  exact Finset.erase_subset v C.sites

omit [Fintype V] [DecidableRel G.Adj] in
/-- Deleting a certified occupied atom lowers cardinality by exactly one. -/
theorem card_delete_occupied (C : RydbergIndependentConfiguration G)
    (v : C.OccupiedAtom) :
    (C.delete v).sites.card + 1 = C.sites.card := by
  exact Finset.card_erase_add_one v.property

omit [Fintype V] [DecidableRel G.Adj] in
/-- Number-score loss from deleting every possible occupied atom once equals initial score. -/
theorem sum_single_decay_cardinality_damage (C : RydbergIndependentConfiguration G) :
    ∑ v : C.OccupiedAtom,
        ((C.sites.card : ℝ) - ((C.delete v).sites.card : ℝ)) =
      (C.sites.card : ℝ) := by
  classical
  have hdamage (v : C.OccupiedAtom) :
      (C.sites.card : ℝ) - ((C.delete v).sites.card : ℝ) = 1 := by
    have h : ((C.delete v).sites.card : ℝ) + 1 = (C.sites.card : ℝ) := by
      exact_mod_cast card_delete_occupied C v
    linarith
  simp_rw [hdamage]
  simp

/-- Approximation score with a manifestly nonzero benchmark denominator. -/
def normalizedScore (C : RydbergIndependentConfiguration G) (benchmark : ℕ) : ℝ :=
  (C.sites.card : ℝ) / ((benchmark : ℝ) + 1)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Total one-decay damage for the normalized MIS score is exactly the original score. -/
theorem sum_single_decay_normalizedScore_damage
    (C : RydbergIndependentConfiguration G) (benchmark : ℕ) :
    ∑ v : C.OccupiedAtom,
        (C.normalizedScore benchmark - (C.delete v).normalizedScore benchmark) =
      C.normalizedScore benchmark := by
  classical
  have hdamage (v : C.OccupiedAtom) :
      C.normalizedScore benchmark - (C.delete v).normalizedScore benchmark =
        1 / ((benchmark : ℝ) + 1) := by
    have h : ((C.delete v).sites.card : ℝ) + 1 = (C.sites.card : ℝ) := by
      exact_mod_cast card_delete_occupied C v
    simp only [normalizedScore]
    have hden : (benchmark : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    linarith
  simp_rw [hdamage]
  simp [normalizedScore, div_eq_mul_inv]

end RydbergIndependentConfiguration

/-- A graph edge packaged as a blockade pair, eliminating adjacency hypotheses downstream. -/
structure RydbergBlockedPair where
  left : V
  right : V
  blocked : G.Adj left right

/-- A triple of sites with pairwise blockade. -/
structure RydbergBlockedTriple where
  first : V
  second : V
  third : V
  first_second : G.Adj first second
  first_third : G.Adj first third
  second_third : G.Adj second third

/-- Classical Rydberg occupation indicator. -/
def rydbergOccupationIndicator
    (C : RydbergIndependentConfiguration G) (v : V) : ℝ :=
  if v ∈ C.sites then 1 else 0

/-- Ising readout associated with Rydberg occupation, `Z = 1 - 2n`. -/
def rydbergSpinIndicator
    (C : RydbergIndependentConfiguration G) (v : V) : ℝ :=
  1 - 2 * rydbergOccupationIndicator G C v

omit [Fintype V] [DecidableRel G.Adj] in
/-- Hard blockade makes simultaneous occupation of an edge identically zero. -/
theorem rydbergOccupationIndicator_mul_blocked_eq_zero
    (C : RydbergIndependentConfiguration G) (e : RydbergBlockedPair G) :
    rydbergOccupationIndicator G C e.left *
      rydbergOccupationIndicator G C e.right = 0 := by
  by_cases hl : e.left ∈ C.sites
  · have hr : e.right ∉ C.sites := by
      intro hr
      exact (C.independent hl hr e.blocked.ne) e.blocked
    simp [rydbergOccupationIndicator, hl, hr]
  · simp [rydbergOccupationIndicator, hl]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Three pairwise-blockaded sites have no joint occupation. -/
theorem rydbergOccupationIndicator_triple_blocked_eq_zero
    (C : RydbergIndependentConfiguration G) (t : RydbergBlockedTriple G) :
    rydbergOccupationIndicator G C t.first *
        rydbergOccupationIndicator G C t.second *
      rydbergOccupationIndicator G C t.third = 0 := by
  rw [mul_assoc, rydbergOccupationIndicator_mul_blocked_eq_zero G C
    ⟨t.second, t.third, t.second_third⟩, mul_zero]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Pointwise Ising product on a blockaded pair. -/
theorem rydbergSpinIndicator_mul_blocked
    (C : RydbergIndependentConfiguration G) (e : RydbergBlockedPair G) :
    rydbergSpinIndicator G C e.left * rydbergSpinIndicator G C e.right =
      1 - 2 * rydbergOccupationIndicator G C e.left -
        2 * rydbergOccupationIndicator G C e.right := by
  have h := rydbergOccupationIndicator_mul_blocked_eq_zero G C e
  simp only [rydbergSpinIndicator]
  calc
    (1 - 2 * rydbergOccupationIndicator G C e.left) *
        (1 - 2 * rydbergOccupationIndicator G C e.right) =
      1 - 2 * rydbergOccupationIndicator G C e.left -
        2 * rydbergOccupationIndicator G C e.right +
        4 * (rydbergOccupationIndicator G C e.left *
          rydbergOccupationIndicator G C e.right) := by ring
    _ = 1 - 2 * rydbergOccupationIndicator G C e.left -
        2 * rydbergOccupationIndicator G C e.right := by rw [h]; ring

omit [Fintype V] [DecidableRel G.Adj] in
/-- Pointwise Ising product on three mutually blockaded sites. -/
theorem rydbergSpinIndicator_triple_blocked
    (C : RydbergIndependentConfiguration G) (t : RydbergBlockedTriple G) :
    rydbergSpinIndicator G C t.first * rydbergSpinIndicator G C t.second *
        rydbergSpinIndicator G C t.third =
      1 - 2 * rydbergOccupationIndicator G C t.first -
        2 * rydbergOccupationIndicator G C t.second -
        2 * rydbergOccupationIndicator G C t.third := by
  have h12 := rydbergOccupationIndicator_mul_blocked_eq_zero G C
    ⟨t.first, t.second, t.first_second⟩
  have h13 := rydbergOccupationIndicator_mul_blocked_eq_zero G C
    ⟨t.first, t.third, t.first_third⟩
  have h23 := rydbergOccupationIndicator_mul_blocked_eq_zero G C
    ⟨t.second, t.third, t.second_third⟩
  simp only [rydbergSpinIndicator]
  calc
    (1 - 2 * rydbergOccupationIndicator G C t.first) *
        (1 - 2 * rydbergOccupationIndicator G C t.second) *
        (1 - 2 * rydbergOccupationIndicator G C t.third) =
      1 - 2 * rydbergOccupationIndicator G C t.first -
        2 * rydbergOccupationIndicator G C t.second -
        2 * rydbergOccupationIndicator G C t.third +
        4 * (rydbergOccupationIndicator G C t.first *
          rydbergOccupationIndicator G C t.second) +
        4 * (rydbergOccupationIndicator G C t.first *
          rydbergOccupationIndicator G C t.third) +
        4 * (rydbergOccupationIndicator G C t.second *
          rydbergOccupationIndicator G C t.third) -
        8 * (rydbergOccupationIndicator G C t.first *
          rydbergOccupationIndicator G C t.second *
          rydbergOccupationIndicator G C t.third) := by ring
    _ = 1 - 2 * rydbergOccupationIndicator G C t.first -
        2 * rydbergOccupationIndicator G C t.second -
        2 * rydbergOccupationIndicator G C t.third := by
      rw [h12, h13, h23]
      ring

/-- Finite probability law on certified independent configurations. -/
structure RydbergOutcomeLaw where
  weight : RydbergIndependentConfiguration G → ℝ
  nonnegative : ∀ C, 0 ≤ weight C
  normalized : ∑ C, weight C = 1

namespace RydbergOutcomeLaw

variable {G}

def meanOccupation (law : RydbergOutcomeLaw G) (v : V) : ℝ :=
  ∑ C, law.weight C * rydbergOccupationIndicator G C v

def meanPairOccupation (law : RydbergOutcomeLaw G) (u v : V) : ℝ :=
  ∑ C, law.weight C *
    (rydbergOccupationIndicator G C u * rydbergOccupationIndicator G C v)

def meanTripleOccupation (law : RydbergOutcomeLaw G) (u v w : V) : ℝ :=
  ∑ C, law.weight C *
    (rydbergOccupationIndicator G C u * rydbergOccupationIndicator G C v *
      rydbergOccupationIndicator G C w)

def meanSpin (law : RydbergOutcomeLaw G) (v : V) : ℝ :=
  ∑ C, law.weight C * rydbergSpinIndicator G C v

def meanPairSpin (law : RydbergOutcomeLaw G) (u v : V) : ℝ :=
  ∑ C, law.weight C *
    (rydbergSpinIndicator G C u * rydbergSpinIndicator G C v)

def meanTripleSpin (law : RydbergOutcomeLaw G) (u v w : V) : ℝ :=
  ∑ C, law.weight C *
    (rydbergSpinIndicator G C u * rydbergSpinIndicator G C v *
      rydbergSpinIndicator G C w)

def connectedSpinCorrelator
    (law : RydbergOutcomeLaw G) (u v : V) : ℝ :=
  law.meanPairSpin u v - law.meanSpin u * law.meanSpin v

def connectedTripleSpinCorrelator
    (law : RydbergOutcomeLaw G) (u v w : V) : ℝ :=
  law.meanTripleSpin u v w - law.meanPairSpin u v * law.meanSpin w -
    law.meanPairSpin u w * law.meanSpin v -
    law.meanPairSpin v w * law.meanSpin u +
    2 * law.meanSpin u * law.meanSpin v * law.meanSpin w

omit [DecidableRel G.Adj] in
theorem meanOccupation_nonneg (law : RydbergOutcomeLaw G) (v : V) :
    0 ≤ law.meanOccupation v := by
  classical
  apply Finset.sum_nonneg
  intro C _
  apply mul_nonneg (law.nonnegative C)
  by_cases h : v ∈ C.sites <;> simp [rydbergOccupationIndicator, h]

omit [DecidableRel G.Adj] in
theorem meanOccupation_le_one (law : RydbergOutcomeLaw G) (v : V) :
    law.meanOccupation v ≤ 1 := by
  classical
  calc
    law.meanOccupation v ≤ ∑ C, law.weight C * 1 := by
      apply Finset.sum_le_sum
      intro C _
      apply mul_le_mul_of_nonneg_left _ (law.nonnegative C)
      by_cases h : v ∈ C.sites <;> simp [rydbergOccupationIndicator, h]
    _ = 1 := by simpa using law.normalized

omit [DecidableRel G.Adj] in
theorem meanPairOccupation_blocked_eq_zero
    (law : RydbergOutcomeLaw G) (e : RydbergBlockedPair G) :
    law.meanPairOccupation e.left e.right = 0 := by
  classical
  simp [meanPairOccupation, rydbergOccupationIndicator_mul_blocked_eq_zero G]

omit [DecidableRel G.Adj] in
theorem meanTripleOccupation_blocked_eq_zero
    (law : RydbergOutcomeLaw G) (t : RydbergBlockedTriple G) :
    law.meanTripleOccupation t.first t.second t.third = 0 := by
  classical
  simp [meanTripleOccupation, rydbergOccupationIndicator_triple_blocked_eq_zero G]

omit [DecidableRel G.Adj] in
theorem meanSpin_eq_one_sub_two_mul_meanOccupation
    (law : RydbergOutcomeLaw G) (v : V) :
    law.meanSpin v = 1 - 2 * law.meanOccupation v := by
  classical
  rw [meanSpin, meanOccupation]
  calc
    ∑ C, law.weight C * rydbergSpinIndicator G C v =
        ∑ C, (law.weight C -
          2 * (law.weight C * rydbergOccupationIndicator G C v)) := by
      apply Finset.sum_congr rfl
      intro C _
      simp only [rydbergSpinIndicator]
      ring
    _ = (∑ C, law.weight C) - 2 *
        (∑ C, law.weight C * rydbergOccupationIndicator G C v) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 1 - 2 * (∑ C, law.weight C * rydbergOccupationIndicator G C v) := by
      rw [law.normalized]

omit [DecidableRel G.Adj] in
theorem meanPairSpin_blocked
    (law : RydbergOutcomeLaw G) (e : RydbergBlockedPair G) :
    law.meanPairSpin e.left e.right =
      1 - 2 * law.meanOccupation e.left - 2 * law.meanOccupation e.right := by
  classical
  rw [meanPairSpin, meanOccupation, meanOccupation]
  calc
    ∑ C, law.weight C *
        (rydbergSpinIndicator G C e.left * rydbergSpinIndicator G C e.right) =
      ∑ C, (law.weight C -
        2 * (law.weight C * rydbergOccupationIndicator G C e.left) -
        2 * (law.weight C * rydbergOccupationIndicator G C e.right)) := by
          apply Finset.sum_congr rfl
          intro C _
          rw [rydbergSpinIndicator_mul_blocked G C e]
          ring
    _ = (∑ C, law.weight C) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C e.left) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C e.right) := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 1 - 2 * (∑ C, law.weight C * rydbergOccupationIndicator G C e.left) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C e.right) := by
      rw [law.normalized]

omit [DecidableRel G.Adj] in
/-- Paper's blocked-edge identity: connected Ising correlation is universally
`-4 ⟨nᵢ⟩⟨nⱼ⟩`. -/
theorem connectedSpinCorrelator_blocked
    (law : RydbergOutcomeLaw G) (e : RydbergBlockedPair G) :
    law.connectedSpinCorrelator e.left e.right =
      -4 * law.meanOccupation e.left * law.meanOccupation e.right := by
  rw [connectedSpinCorrelator, meanPairSpin_blocked law e,
    meanSpin_eq_one_sub_two_mul_meanOccupation,
    meanSpin_eq_one_sub_two_mul_meanOccupation]
  ring

omit [DecidableRel G.Adj] in
theorem meanTripleSpin_blocked
    (law : RydbergOutcomeLaw G) (t : RydbergBlockedTriple G) :
    law.meanTripleSpin t.first t.second t.third =
      1 - 2 * law.meanOccupation t.first -
        2 * law.meanOccupation t.second -
        2 * law.meanOccupation t.third := by
  classical
  rw [meanTripleSpin, meanOccupation, meanOccupation, meanOccupation]
  calc
    ∑ C, law.weight C *
        (rydbergSpinIndicator G C t.first * rydbergSpinIndicator G C t.second *
          rydbergSpinIndicator G C t.third) =
      ∑ C, (law.weight C -
        2 * (law.weight C * rydbergOccupationIndicator G C t.first) -
        2 * (law.weight C * rydbergOccupationIndicator G C t.second) -
        2 * (law.weight C * rydbergOccupationIndicator G C t.third)) := by
          apply Finset.sum_congr rfl
          intro C _
          rw [rydbergSpinIndicator_triple_blocked G C t]
          ring
    _ = (∑ C, law.weight C) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.first) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.second) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.third) := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 1 - 2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.first) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.second) -
        2 * (∑ C, law.weight C * rydbergOccupationIndicator G C t.third) := by
      rw [law.normalized]

omit [DecidableRel G.Adj] in
/-- Higher blocked-clique survivor: every three-site connected Ising correlator is negative,
with universal factorial coefficient `-16`. -/
theorem connectedTripleSpinCorrelator_blocked
    (law : RydbergOutcomeLaw G) (t : RydbergBlockedTriple G) :
    law.connectedTripleSpinCorrelator t.first t.second t.third =
      -16 * law.meanOccupation t.first * law.meanOccupation t.second *
        law.meanOccupation t.third := by
  rw [connectedTripleSpinCorrelator, meanTripleSpin_blocked law t,
    meanPairSpin_blocked law ⟨t.first, t.second, t.first_second⟩,
    meanPairSpin_blocked law ⟨t.first, t.third, t.first_third⟩,
    meanPairSpin_blocked law ⟨t.second, t.third, t.second_third⟩,
    meanSpin_eq_one_sub_two_mul_meanOccupation,
    meanSpin_eq_one_sub_two_mul_meanOccupation,
    meanSpin_eq_one_sub_two_mul_meanOccupation]
  ring

end RydbergOutcomeLaw

end HTGeometry
