import GaloisForLFunctions.HTGeometry.RydbergIndependentSetCorrelators
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants
import GaloisForLFunctions.HTGeometry.HardExclusionJointCumulants

/-!
# Rydberg one-site hard-exclusion cumulants

Every site marginal of a certified Rydberg outcome law is a zero-or-one point
count.  This bridges the graph-occupation model to the corpus's existing
hard-exclusion factorial-moment framework.
-/

open scoped BigOperators

noncomputable section

namespace HTGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Finite site set whose distinct vertices are pairwise blockaded. -/
structure RydbergBlockedClique where
  sites : Finset V
  pairwiseBlocked : (sites : Set V).Pairwise G.Adj

namespace RydbergOutcomeLaw

variable {G}

/-- Actual point-count law obtained by observing one site of a Rydberg outcome. -/
def sitePointCountLaw (law : RydbergOutcomeLaw G) (v : V) :
    GaloisForLFunctions.HTGeometry.FinitePointCountLaw
      (RydbergIndependentConfiguration G) where
  weight := law.weight
  count C := if v ∈ C.sites then 1 else 0
  weight_nonneg := law.nonnegative
  weight_sum_one := law.normalized

omit [DecidableRel G.Adj] in
theorem sitePointCountLaw_factorialMoment_one
    (law : RydbergOutcomeLaw G) (v : V) :
    (law.sitePointCountLaw v).factorialMoment 1 = law.meanOccupation v := by
  classical
  simp [sitePointCountLaw,
    GaloisForLFunctions.HTGeometry.FinitePointCountLaw.factorialMoment,
    meanOccupation, rydbergOccupationIndicator]

omit [DecidableRel G.Adj] in
/-- All site factorial moments of order at least two vanish exactly. -/
theorem sitePointCountLaw_factorialMoment_succ_succ
    (law : RydbergOutcomeLaw G) (v : V) (k : ℕ) :
    (law.sitePointCountLaw v).factorialMoment (k + 2) = 0 := by
  classical
  unfold GaloisForLFunctions.HTGeometry.FinitePointCountLaw.factorialMoment
  apply Finset.sum_eq_zero
  intro C hC
  by_cases hv : v ∈ C.sites
  · simp [sitePointCountLaw, hv]
  · simp [sitePointCountLaw, hv]

omit [DecidableRel G.Adj] in
theorem sitePointCountLaw_factorialCumulantOne
    (law : RydbergOutcomeLaw G) (v : V) :
    (law.sitePointCountLaw v).factorialCumulantOne = law.meanOccupation v := by
  exact law.sitePointCountLaw_factorialMoment_one v

omit [DecidableRel G.Adj] in
/-- Every Rydberg site has negative second factorial cumulant `-p²`. -/
theorem sitePointCountLaw_factorialCumulantTwo
    (law : RydbergOutcomeLaw G) (v : V) :
    (law.sitePointCountLaw v).factorialCumulantTwo =
      -(law.meanOccupation v) ^ 2 := by
  rw [GaloisForLFunctions.HTGeometry.FinitePointCountLaw.factorialCumulantTwo,
    law.sitePointCountLaw_factorialMoment_one v,
    show (law.sitePointCountLaw v).factorialMoment 2 = 0 by
      simpa using law.sitePointCountLaw_factorialMoment_succ_succ v 0]
  ring

omit [DecidableRel G.Adj] in
/-- Every Rydberg site has third factorial cumulant `2p³`. -/
theorem sitePointCountLaw_factorialCumulantThree
    (law : RydbergOutcomeLaw G) (v : V) :
    (law.sitePointCountLaw v).factorialCumulantThree =
      2 * (law.meanOccupation v) ^ 3 := by
  rw [GaloisForLFunctions.HTGeometry.FinitePointCountLaw.factorialCumulantThree,
    law.sitePointCountLaw_factorialMoment_one v,
    show (law.sitePointCountLaw v).factorialMoment 2 = 0 by
      simpa using law.sitePointCountLaw_factorialMoment_succ_succ v 0,
    show (law.sitePointCountLaw v).factorialMoment 3 = 0 by
      simpa using law.sitePointCountLaw_factorialMoment_succ_succ v 1]
  ring

omit [DecidableRel G.Adj] in
/-- Exact no-excitation probability at one site. -/
theorem sitePointCountLaw_voidMass
    (law : RydbergOutcomeLaw G) (v : V) :
    (law.sitePointCountLaw v).voidMass = 1 - law.meanOccupation v := by
  classical
  have hsplit :
      (∑ C, law.weight C) =
        (∑ C, if v ∈ C.sites then law.weight C else 0) +
          ∑ C, if v ∈ C.sites then 0 else law.weight C := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro C hC
    by_cases hv : v ∈ C.sites <;> simp [hv]
  have hmean : law.meanOccupation v =
      ∑ C, if v ∈ C.sites then law.weight C else 0 := by
    rw [meanOccupation]
    apply Finset.sum_congr rfl
    intro C hC
    by_cases hv : v ∈ C.sites <;> simp [rydbergOccupationIndicator, hv]
  unfold GaloisForLFunctions.HTGeometry.FinitePointCountLaw.voidMass
  simp only [sitePointCountLaw]
  have hvoid :
      (∑ C, if (if v ∈ C.sites then 1 else 0) = 0 then law.weight C else 0) =
        ∑ C, if v ∈ C.sites then 0 else law.weight C := by
    apply Finset.sum_congr rfl
    intro C hC
    by_cases hv : v ∈ C.sites <;> simp [hv]
  rw [hvoid]
  rw [law.normalized, ← hmean] at hsplit
  linarith

/-- Joint occupation moments on the labelled sites of a blocked clique. -/
def blockedCliqueMomentFamily
    (law : RydbergOutcomeLaw G) (K : RydbergBlockedClique G) :
    HardExclusionMomentFamily K.sites where
  mean i := law.meanOccupation i
  moment s := ∑ C, law.weight C *
    ∏ i ∈ s, rydbergOccupationIndicator G C i
  moment_singleton i := by
    simp [meanOccupation]
  moment_nonsingleton s hs := by
    classical
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    apply Finset.sum_eq_zero
    intro C hC
    have hadj : G.Adj (i : V) (j : V) :=
      K.pairwiseBlocked i.property j.property (Subtype.coe_ne_coe.mpr hij)
    have hpair := rydbergOccupationIndicator_mul_blocked_eq_zero G C
      ⟨(i : V), (j : V), hadj⟩
    have hprod : (∏ k ∈ s, rydbergOccupationIndicator G C (k : V)) = 0 := by
      rcases mul_eq_zero.mp hpair with hi0 | hj0
      · exact Finset.prod_eq_zero hi hi0
      · exact Finset.prod_eq_zero hj hj0
    rw [hprod, mul_zero]

/-- All-order connected occupation cumulant on every subset of a blocked clique. -/
def blockedCliqueOccupationCumulant
    (law : RydbergOutcomeLaw G) (K : RydbergBlockedClique G)
    (s : Finset K.sites) : ℝ :=
  (law.blockedCliqueMomentFamily K).jointCumulant s

omit [DecidableRel G.Adj] in
/-- Universal all-order hard-blockade hierarchy.  Pair order gives a negative
product, triple order gives twice a positive product, and signs/factorials
continue mechanically at every order. -/
theorem blockedCliqueOccupationCumulant_eq
    (law : RydbergOutcomeLaw G) (K : RydbergBlockedClique G)
    (s : Finset K.sites) :
    law.blockedCliqueOccupationCumulant K s =
      (-1 : ℝ) ^ (s.card - 1) * (s.card - 1).factorial *
        ∏ i ∈ s, law.meanOccupation (i : V) := by
  exact (law.blockedCliqueMomentFamily K).jointCumulant_eq_discrete s

end RydbergOutcomeLaw

end HTGeometry
