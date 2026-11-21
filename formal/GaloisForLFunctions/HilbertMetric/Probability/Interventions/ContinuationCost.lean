import GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
import Mathlib.Tactic.Ring

/-!
# Optimal binary pairing for a continuation cost

The rescue mass parametrizes the joint table. A continuation cost is
affine in that mass, so its contrast determines which endpoint is
optimal. Equal marginals impose the diagonal pairing.
-/

open Set
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

noncomputable section

/-- Least rescue mass permitted by the two marginals. -/
def lowerRescueMass (p q : FailureRate) : ℝ :=
  max 0 ((p.1 : ℝ) - q.1)

/-- Greatest rescue mass permitted by the two marginals. -/
def upperRescueMass (p q : FailureRate) : ℝ :=
  min (p.1 : ℝ) (1 - q.1)

theorem rescue_mem_Icc {p q : FailureRate} (C : Pairing p q) :
    rescue C ∈ Icc (lowerRescueMass p q) (upperRescueMass p q) := by
  rw [lowerRescueMass, upperRescueMass, ← range_rescue]
  exact mem_range_self C

theorem lowerRescueMass_le_upper (p q : FailureRate) :
    lowerRescueMass p q ≤ upperRescueMass p q := by
  obtain ⟨C, _, _⟩ := existsUnique_minimum_disagreement p q
  exact (rescue_mem_Icc C).1.trans (rescue_mem_Icc C).2

private theorem exists_pairing_at_rescue {p q : FailureRate} {x : ℝ}
    (hx : x ∈ Icc (lowerRescueMass p q) (upperRescueMass p q)) :
    ∃ C : Pairing p q, rescue C = x := by
  have h := hx
  rw [lowerRescueMass, upperRescueMass, ← range_rescue] at h
  exact h

/-- The endpoint realized by shared threshold draws. -/
def sharedPairing (p q : FailureRate) : Pairing p q :=
  Classical.choose (exists_pairing_at_rescue
    (show lowerRescueMass p q ∈ Icc (lowerRescueMass p q) (upperRescueMass p q) from
      ⟨le_rfl, lowerRescueMass_le_upper p q⟩))

/-- The endpoint with maximal rescue mass. -/
def upperRescuePairing (p q : FailureRate) : Pairing p q :=
  Classical.choose (exists_pairing_at_rescue
    (show upperRescueMass p q ∈ Icc (lowerRescueMass p q) (upperRescueMass p q) from
      ⟨lowerRescueMass_le_upper p q, le_rfl⟩))

theorem rescue_sharedPairing (p q : FailureRate) : rescue (sharedPairing p q) = lowerRescueMass p q :=
  Classical.choose_spec (exists_pairing_at_rescue
    (show lowerRescueMass p q ∈ Icc (lowerRescueMass p q) (upperRescueMass p q) from
      ⟨le_rfl, lowerRescueMass_le_upper p q⟩))

theorem rescue_upperRescuePairing (p q : FailureRate) :
    rescue (upperRescuePairing p q) = upperRescueMass p q :=
  Classical.choose_spec (exists_pairing_at_rescue
    (show upperRescueMass p q ∈ Icc (lowerRescueMass p q) (upperRescueMass p q) from
      ⟨lowerRescueMass_le_upper p q, le_rfl⟩))

/-- Equal conditional marginals must use the diagonal law. -/
def AdmissiblePairing {p q : FailureRate} (C : Pairing p q) : Prop :=
  p = q → rescue C = 0

theorem admissiblePairing_iff_equal_outcomes {p q : FailureRate} (C : Pairing p q) :
    AdmissiblePairing C ↔ p = q → ∀ a b : Bool, a ≠ b → C.plan a b = 0 := by
  constructor
  · intro h he
    have hR := h he
    have hH : harm C = 0 := by
      have hr := rescue_sub_harm C
      have hpq : (p.1 : ℝ) = q.1 := congrArg (fun r : FailureRate => (r.1 : ℝ)) he
      rw [hpq, sub_self, hR, zero_sub] at hr
      exact neg_eq_zero.mp hr
    intro a b hab
    cases a <;> cases b
    · exact (hab rfl).elim
    · apply NNReal.eq
      exact hH
    · apply NNReal.eq
      exact hR
    · exact (hab rfl).elim
  · intro h he
    have hh := h he true false (by intro hh; cases hh)
    change (C.plan true false : ℝ) = 0
    rw [hh, NNReal.coe_zero]

theorem admissible_sharedPairing (p q : FailureRate) :
    AdmissiblePairing (sharedPairing p q) := by
  intro he
  rw [rescue_sharedPairing, lowerRescueMass, he, sub_self, max_self]

theorem sharedPairing_disagreement (p q : FailureRate) :
    rescue (sharedPairing p q) + harm (sharedPairing p q) = |(p.1 : ℝ) - q.1| := by
  have h := rescue_sub_harm (sharedPairing p q)
  by_cases he : 0 ≤ (p.1 : ℝ) - q.1
  · rw [abs_of_nonneg he, rescue_sharedPairing, lowerRescueMass, max_eq_right he]
    rw [rescue_sharedPairing, lowerRescueMass, max_eq_right he] at h
    linarith only [h]
  · have he' := le_of_not_ge he
    rw [abs_of_nonpos he', rescue_sharedPairing, lowerRescueMass, max_eq_left he']
    rw [rescue_sharedPairing, lowerRescueMass, max_eq_left he'] at h
    linarith only [h]

theorem lowerRescueMass_lt_upper_of_interior (p q : Set.Ioo (0 : ℝ≥0) 1) :
    let p' : FailureRate := ⟨p.1, p.2.2.le⟩
    let q' : FailureRate := ⟨q.1, q.2.2.le⟩
    lowerRescueMass p' q' < upperRescueMass p' q' := by
  obtain ⟨C, D, h⟩ := interior_rescue_not_identified p q
  exact ((rescue_mem_Icc C).1.trans_lt h).trans_le (rescue_mem_Icc D).2

/-- Expected downstream cost under a binary pairing. -/
def pairingExpectation {p q : FailureRate} (C : Pairing p q) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ a, ∑ b, (C.plan a b : ℝ) * f a b

theorem pairingExpectation_mono {p q : FailureRate} (C : Pairing p q) {f g : Bool → Bool → ℝ}
    (h : ∀ a b, f a b ≤ g a b) : pairingExpectation C f ≤ pairingExpectation C g :=
  Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h a b) (C.plan a b).2

theorem pairingExpectation_factual {p q : FailureRate} (C : Pairing p q) (f : Bool → ℝ) :
    pairingExpectation C (fun a _ => f a) = ∑ a, (failureLaw p a : ℝ) * f a := by
  unfold pairingExpectation
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul]
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) (C.row a)
  push_cast at h
  rw [h]

theorem pairingExpectation_counterfactual {p q : FailureRate} (C : Pairing p q) (f : Bool → ℝ) :
    pairingExpectation C (fun _ b => f b) = ∑ b, (failureLaw q b : ℝ) * f b := by
  unfold pairingExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul]
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) (C.col b)
  push_cast at h
  rw [h]

/-- The coefficient of rescue mass in the continuation cost. -/
def rescueContrast (f : Bool → Bool → ℝ) : ℝ :=
  f true false + f false true - f false false - f true true

private theorem pairingExpectation_affine {p q : FailureRate} (C : Pairing p q) (f : Bool → Bool → ℝ) :
    pairingExpectation C f = (1 - (q.1 : ℝ)) * f false false +
      ((q.1 : ℝ) - p.1) * f false true + (p.1 : ℝ) * f true true + rescue C * rescueContrast f := by
  have hr := congrArg (fun x : ℝ≥0 => (x : ℝ)) (C.row true)
  have hc := congrArg (fun x : ℝ≥0 => (x : ℝ)) (C.col false)
  simp only [Fintype.sum_bool, NNReal.coe_add, failureLaw, NNReal.coe_sub q.2] at hr hc
  have h₀₀ : (C.plan false false : ℝ) = 1 - (q.1 : ℝ) - rescue C := by
    change rescue C + (C.plan false false : ℝ) = 1 - (q.1 : ℝ) at hc
    linarith only [hc]
  have h₁₁ : (C.plan true true : ℝ) = (p.1 : ℝ) - rescue C := by
    change (C.plan true true : ℝ) + rescue C = (p.1 : ℝ) at hr
    linarith only [hr]
  have h₀₁ : (C.plan false true : ℝ) = (q.1 : ℝ) - p.1 + rescue C := by
    have h := rescue_sub_harm C
    change rescue C - (C.plan false true : ℝ) = (p.1 : ℝ) - q.1 at h
    linarith only [h]
  simp only [pairingExpectation, Fintype.sum_bool, h₀₀, h₀₁, h₁₁, rescueContrast,
    show (C.plan true false : ℝ) = rescue C from rfl]
  ring

theorem pairingExpectation_sub {p q : FailureRate} (C D : Pairing p q) (f : Bool → Bool → ℝ) :
    pairingExpectation C f - pairingExpectation D f = (rescue C - rescue D) * rescueContrast f := by
  rw [pairingExpectation_affine C, pairingExpectation_affine D]
  ring

/-- A continuation cost with negative contrast selects the upper
rescue endpoint when the two marginals differ. -/
def continuationOptimalPairing (p q : FailureRate) (f : Bool → Bool → ℝ) : Pairing p q :=
  if p = q ∨ 0 ≤ rescueContrast f then sharedPairing p q else upperRescuePairing p q

theorem admissible_continuationOptimalPairing (p q : FailureRate) (f : Bool → Bool → ℝ) :
    AdmissiblePairing (continuationOptimalPairing p q f) := by
  intro h
  rw [continuationOptimalPairing, if_pos (Or.inl h)]
  exact admissible_sharedPairing p q h

/-- The selected endpoint minimizes the expected continuation cost
among all admissible pairings. -/
theorem continuationOptimalPairing_le {p q : FailureRate} (f : Bool → Bool → ℝ)
    (C : Pairing p q) (hC : AdmissiblePairing C) :
    pairingExpectation (continuationOptimalPairing p q f) f ≤ pairingExpectation C f := by
  by_cases h : p = q
  · rw [continuationOptimalPairing, if_pos (Or.inl h)]
    have he : sharedPairing p q = C :=
      pairing_ext ((admissible_sharedPairing p q h).trans (hC h).symm)
    rw [he]
  · apply sub_nonneg.mp
    rw [pairingExpectation_sub]
    by_cases hs : 0 ≤ rescueContrast f
    · rw [continuationOptimalPairing, if_pos (Or.inr hs), rescue_sharedPairing]
      exact mul_nonneg (sub_nonneg.mpr (rescue_mem_Icc C).1) hs
    · rw [continuationOptimalPairing, if_neg (not_or.mpr ⟨h, hs⟩), rescue_upperRescuePairing]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (rescue_mem_Icc C).2) (le_of_not_ge hs)

/-- Shared thresholds are strictly suboptimal precisely when a larger
rescue mass is available and lowers the continuation cost. -/
theorem continuationOptimalPairing_lt_shared_iff (p q : FailureRate) (f : Bool → Bool → ℝ) :
    pairingExpectation (continuationOptimalPairing p q f) f < pairingExpectation (sharedPairing p q) f ↔
      p ≠ q ∧ lowerRescueMass p q < upperRescueMass p q ∧ rescueContrast f < 0 := by
  by_cases h : p = q ∨ 0 ≤ rescueContrast f
  · rw [continuationOptimalPairing, if_pos h]
    constructor
    · intro hh
      exact (lt_irrefl _ hh).elim
    · rintro ⟨hpq, _, hf⟩
      exact (h.elim hpq (not_le_of_gt hf)).elim
  · have hpq := (not_or.mp h).1
    have hf := lt_of_not_ge (not_or.mp h).2
    rw [continuationOptimalPairing, if_neg h, ← sub_pos, pairingExpectation_sub,
      rescue_sharedPairing, rescue_upperRescuePairing]
    constructor
    · intro hs
      have hlt : lowerRescueMass p q < upperRescueMass p q := by
        by_contra! hge
        exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hge) hf.le)) hs
      exact ⟨hpq, hlt, hf⟩
    · rintro ⟨_, hlt, _⟩
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hlt) hf

#print axioms admissiblePairing_iff_equal_outcomes
#print axioms sharedPairing_disagreement
#print axioms pairingExpectation_factual
#print axioms pairingExpectation_counterfactual
#print axioms continuationOptimalPairing_le
#print axioms continuationOptimalPairing_lt_shared_iff

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
