import GaloisForLFunctions.HilbertMetric.Probability.Interventions.CoAdaptedBellman

/-!
# The causal gap of a delayed binary observation

When the final counterfactual failure rate is constant, the optimal
causal rescue mass averages the positive conditional rate differences.
The terminal Fréchet lower bound takes the positive part after averaging.
Their difference is the smaller of the expected positive and negative
parts of the conditional rate difference.
-/

open Set
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

noncomputable section

variable {σ τ : Type*}

/-- Run the prefix policy and then the suffix policy. -/
def appendCoAdaptedPolicy :
    {ps qs : List (BinaryInterventionStage σ τ)} →
      CoAdaptedPolicy ps → CoAdaptedPolicy qs → CoAdaptedPolicy (ps ++ qs)
  | [], _, .stop, η => η
  | _ :: _, _, .cons C π, η => .cons C (appendCoAdaptedPolicy π η)

/-- Every policy on a concatenated horizon splits at the prescribed time. -/
theorem exists_appendCoAdaptedPolicy_eq (ps qs : List (BinaryInterventionStage σ τ))
    (π : CoAdaptedPolicy (ps ++ qs)) :
    ∃ (ρ : CoAdaptedPolicy ps) (η : CoAdaptedPolicy qs), appendCoAdaptedPolicy ρ η = π := by
  induction ps with
  | nil => exact ⟨.stop, π, rfl⟩
  | cons d ps ih =>
    change CoAdaptedPolicy (d :: (ps ++ qs)) at π
    cases π with
    | cons C π =>
      obtain ⟨ρ, η, h⟩ := ih π
      exact ⟨.cons C ρ, η, congrArg (CoAdaptedPolicy.cons C) h⟩

theorem trajectoryExpectation_appendPolicy (g : σ → τ → ℝ)
    {ps qs : List (BinaryInterventionStage σ τ)} (ρ : CoAdaptedPolicy ps) (η : CoAdaptedPolicy qs) :
    trajectoryExpectation g (appendCoAdaptedPolicy ρ η) =
      trajectoryExpectation (trajectoryExpectation g η) ρ := by
  induction ρ with
  | stop => rfl
  | @cons d ps C ρ ih =>
    funext x y
    change pairingExpectation (C x y) (stageContinuation d
      (trajectoryExpectation g (appendCoAdaptedPolicy ρ η)) x y) =
        pairingExpectation (C x y) (stageContinuation d
          (trajectoryExpectation (trajectoryExpectation g η) ρ) x y)
    rw [ih]

/-- The suffix supplies the terminal payoff for the optimal prefix. -/
theorem coAdaptedValue_append (g : σ → τ → ℝ) (ps qs : List (BinaryInterventionStage σ τ)) :
    coAdaptedValue g (ps ++ qs) = coAdaptedValue (coAdaptedValue g qs) ps := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    simp only [List.cons_append, coAdaptedValue, ih]

theorem coAdaptedValue_factual (f : σ → ℝ) (ps : List (BinaryInterventionStage σ τ)) :
    coAdaptedValue (fun x _ => f x) ps = fun x _ => factualExpectation f ps x := by
  rw [← trajectoryExpectation_optimalCoAdaptedPolicy, trajectoryExpectation_factual]

private theorem pairingExpectation_rawRescue {p q : FailureRate} (C : Pairing p q) :
    pairingExpectation C (terminalRescueCost id id) = rescue C := by
  simp [pairingExpectation, terminalRescueCost, rescue]

private theorem stageContinuation_decodedRescue (d : BinaryInterventionStage σ τ)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (x : σ) (y : τ) :
    stageContinuation d (terminalRescueCost f g) x y = terminalRescueCost id id := by
  funext a b
  simp only [stageContinuation, terminalRescueCost, hf, hg, id_eq]
  rfl

private theorem finalRescue_coAdaptedValue (d : BinaryInterventionStage σ τ)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) :
    coAdaptedValue (terminalRescueCost f g) [d] =
      fun x y => lowerRescueMass (d.factualRate x) (d.counterfactualRate y) := by
  funext x y
  let h := stageContinuation d (terminalRescueCost f g) x y
  change pairingExpectation (continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y) h) h = _
  have he : h = terminalRescueCost id id := stageContinuation_decodedRescue d f g hf hg x y
  have hc : 0 ≤ rescueContrast (terminalRescueCost id id) := by norm_num [rescueContrast, terminalRescueCost]
  rw [he, continuationOptimalPairing, if_pos (Or.inr hc), pairingExpectation_rawRescue, rescue_sharedPairing]

private theorem finalRescue_lower_le_expectation (d : BinaryInterventionStage σ τ)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (η : CoAdaptedPolicy [d]) (x : σ) (y : τ) :
    lowerRescueMass (d.factualRate x) (d.counterfactualRate y) ≤
      trajectoryExpectation (terminalRescueCost f g) η x y := by
  cases η with
  | cons C η =>
    cases η with
    | stop =>
      change _ ≤ pairingExpectation (C x y) (stageContinuation d (terminalRescueCost f g) x y)
      rw [stageContinuation_decodedRescue d f g hf hg, pairingExpectation_rawRescue]
      exact (rescue_mem_Icc (C x y)).1

/-- With a constant final counterfactual rate, the optimum averages the
conditional Fréchet lower bounds over the factual prefix. -/
theorem coAdaptedValue_delayedRescue (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) :
    coAdaptedValue (terminalRescueCost f g) (ps ++ [d]) =
      fun x _ => factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps x := by
  rw [coAdaptedValue_append, finalRescue_coAdaptedValue d f g hf hg]
  simp only [hq, coAdaptedValue_factual]

/-- The marginal lower bound at the final step applies to every co-adapted policy. -/
theorem delayedRescue_lower_le_all_policies (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (π : CoAdaptedPolicy (ps ++ [d]))
    (x : σ) (y : τ) :
    factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps x ≤
      trajectoryExpectation (terminalRescueCost f g) π x y := by
  obtain ⟨ρ, η, hπ⟩ := exists_appendCoAdaptedPolicy_eq ps [d] π
  rw [← hπ, trajectoryExpectation_appendPolicy]
  have h := trajectoryExpectation_mono
    (fun z w => show lowerRescueMass (d.factualRate z) q ≤
        trajectoryExpectation (terminalRescueCost f g) η z w from by
          rw [← hq w]
          exact finalRescue_lower_le_expectation d f g hf hg η z w) ρ x y
  rw [trajectoryExpectation_factual] at h
  exact h

/-- In this regime the admissible optimum also attains the unrestricted
co-adapted minimum. -/
theorem delayedRescue_isLeast_all_policies (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (x : σ) (y : τ) :
    IsLeast {r | ∃ π : CoAdaptedPolicy (ps ++ [d]), trajectoryExpectation (terminalRescueCost f g) π x y = r}
      (factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps x) := by
  refine ⟨⟨optimalCoAdaptedPolicy (terminalRescueCost f g) (ps ++ [d]), ?_⟩, ?_⟩
  · rw [trajectoryExpectation_optimalCoAdaptedPolicy, coAdaptedValue_delayedRescue ps d q hq f g hf hg]
  · rintro _ ⟨π, rfl⟩
    exact delayedRescue_lower_le_all_policies ps d q hq f g hf hg π x y

theorem factualExpectation_append (f : σ → ℝ) (ps qs : List (BinaryInterventionStage σ τ)) :
    factualExpectation f (ps ++ qs) = factualExpectation (factualExpectation f qs) ps := by
  induction ps with
  | nil => rfl
  | cons d ps ih => simp only [List.cons_append, factualExpectation, ih]

theorem counterfactualExpectation_append (f : τ → ℝ) (ps qs : List (BinaryInterventionStage σ τ)) :
    counterfactualExpectation f (ps ++ qs) = counterfactualExpectation (counterfactualExpectation f qs) ps := by
  induction ps with
  | nil => rfl
  | cons d ps ih => simp only [List.cons_append, counterfactualExpectation, ih]

private theorem failureLaw_real_sum (p : FailureRate) : ∑ a, (failureLaw p a : ℝ) = 1 := by
  rw [Fintype.sum_bool]
  change (p.1 : ℝ) + ↑(1 - p.1) = 1
  rw [NNReal.coe_sub p.2, NNReal.coe_one]
  ring

theorem factualExpectation_const (c : ℝ) (ps : List (BinaryInterventionStage σ τ)) :
    factualExpectation (fun _ => c) ps = fun _ => c := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    funext x
    change (∑ a, (failureLaw (d.factualRate x) a : ℝ) *
      factualExpectation (fun _ => c) ps (d.factualNext x a)) = c
    simp only [ih, ← Finset.sum_mul, failureLaw_real_sum, one_mul]

theorem counterfactualExpectation_const (c : ℝ) (ps : List (BinaryInterventionStage σ τ)) :
    counterfactualExpectation (fun _ => c) ps = fun _ => c := by
  induction ps with
  | nil => rfl
  | cons d ps ih =>
    funext y
    change (∑ b, (failureLaw (d.counterfactualRate y) b : ℝ) *
      counterfactualExpectation (fun _ => c) ps (d.counterfactualNext y b)) = c
    simp only [ih, ← Finset.sum_mul, failureLaw_real_sum, one_mul]

theorem factualExpectation_sub (f g : σ → ℝ) (ps : List (BinaryInterventionStage σ τ)) :
    factualExpectation (fun z => f z - g z) ps =
      fun x => factualExpectation f ps x - factualExpectation g ps x := by
  induction ps with
  | nil => rfl
  | cons d ps ih => simp only [factualExpectation, ih, mul_sub, Finset.sum_sub_distrib]

/-- The terminal factual failure rate averages the last conditional
rates. The counterfactual failure rate is the common last rate. -/
theorem delayedRescue_terminalMarginals (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (x : σ) (y : τ) :
    factualFailureMass f (ps ++ [d]) x = factualExpectation (fun z => ((d.factualRate z).1 : ℝ)) ps x ∧
      counterfactualFailureMass g (ps ++ [d]) y = (q.1 : ℝ) := by
  have hF : factualExpectation (fun z => if f z then (1 : ℝ) else 0) [d] =
      fun z => ((d.factualRate z).1 : ℝ) := by
    funext z
    change (∑ a, (failureLaw (d.factualRate z) a : ℝ) *
      (if f (d.factualNext z a) then 1 else 0)) = _
    simp [hf, failureLaw]
  have hQ : counterfactualExpectation (fun z => if g z then (1 : ℝ) else 0) [d] =
      fun _ => (q.1 : ℝ) := by
    funext z
    change (∑ b, (failureLaw (d.counterfactualRate z) b : ℝ) *
      (if g (d.counterfactualNext z b) then 1 else 0)) = _
    simp [hg, hq, failureLaw]
  exact ⟨by rw [factualFailureMass, factualExpectation_append, hF],
    by rw [counterfactualFailureMass, counterfactualExpectation_append, hQ, counterfactualExpectation_const]⟩

private theorem sub_eq_rescueLower_sub_reverse (p q : FailureRate) :
    (p.1 : ℝ) - q.1 = lowerRescueMass p q - lowerRescueMass q p := by
  by_cases h : (q.1 : ℝ) ≤ p.1
  · rw [lowerRescueMass, lowerRescueMass, max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h), sub_zero]
  · have hp := (lt_of_not_ge h).le
    rw [lowerRescueMass, lowerRescueMass, max_eq_left (sub_nonpos.mpr hp), max_eq_right (sub_nonneg.mpr hp)]
    ring

/-- The causal excess over the terminal Fréchet lower bound is the
smaller of the two directional conditional differences, averaged over
the factual prefix law. -/
theorem delayedRescue_gap_eq_min (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (x : σ) (y : τ) :
    coAdaptedValue (terminalRescueCost f g) (ps ++ [d]) x y -
        max 0 (factualFailureMass f (ps ++ [d]) x - counterfactualFailureMass g (ps ++ [d]) y) =
      min (factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps x)
        (factualExpectation (fun z => lowerRescueMass q (d.factualRate z)) ps x) := by
  obtain ⟨hF, hQ⟩ := delayedRescue_terminalMarginals ps d q hq f g hf hg x y
  let P := factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps x
  let N := factualExpectation (fun z => lowerRescueMass q (d.factualRate z)) ps x
  have hdiff : factualFailureMass f (ps ++ [d]) x - counterfactualFailureMass g (ps ++ [d]) y =
      P - N := by
    rw [hF, hQ]
    calc
      _ = factualExpectation (fun z => ((d.factualRate z).1 : ℝ) - q.1) ps x := by
        rw [factualExpectation_sub, factualExpectation_const]
      _ = factualExpectation (fun z => lowerRescueMass (d.factualRate z) q -
        lowerRescueMass q (d.factualRate z)) ps x := by
        exact congrArg (fun F => factualExpectation F ps x) (funext fun z => sub_eq_rescueLower_sub_reverse _ _)
      _ = _ := congrFun (factualExpectation_sub _ _ ps) x
  rw [coAdaptedValue_delayedRescue ps d q hq f g hf hg, hdiff]
  change P - max 0 (P - N) = min P N
  by_cases h : N ≤ P
  · rw [max_eq_right (sub_nonneg.mpr h), min_eq_right h]
    ring
  · have h' := (lt_of_not_ge h).le
    rw [max_eq_left (sub_nonpos.mpr h'), min_eq_left h', sub_zero]

/-- A final factual state can be reached along a prefix of positive
branch probabilities. -/
def PositiveFactualReachable : List (BinaryInterventionStage σ τ) → σ → σ → Prop
  | [], x, z => z = x
  | d :: ds, x, z => ∃ a, 0 < (failureLaw (d.factualRate x) a : ℝ) ∧
      PositiveFactualReachable ds (d.factualNext x a) z

private theorem factualExpectation_nonneg (F : σ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (ps : List (BinaryInterventionStage σ τ)) : ∀ x, 0 ≤ factualExpectation F ps x := by
  induction ps with
  | nil => exact hF
  | cons d ds ih =>
    intro x
    exact Finset.sum_nonneg fun a _ => mul_nonneg (failureLaw (d.factualRate x) a).2 (ih (d.factualNext x a))

/-- A nonnegative payoff has positive expectation exactly when it is
positive at some reachable state. -/
theorem factualExpectation_pos_iff (F : σ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (ps : List (BinaryInterventionStage σ τ)) (x : σ) :
    0 < factualExpectation F ps x ↔ ∃ z, PositiveFactualReachable ps x z ∧ 0 < F z := by
  classical
  induction ps generalizing x with
  | nil =>
    change 0 < F x ↔ ∃ z, z = x ∧ 0 < F z
    exact ⟨fun h => ⟨x, rfl, h⟩, by rintro ⟨_, rfl, h⟩; exact h⟩
  | cons d ds ih =>
    let w (a : Bool) : ℝ := failureLaw (d.factualRate x) a
    let H (a : Bool) := factualExpectation F ds (d.factualNext x a)
    have hw (a : Bool) : 0 ≤ w a := (failureLaw (d.factualRate x) a).2
    have hH (a : Bool) : 0 ≤ H a := factualExpectation_nonneg F hF ds (d.factualNext x a)
    change 0 < (∑ a, w a * H a) ↔ ∃ z, (∃ a, 0 < w a ∧
      PositiveFactualReachable ds (d.factualNext x a) z) ∧ 0 < F z
    constructor
    · intro hs
      obtain ⟨a, ha⟩ : ∃ a, 0 < w a * H a := by
        by_contra hn
        have hsum : (∑ a, w a * H a) ≤ 0 :=
          Finset.sum_nonpos fun a _ => le_of_not_gt fun ha => hn ⟨a, ha⟩
        exact (not_lt_of_ge hsum) hs
      have ha₀ : 0 < w a := lt_of_le_of_ne (hw a) (by
        intro he
        rw [← he, zero_mul] at ha
        exact lt_irrefl _ ha)
      have ha₁ : 0 < H a := lt_of_le_of_ne (hH a) (by
        intro he
        rw [← he, mul_zero] at ha
        exact lt_irrefl _ ha)
      obtain ⟨z, hz, hzF⟩ := (ih (d.factualNext x a)).mp ha₁
      exact ⟨z, ⟨a, ha₀, hz⟩, hzF⟩
    · rintro ⟨z, ⟨a, ha, hz⟩, hzF⟩
      have he : 0 < H a := (ih (d.factualNext x a)).mpr ⟨z, hz, hzF⟩
      exact (mul_pos ha he).trans_le
        (Finset.single_le_sum (fun b _ => mul_nonneg (hw b) (hH b)) (Finset.mem_univ a))

private theorem factualExpectation_lowerRescue_pos_iff
    (p q : σ → FailureRate) (ps : List (BinaryInterventionStage σ τ)) (x : σ) :
    0 < factualExpectation (fun z => lowerRescueMass (p z) (q z)) ps x ↔
      ∃ z, PositiveFactualReachable ps x z ∧ ((q z).1 : ℝ) < (p z).1 := by
  rw [factualExpectation_pos_iff (fun z => lowerRescueMass (p z) (q z))
    (fun z => le_max_left 0 ((p z).1 - (q z).1 : ℝ)) ps x]
  simp only [lowerRescueMass, lt_max_iff, lt_irrefl, false_or, sub_pos]

/-- The causal lower bound is strictly above the terminal Fréchet bound
exactly when positive-probability factual histories straddle the final
counterfactual rate. -/
theorem delayedRescue_strictGap_iff_straddles (ps : List (BinaryInterventionStage σ τ))
    (d : BinaryInterventionStage σ τ) (q : FailureRate) (hq : ∀ y, d.counterfactualRate y = q)
    (f : σ → Bool) (g : τ → Bool) (hf : ∀ x a, f (d.factualNext x a) = a)
    (hg : ∀ y b, g (d.counterfactualNext y b) = b) (x : σ) (y : τ) :
    max 0 (factualFailureMass f (ps ++ [d]) x - counterfactualFailureMass g (ps ++ [d]) y) <
        coAdaptedValue (terminalRescueCost f g) (ps ++ [d]) x y ↔
      (∃ z, PositiveFactualReachable ps x z ∧ (q.1 : ℝ) < (d.factualRate z).1) ∧
        (∃ z, PositiveFactualReachable ps x z ∧ ((d.factualRate z).1 : ℝ) < q.1) := by
  rw [← sub_pos, delayedRescue_gap_eq_min ps d q hq f g hf hg, lt_min_iff,
    factualExpectation_lowerRescue_pos_iff _ (fun _ => q), factualExpectation_lowerRescue_pos_iff (fun _ => q) _]

private def fairFailureRate : FailureRate := ⟨1 / 2, by norm_num⟩

private theorem fairFailureRate_coe : (fairFailureRate.1 : ℝ) = 1 / 2 := by
  change (((1 / 2 : ℝ≥0) : ℝ)) = 1 / 2
  push_cast
  rfl

/-- The midpoint of two failure rates. -/
def meanFailureRate (p q : FailureRate) : FailureRate :=
  ⟨(p.1 + q.1) / 2, by
    have hp : (p.1 : ℝ) ≤ 1 := by exact_mod_cast p.2
    have hq : (q.1 : ℝ) ≤ 1 := by exact_mod_cast q.2
    have h : ((p.1 : ℝ) + q.1) / 2 ≤ 1 := by linarith only [hp, hq]
    exact_mod_cast h⟩

theorem meanFailureRate_coe (p q : FailureRate) :
    ((meanFailureRate p q).1 : ℝ) = ((p.1 : ℝ) + q.1) / 2 := by
  change ((((p.1 + q.1) / 2 : ℝ≥0) : ℝ)) = _
  push_cast
  rfl

private def copyingObservation (p : Bool → FailureRate) (q : FailureRate) : BinaryInterventionStage Bool Bool :=
  ⟨p, fun _ => q, fun _ a => a, fun _ b => b⟩

/-- A fair observed prefix followed by a factual rate depending on its
bit. The counterfactual final rate is their midpoint. -/
def delayedSymmetricStages (lo hi : FailureRate) : List (BinaryInterventionStage Bool Bool) :=
  [copyingObservation (fun _ => fairFailureRate) fairFailureRate,
    copyingObservation (fun x => if x then hi else lo) (meanFailureRate lo hi)]

private theorem factualExpectation_oneFair (F : Bool → ℝ) (x : Bool) :
    factualExpectation F [copyingObservation (fun _ => fairFailureRate) fairFailureRate] x =
      (F true + F false) / 2 := by
  change (∑ a, (failureLaw fairFailureRate a : ℝ) * F a) = _
  rw [Fintype.sum_bool]
  change (fairFailureRate.1 : ℝ) * F true + ↑(1 - fairFailureRate.1) * F false = _
  rw [NNReal.coe_sub fairFailureRate.2, NNReal.coe_one, fairFailureRate_coe]
  ring

/-- Equal terminal marginals can hide a strictly positive causal gap.
The exact optimum over all policies is a quarter of the difference
between the two factual conditional rates. -/
theorem delayedSymmetric_equalMarginals_exact_minimum (lo hi : FailureRate)
    (hlt : (lo.1 : ℝ) < hi.1) :
    let ds := delayedSymmetricStages lo hi
    factualFailureMass id ds false = counterfactualFailureMass id ds false ∧
      IsLeast {r | ∃ π : CoAdaptedPolicy ds, trajectoryExpectation (terminalRescueCost id id) π false false = r}
        (((hi.1 : ℝ) - lo.1) / 4) ∧ 0 < ((hi.1 : ℝ) - lo.1) / 4 := by
  let q := meanFailureRate lo hi
  let ps := [copyingObservation (fun _ => fairFailureRate) fairFailureRate]
  let d := copyingObservation (fun x => if x then hi else lo) q
  have hq : ∀ y, d.counterfactualRate y = q := fun _ => rfl
  have hf : ∀ x a, id (d.factualNext x a) = a := fun _ _ => rfl
  have hg : ∀ y b, id (d.counterfactualNext y b) = b := fun _ _ => rfl
  obtain ⟨hF, hQ⟩ := delayedRescue_terminalMarginals ps d q hq id id hf hg false false
  have hqr : (q.1 : ℝ) = ((lo.1 : ℝ) + hi.1) / 2 := meanFailureRate_coe lo hi
  have hlow : (lo.1 : ℝ) ≤ q.1 := by rw [hqr]; linarith only [hlt]
  have hhigh : (q.1 : ℝ) ≤ hi.1 := by rw [hqr]; linarith only [hlt]
  have hFq : factualFailureMass id (ps ++ [d]) false = (q.1 : ℝ) := by
    rw [hF, factualExpectation_oneFair, hqr]
    change ((hi.1 : ℝ) + lo.1) / 2 = ((lo.1 : ℝ) + hi.1) / 2
    rw [add_comm (hi.1 : ℝ)]
  have hm : factualExpectation (fun z => lowerRescueMass (d.factualRate z) q) ps false =
      ((hi.1 : ℝ) - lo.1) / 4 := by
    rw [factualExpectation_oneFair]
    change (lowerRescueMass hi q + lowerRescueMass lo q) / 2 = _
    rw [lowerRescueMass, lowerRescueMass, max_eq_right (sub_nonneg.mpr hhigh),
      max_eq_left (sub_nonpos.mpr hlow), hqr]
    ring
  refine ⟨hFq.trans hQ.symm, ?_, div_pos (sub_pos.mpr hlt) (by norm_num)⟩
  rw [← hm]
  exact delayedRescue_isLeast_all_policies ps d q hq id id hf hg false false

#print axioms exists_appendCoAdaptedPolicy_eq
#print axioms coAdaptedValue_delayedRescue
#print axioms delayedRescue_isLeast_all_policies
#print axioms delayedRescue_gap_eq_min
#print axioms factualExpectation_pos_iff
#print axioms delayedRescue_strictGap_iff_straddles
#print axioms delayedSymmetric_equalMarginals_exact_minimum

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
