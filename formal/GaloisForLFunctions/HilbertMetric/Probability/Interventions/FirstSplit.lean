import GaloisForLFunctions.HilbertMetric.Probability.Interventions.CoAdaptedBellman
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# First disagreement in a shared threshold coupling

Each binary outcome updates the recorded history by the same rule in
both runs. The first disagreement has an exact survival-weighted hazard
and is bounded by the sum of the hazards along either marginal run.
-/

open Filter Set
open scoped BigOperators NNReal Topology

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

noncomputable section

variable {σ : Type*}

/-- A history-dependent binary observation with a common state update. -/
structure SharedHistoryStep (σ : Type*) where
  factualRate : σ → FailureRate
  counterfactualRate : σ → FailureRate
  next : σ → Bool → σ

def SharedHistoryStep.asStage (d : SharedHistoryStep σ) : BinaryInterventionStage σ σ :=
  ⟨d.factualRate, d.counterfactualRate, d.next, d.next⟩

/-- Store the branch record, with the latest branch first. -/
def SharedHistoryStep.recordedStage (d : SharedHistoryStep σ) :
    BinaryInterventionStage (σ × List Bool) (σ × List Bool) :=
  ⟨fun s => d.factualRate s.1, fun s => d.counterfactualRate s.1,
    fun s a => (d.next s.1 a, a :: s.2), fun s b => (d.next s.1 b, b :: s.2)⟩

/-- The binary total variation distance at a common state. -/
def splitHazard (d : SharedHistoryStep σ) (x : σ) : ℝ :=
  |((d.factualRate x).1 : ℝ) - (d.counterfactualRate x).1|

/-- Mass assigned to an agreement on branch `a` by the shared threshold. -/
def matchingWeight (d : SharedHistoryStep σ) (x : σ) (a : Bool) : ℝ :=
  (sharedPairing (d.factualRate x) (d.counterfactualRate x)).plan a a

theorem matchingWeight_nonneg (d : SharedHistoryStep σ) (x : σ) (a : Bool) :
    0 ≤ matchingWeight d x a :=
  ((sharedPairing (d.factualRate x) (d.counterfactualRate x)).plan a a).2

theorem matchingWeight_le_factual (d : SharedHistoryStep σ) (x : σ) (a : Bool) :
    matchingWeight d x a ≤ failureLaw (d.factualRate x) a := by
  let C := sharedPairing (d.factualRate x) (d.counterfactualRate x)
  have h : C.plan a a ≤ ∑ b, C.plan a b := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a)
  exact_mod_cast (h.trans_eq (C.row a))

theorem matchingWeight_le_counterfactual (d : SharedHistoryStep σ) (x : σ) (a : Bool) :
    matchingWeight d x a ≤ failureLaw (d.counterfactualRate x) a := by
  let C := sharedPairing (d.factualRate x) (d.counterfactualRate x)
  have h : C.plan a a ≤ ∑ b, C.plan b a :=
    Finset.single_le_sum (f := fun b => C.plan b a) (fun _ _ => zero_le) (Finset.mem_univ a)
  exact_mod_cast (h.trans_eq (C.col a))

private theorem pairingExpectation_one {p q : FailureRate} (C : Pairing p q) :
    pairingExpectation C (fun _ _ => 1) = 1 := by
  rw [pairingExpectation_factual]
  rw [Fintype.sum_bool, mul_one, mul_one]
  change (p.1 : ℝ) + ↑(1 - p.1) = 1
  rw [NNReal.coe_sub p.2, NNReal.coe_one]
  ring

private theorem pairingExpectation_splitCost (p q : FailureRate) (F : Bool → ℝ) :
    pairingExpectation (sharedPairing p q) (fun a b => if a = b then F a else 1) =
      |(p.1 : ℝ) - q.1| + ∑ a, ((sharedPairing p q).plan a a : ℝ) * F a := by
  rw [← sharedPairing_disagreement p q]
  simp [pairingExpectation, rescue, harm]
  ring

/-- The total surviving mass is the complement of the current hazard. -/
theorem matchingWeight_sum (d : SharedHistoryStep σ) (x : σ) :
    ∑ a, matchingWeight d x a = 1 - splitHazard d x := by
  have h := pairingExpectation_splitCost (d.factualRate x) (d.counterfactualRate x) (fun _ => 1)
  simp only [ite_self, pairingExpectation_one, mul_one] at h
  change 1 = splitHazard d x + ∑ a, matchingWeight d x a at h
  linarith only [h]

/-- The chance of splitting now plus the chance of later splitting on
histories that survive this step. -/
def firstSplitMass : List (SharedHistoryStep σ) → σ → ℝ
  | [], _ => 0
  | d :: ds, x => splitHazard d x + ∑ a, matchingWeight d x a * firstSplitMass ds (d.next x a)

/-- Sum of local split hazards expected along a marginal path. -/
def marginalHazardBudget (rate : SharedHistoryStep σ → σ → FailureRate) :
    List (SharedHistoryStep σ) → σ → ℝ
  | [], _ => 0
  | d :: ds, x => splitHazard d x + ∑ a, (failureLaw (rate d x) a : ℝ) *
      marginalHazardBudget rate ds (d.next x a)

theorem firstSplitMass_nonneg (ds : List (SharedHistoryStep σ)) (x : σ) : 0 ≤ firstSplitMass ds x := by
  induction ds generalizing x with
  | nil => exact le_rfl
  | cons d ds ih =>
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun a _ => mul_nonneg (matchingWeight_nonneg d x a) (ih _))

theorem splitHazard_le_firstSplitMass (d : SharedHistoryStep σ) (ds : List (SharedHistoryStep σ)) (x : σ) :
    splitHazard d x ≤ firstSplitMass (d :: ds) x := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
    mul_nonneg (matchingWeight_nonneg d x a) (firstSplitMass_nonneg ds _))

private theorem firstSplitMass_le_budget (rate : SharedHistoryStep σ → σ → FailureRate)
    (ds : List (SharedHistoryStep σ)) (x : σ)
    (h : ∀ d ∈ ds, ∀ x a, matchingWeight d x a ≤ failureLaw (rate d x) a) :
    firstSplitMass ds x ≤ marginalHazardBudget rate ds x := by
  induction ds generalizing x with
  | nil => exact le_rfl
  | cons d ds ih =>
    refine add_le_add (le_refl (splitHazard d x)) (Finset.sum_le_sum fun a _ => ?_)
    have hr := h d (List.mem_cons_self) x a
    have ht := ih (d.next x a) (fun e he => h e (List.mem_cons_of_mem d he))
    exact mul_le_mul hr ht (firstSplitMass_nonneg ds _) (failureLaw (rate d x) a).2

/-- The factual cumulative expected total variation bounds the first split. -/
theorem firstSplitMass_le_factualBudget (ds : List (SharedHistoryStep σ)) (x : σ) :
    firstSplitMass ds x ≤ marginalHazardBudget SharedHistoryStep.factualRate ds x :=
  firstSplitMass_le_budget _ ds x fun d _ => matchingWeight_le_factual d

/-- The counterfactual path yields a second bound for the same split probability. -/
theorem firstSplitMass_le_counterfactualBudget (ds : List (SharedHistoryStep σ)) (x : σ) :
    firstSplitMass ds x ≤ marginalHazardBudget SharedHistoryStep.counterfactualRate ds x :=
  firstSplitMass_le_budget _ ds x fun d _ => matchingWeight_le_counterfactual d

/-- Indicator that the two saved branch records disagree. -/
def recordSplitCost (s t : σ × List Bool) : ℝ := if s.2 = t.2 then 0 else 1

private theorem recordSplit_eq_one_of_ne (ds : List (SharedHistoryStep σ))
    (s t : σ × List Bool) (hne : s.2 ≠ t.2) :
    trajectoryExpectation recordSplitCost (sharedThresholdPolicy (ds.map SharedHistoryStep.recordedStage)) s t = 1 := by
  induction ds generalizing s t with
  | nil => exact if_neg hne
  | cons d ds ih =>
    let π := sharedThresholdPolicy (ds.map SharedHistoryStep.recordedStage)
    let f := stageContinuation d.recordedStage (trajectoryExpectation recordSplitCost π) s t
    change pairingExpectation (sharedPairing (d.factualRate s.1) (d.counterfactualRate t.1)) f = 1
    have hf : f = fun _ _ => 1 := by
      funext a b
      exact ih (d.next s.1 a, a :: s.2) (d.next t.1 b, b :: t.2) fun he => hne (List.cons.inj he).2
    rw [hf, pairingExpectation_one]

/-- The recursion is exactly the shared policy's probability of unequal
records at the end. The first distinct branch remains in the record. -/
theorem sharedThreshold_recordSplit_eq (ds : List (SharedHistoryStep σ)) (x : σ) (h : List Bool) :
    trajectoryExpectation recordSplitCost (sharedThresholdPolicy (ds.map SharedHistoryStep.recordedStage))
      (x, h) (x, h) = firstSplitMass ds x := by
  induction ds generalizing x h with
  | nil => exact if_pos rfl
  | cons d ds ih =>
    let π := sharedThresholdPolicy (ds.map SharedHistoryStep.recordedStage)
    let f := stageContinuation d.recordedStage (trajectoryExpectation recordSplitCost π) (x, h) (x, h)
    change pairingExpectation (sharedPairing (d.factualRate x) (d.counterfactualRate x)) f = _
    have hf : f = fun a b => if a = b then firstSplitMass ds (d.next x a) else 1 := by
      funext a b
      by_cases he : a = b
      · subst b
        rw [if_pos rfl]
        exact ih (d.next x a) (a :: h)
      · rw [if_neg he]
        exact recordSplit_eq_one_of_ne ds (d.next x a, a :: h) (d.next x b, b :: h) fun hab =>
          he (List.cons.inj hab).1
    rw [hf, pairingExpectation_splitCost]
    rfl

theorem firstSplitMass_le_one (ds : List (SharedHistoryStep σ)) (x : σ) : firstSplitMass ds x ≤ 1 := by
  rw [← sharedThreshold_recordSplit_eq ds x []]
  refine (trajectoryExpectation_mem_Icc recordSplitCost (fun s t => ?_) _ _ _).2
  unfold recordSplitCost
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩

/-- Any bounded payoff charged only for different final states costs at
most the probability of a split under the shared policy. -/
theorem sharedThreshold_payoff_le_firstSplitMass (g : σ → σ → ℝ)
    (hg : ∀ x y, g x y ∈ Icc 0 1) (hdiag : ∀ x, g x x = 0)
    (ds : List (SharedHistoryStep σ)) (x : σ) :
    trajectoryExpectation g (sharedThresholdPolicy (ds.map SharedHistoryStep.asStage)) x x ≤ firstSplitMass ds x := by
  induction ds generalizing x with
  | nil => exact (hdiag x).le
  | cons d ds ih =>
    let π := sharedThresholdPolicy (ds.map SharedHistoryStep.asStage)
    let C := sharedPairing (d.factualRate x) (d.counterfactualRate x)
    let F (a b : Bool) := if a = b then firstSplitMass ds (d.next x a) else 1
    change pairingExpectation C (stageContinuation d.asStage (trajectoryExpectation g π) x x) ≤ _
    have hF : pairingExpectation C F = firstSplitMass (d :: ds) x :=
      pairingExpectation_splitCost (d.factualRate x) (d.counterfactualRate x) (fun a => firstSplitMass ds (d.next x a))
    rw [← hF]
    apply pairingExpectation_mono
    intro a b
    by_cases he : a = b
    · subst b
      change trajectoryExpectation g π (d.next x a) (d.next x a) ≤ F a a
      rw [show F a a = firstSplitMass ds (d.next x a) from if_pos rfl]
      exact ih (d.next x a)
    · change trajectoryExpectation g π (d.next x a) (d.next x b) ≤ F a b
      rw [show F a b = 1 from if_neg he]
      exact (trajectoryExpectation_mem_Icc g hg π _ _).2

/-- Difference of expectations of any bounded observable is controlled
by the chance that the coupled histories ever split. -/
theorem abs_marginalExpectation_sub_le_firstSplitMass (f : σ → ℝ)
    (hf : ∀ x, f x ∈ Icc 0 1) (ds : List (SharedHistoryStep σ)) (x : σ) :
    |factualExpectation f (ds.map SharedHistoryStep.asStage) x -
      counterfactualExpectation f (ds.map SharedHistoryStep.asStage) x| ≤ firstSplitMass ds x := by
  let π := sharedThresholdPolicy (ds.map SharedHistoryStep.asStage)
  let g (z w : σ) := |f z - f w|
  have hg (z w : σ) : g z w ∈ Icc 0 1 := by
    change |f z - f w| ∈ Icc 0 1
    exact ⟨abs_nonneg _, abs_le.mpr
      ⟨by linarith only [(hf z).1, (hf w).2], by linarith only [(hf z).2, (hf w).1]⟩⟩
  have hb := sharedThreshold_payoff_le_firstSplitMass g hg
    (fun z => by simp only [g, sub_self, abs_zero]) ds x
  have hfwd := trajectoryExpectation_mono (fun z w => le_abs_self (f z - f w)) π x x
  have hrev := trajectoryExpectation_mono (fun z w => (abs_sub_comm (f w) (f z)) ▸ le_abs_self (f w - f z)) π x x
  rw [trajectoryExpectation_sub_payoff, trajectoryExpectation_factual, trajectoryExpectation_counterfactual] at hfwd
  rw [trajectoryExpectation_sub_payoff, trajectoryExpectation_counterfactual, trajectoryExpectation_factual] at hrev
  exact abs_le.mpr ⟨by linarith only [hrev.trans hb], hfwd.trans hb⟩

/-- Product survival bound when every compared branch rate changes by at
most `δ`. It preserves the accumulated survival through the horizon. -/
theorem firstSplitMass_le_one_sub_pow (ds : List (SharedHistoryStep σ)) (x : σ) (δ : ℝ)
    (hδ : δ ∈ Icc 0 1) (h : ∀ d ∈ ds, ∀ x, splitHazard d x ≤ δ) :
    firstSplitMass ds x ≤ 1 - (1 - δ) ^ ds.length := by
  induction ds generalizing x with
  | nil => simp only [firstSplitMass, List.length_nil, pow_zero, sub_self, le_refl]
  | cons d ds ih =>
    have hd := h d List.mem_cons_self x
    let t := (1 - δ) ^ ds.length
    have ht : 0 ≤ t := pow_nonneg (sub_nonneg.mpr hδ.2) _
    calc
      firstSplitMass (d :: ds) x ≤ splitHazard d x + ∑ a, matchingWeight d x a * (1 - t) := by
        refine add_le_add (le_refl (splitHazard d x)) (Finset.sum_le_sum fun a _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (ih (d.next x a) (fun e he => h e (List.mem_cons_of_mem d he))) (matchingWeight_nonneg d x a)
      _ = 1 - (1 - splitHazard d x) * t := by
        rw [← Finset.sum_mul, matchingWeight_sum]
        ring
      _ ≤ 1 - (1 - δ) * t := by
        exact sub_le_sub_left (mul_le_mul_of_nonneg_right (sub_le_sub_left hd _) ht) _
      _ = 1 - (1 - δ) ^ (d :: ds).length := by
        rw [List.length_cons, pow_succ, mul_comm]

/-- If all the conditional hazards are the same, the survival bound is exact. -/
theorem firstSplitMass_eq_one_sub_pow (ds : List (SharedHistoryStep σ)) (x : σ) (δ : ℝ)
    (h : ∀ d ∈ ds, ∀ x, splitHazard d x = δ) :
    firstSplitMass ds x = 1 - (1 - δ) ^ ds.length := by
  induction ds generalizing x with
  | nil => simp only [firstSplitMass, List.length_nil, pow_zero, sub_self]
  | cons d ds ih =>
    have ht (a : Bool) := ih (d.next x a) fun e he => h e (List.mem_cons_of_mem d he)
    simp only [firstSplitMass, ht]
    rw [← Finset.sum_mul, matchingWeight_sum, h d List.mem_cons_self x, List.length_cons, pow_succ]
    ring

/-- A family of interventions varying only the counterfactual branch law. -/
structure SharedHistoryStepFamily (ι σ : Type*) where
  factualRate : σ → FailureRate
  counterfactualRate : ι → σ → FailureRate
  next : σ → Bool → σ

variable {ι : Type*}

def SharedHistoryStepFamily.atParameter (d : SharedHistoryStepFamily ι σ) (s : ι) : SharedHistoryStep σ :=
  ⟨d.factualRate, d.counterfactualRate s, d.next⟩

/-- The intervened conditional rate tends to the factual one on every
prefix with positive factual probability. -/
def RatesConvergeOnFactualPaths (l : Filter ι) : List (SharedHistoryStepFamily ι σ) → σ → Prop
  | [], _ => True
  | d :: ds, x =>
    Tendsto (fun s => ((d.counterfactualRate s x).1 : ℝ)) l (𝓝 ((d.factualRate x).1 : ℝ)) ∧
      ∀ a, 0 < failureLaw (d.factualRate x) a → RatesConvergeOnFactualPaths l ds (d.next x a)

private theorem factualBudget_tendsto_zero (l : Filter ι) (ds : List (SharedHistoryStepFamily ι σ)) (x : σ)
    (h : RatesConvergeOnFactualPaths l ds x) :
    Tendsto (fun s => marginalHazardBudget SharedHistoryStep.factualRate
      (ds.map fun d => d.atParameter s) x) l (𝓝 0) := by
  induction ds generalizing x with
  | nil => exact tendsto_const_nhds
  | cons d ds ih =>
    let H (a : Bool) (s : ι) := marginalHazardBudget SharedHistoryStep.factualRate
      (ds.map fun e => e.atParameter s) (d.next x a)
    have hd : Tendsto (fun s => splitHazard (d.atParameter s) x) l (𝓝 0) := by
      have hc : Tendsto (fun _ : ι => ((d.factualRate x).1 : ℝ)) l (𝓝 ((d.factualRate x).1 : ℝ)) :=
        tendsto_const_nhds
      simpa only [splitHazard, SharedHistoryStepFamily.atParameter, sub_self, abs_zero] using (hc.sub h.1).abs
    have ht (a : Bool) : Tendsto (fun s => (failureLaw (d.factualRate x) a : ℝ) * H a s) l (𝓝 0) := by
      by_cases hp : 0 < failureLaw (d.factualRate x) a
      · have hh : Tendsto (H a) l (𝓝 0) := ih (d.next x a) (h.2 a hp)
        simpa only [mul_zero] using hh.const_mul (failureLaw (d.factualRate x) a : ℝ)
      · have hz := le_antisymm (le_of_not_gt hp) zero_le
        simp only [hz, NNReal.coe_zero, zero_mul]
        exact tendsto_const_nhds
    change Tendsto (fun s => splitHazard (d.atParameter s) x + ∑ a, (failureLaw (d.factualRate x) a : ℝ) * H a s)
      l (𝓝 0)
    simpa only [Fintype.sum_bool, add_zero] using hd.add ((ht true).add (ht false))

/-- Pointwise convergence on the factual support suffices for the whole
shared trajectory to agree with probability tending to one. -/
theorem firstSplitMass_tendsto_zero (l : Filter ι) (ds : List (SharedHistoryStepFamily ι σ)) (x : σ)
    (h : RatesConvergeOnFactualPaths l ds x) :
    Tendsto (fun s => firstSplitMass (ds.map fun d => d.atParameter s) x) l (𝓝 0) :=
  squeeze_zero (fun _ => firstSplitMass_nonneg _ _) (fun _ => firstSplitMass_le_factualBudget _ _)
    (factualBudget_tendsto_zero l ds x h)

/-- The shared terminal rescue probability tends to zero for every
fixed decoder. -/
theorem sharedRescue_tendsto_zero (l : Filter ι) (ds : List (SharedHistoryStepFamily ι σ)) (x : σ) (f : σ → Bool)
    (h : RatesConvergeOnFactualPaths l ds x) :
    Tendsto (fun s => trajectoryExpectation (terminalRescueCost f f)
      (sharedThresholdPolicy (ds.map fun d => (d.atParameter s).asStage)) x x) l (𝓝 0) := by
  have hc (z w : σ) : terminalRescueCost f f z w ∈ Icc 0 1 := by
    unfold terminalRescueCost
    split
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hdiag (z : σ) : terminalRescueCost f f z z = 0 := by
    cases hz : f z <;> simp [terminalRescueCost, hz]
  refine squeeze_zero ?_ ?_ (firstSplitMass_tendsto_zero l ds x h)
  · intro s
    exact (trajectoryExpectation_mem_Icc _ hc _ x x).1
  · intro s
    let steps := ds.map fun d => d.atParameter s
    have he : steps.map SharedHistoryStep.asStage = ds.map (fun d => (d.atParameter s).asStage) := by
      simp only [steps, List.map_map, Function.comp_def]
    have hpay := congrArg (fun stages => trajectoryExpectation (terminalRescueCost f f)
      (sharedThresholdPolicy stages) x x) he
    exact hpay.symm.trans_le (sharedThreshold_payoff_le_firstSplitMass _ hc hdiag steps x)

private theorem factualFailureMass_family_eq (ds : List (SharedHistoryStepFamily ι σ))
    (f : σ → Bool) (s t : ι) (x : σ) :
    factualFailureMass f (ds.map fun d => (d.atParameter s).asStage) x =
      factualFailureMass f (ds.map fun d => (d.atParameter t).asStage) x := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
    change (∑ a, (failureLaw (d.factualRate x) a : ℝ) *
      factualFailureMass f (ds.map fun e => (e.atParameter s).asStage) (d.next x a)) =
        ∑ a, (failureLaw (d.factualRate x) a : ℝ) *
          factualFailureMass f (ds.map fun e => (e.atParameter t).asStage) (d.next x a)
    exact Finset.sum_congr rfl fun a _ => congrArg _ (ih (d.next x a))

/-- The shared probability of necessity tends to zero. The factual
denominator is fixed throughout the family. -/
theorem sharedNecessity_tendsto_zero (l : Filter ι) (ds : List (SharedHistoryStepFamily ι σ)) (x : σ)
    (f : σ → Bool) (t : ι) (h : RatesConvergeOnFactualPaths l ds x) :
    Tendsto (fun s => policyNecessity f f
      (sharedThresholdPolicy (ds.map fun d => (d.atParameter s).asStage)) x x) l (𝓝 0) := by
  let P := factualFailureMass f (ds.map fun d => (d.atParameter t).asStage) x
  have he : (fun s => policyNecessity f f
      (sharedThresholdPolicy (ds.map fun d => (d.atParameter s).asStage)) x x) =
      fun s => trajectoryExpectation (terminalRescueCost f f)
        (sharedThresholdPolicy (ds.map fun d => (d.atParameter s).asStage)) x x / P := by
    funext s
    exact congrArg (fun p => trajectoryExpectation (terminalRescueCost f f)
      (sharedThresholdPolicy (ds.map fun d => (d.atParameter s).asStage)) x x / p)
      (factualFailureMass_family_eq ds f s t x)
  rw [he]
  simpa only [zero_div] using (sharedRescue_tendsto_zero l ds x f h).div_const P

#print axioms matchingWeight_sum
#print axioms firstSplitMass_le_factualBudget
#print axioms firstSplitMass_le_counterfactualBudget
#print axioms sharedThreshold_recordSplit_eq
#print axioms sharedThreshold_payoff_le_firstSplitMass
#print axioms abs_marginalExpectation_sub_le_firstSplitMass
#print axioms firstSplitMass_le_one_sub_pow
#print axioms firstSplitMass_eq_one_sub_pow
#print axioms firstSplitMass_tendsto_zero
#print axioms sharedRescue_tendsto_zero
#print axioms sharedNecessity_tendsto_zero

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
