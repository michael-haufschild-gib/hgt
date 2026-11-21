import GaloisForLFunctions.HilbertMetric.Probability.Interventions.ContinuationCost

/-!
# Exact finite-horizon co-adapted pairing

Each run keeps its own state and marginal transition law. The pairing
may depend on both current states. Backward induction selects the
optimal binary coupling for the terminal cost, including rescue.
-/

open Set
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

noncomputable section

universe u v

/-- A binary step in each run. States may retain the whole observed history. -/
structure BinaryInterventionStage (σ : Type u) (τ : Type v) where
  factualRate : σ → FailureRate
  counterfactualRate : τ → FailureRate
  factualNext : σ → Bool → σ
  counterfactualNext : τ → Bool → τ

variable {σ : Type u} {τ : Type v}

/-- Choice of a joint law after observing the two current states. -/
abbrev StagePairing (d : BinaryInterventionStage σ τ) :=
  (x : σ) → (y : τ) → Pairing (d.factualRate x) (d.counterfactualRate y)

/-- A co-adapted policy specifies a pairing at each stage and pair of states. -/
inductive CoAdaptedPolicy : List (BinaryInterventionStage σ τ) → Type (max u v)
  | stop : CoAdaptedPolicy []
  | cons {d : BinaryInterventionStage σ τ} {ds : List (BinaryInterventionStage σ τ)}
      (pair : StagePairing d) (tail : CoAdaptedPolicy ds) : CoAdaptedPolicy (d :: ds)

/-- Admissibility requires identical branches whenever the current marginals agree. -/
def AdmissiblePolicy : {ds : List (BinaryInterventionStage σ τ)} → CoAdaptedPolicy ds → Prop
  | [], .stop => True
  | _ :: _, .cons C π => (∀ x y, AdmissiblePairing (C x y)) ∧ AdmissiblePolicy π

/-- The four continuation values at a given pair of states. -/
def stageContinuation (d : BinaryInterventionStage σ τ) (W : σ → τ → ℝ) (x : σ) (y : τ) :
    Bool → Bool → ℝ :=
  fun a b => W (d.factualNext x a) (d.counterfactualNext y b)

/-- Expected terminal cost of a co-adapted policy. -/
def trajectoryExpectation (g : σ → τ → ℝ) :
    {ds : List (BinaryInterventionStage σ τ)} → CoAdaptedPolicy ds → σ → τ → ℝ
  | [], .stop => g
  | d :: _, .cons C π => fun x y =>
    pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation g π) x y)

/-- The backward value uses the appropriate endpoint of the rescue interval
at each pair of current states. -/
def coAdaptedValue (g : σ → τ → ℝ) : List (BinaryInterventionStage σ τ) → σ → τ → ℝ
  | [] => g
  | d :: ds => fun x y =>
    let f := stageContinuation d (coAdaptedValue g ds) x y
    pairingExpectation (continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y) f) f

/-- Policy realizing the backward value. -/
def optimalCoAdaptedPolicy (g : σ → τ → ℝ) : (ds : List (BinaryInterventionStage σ τ)) → CoAdaptedPolicy ds
  | [] => .stop
  | d :: ds => .cons (fun x y =>
      continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y)
        (stageContinuation d (coAdaptedValue g ds) x y)) (optimalCoAdaptedPolicy g ds)

theorem admissible_optimalCoAdaptedPolicy (g : σ → τ → ℝ) (ds : List (BinaryInterventionStage σ τ)) :
    AdmissiblePolicy (optimalCoAdaptedPolicy g ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨fun x y => admissible_continuationOptimalPairing _ _ _, ih⟩

theorem trajectoryExpectation_optimalCoAdaptedPolicy (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) :
    trajectoryExpectation g (optimalCoAdaptedPolicy g ds) = coAdaptedValue g ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    funext x y
    change pairingExpectation
      (continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y)
        (stageContinuation d (coAdaptedValue g ds) x y))
      (stageContinuation d (trajectoryExpectation g (optimalCoAdaptedPolicy g ds)) x y) = _
    rw [ih]
    rfl

theorem coAdaptedValue_le_trajectoryExpectation (g : σ → τ → ℝ)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    AdmissiblePolicy π → ∀ x y, coAdaptedValue g ds x y ≤ trajectoryExpectation g π x y := by
  induction π with
  | stop =>
    intro _ x y
    exact le_rfl
  | @cons d ds C π ih =>
    intro h x y
    change (∀ x y, AdmissiblePairing (C x y)) ∧ AdmissiblePolicy π at h
    let f := stageContinuation d (coAdaptedValue g ds) x y
    change pairingExpectation (continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y) f) f ≤
      pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation g π) x y)
    exact (continuationOptimalPairing_le f (C x y) (h.1 x y)).trans
      (pairingExpectation_mono (C x y) fun a b => ih h.2 (d.factualNext x a) (d.counterfactualNext y b))

/-- The finite-horizon value is the attained minimum over admissible
co-adapted policies, for arbitrary real terminal costs. -/
theorem coAdaptedValue_isLeast (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    IsLeast {z | ∃ π : CoAdaptedPolicy ds, AdmissiblePolicy π ∧ trajectoryExpectation g π x y = z}
      (coAdaptedValue g ds x y) := by
  refine ⟨⟨optimalCoAdaptedPolicy g ds, admissible_optimalCoAdaptedPolicy g ds, ?_⟩, ?_⟩
  · rw [trajectoryExpectation_optimalCoAdaptedPolicy]
  · rintro _ ⟨π, hπ, rfl⟩
    exact coAdaptedValue_le_trajectoryExpectation g π hπ x y

/-- Independent of the coupling, the factual run has its ordinary marginal law. -/
def factualExpectation (f : σ → ℝ) : List (BinaryInterventionStage σ τ) → σ → ℝ
  | [] => f
  | d :: ds => fun x => ∑ a, (failureLaw (d.factualRate x) a : ℝ) *
    factualExpectation f ds (d.factualNext x a)

/-- Independent of the coupling, the intervened run has its ordinary marginal law. -/
def counterfactualExpectation (f : τ → ℝ) : List (BinaryInterventionStage σ τ) → τ → ℝ
  | [] => f
  | d :: ds => fun y => ∑ b, (failureLaw (d.counterfactualRate y) b : ℝ) *
    counterfactualExpectation f ds (d.counterfactualNext y b)

theorem trajectoryExpectation_factual (f : σ → ℝ) {ds : List (BinaryInterventionStage σ τ)}
    (π : CoAdaptedPolicy ds) :
    trajectoryExpectation (fun x _ => f x) π = fun x _ => factualExpectation f ds x := by
  induction π with
  | stop => rfl
  | @cons d ds C π ih =>
    funext x y
    change pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation (fun x _ => f x) π) x y) = _
    rw [ih]
    exact pairingExpectation_factual (C x y) (fun a => factualExpectation f ds (d.factualNext x a))

theorem trajectoryExpectation_counterfactual (f : τ → ℝ) {ds : List (BinaryInterventionStage σ τ)}
    (π : CoAdaptedPolicy ds) :
    trajectoryExpectation (fun _ y => f y) π = fun _ y => counterfactualExpectation f ds y := by
  induction π with
  | stop => rfl
  | @cons d ds C π ih =>
    funext x y
    change pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation (fun _ y => f y) π) x y) = _
    rw [ih]
    exact pairingExpectation_counterfactual (C x y)
      (fun b => counterfactualExpectation f ds (d.counterfactualNext y b))

theorem trajectoryExpectation_mono {g h : σ → τ → ℝ} (hle : ∀ x y, g x y ≤ h x y)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    ∀ x y, trajectoryExpectation g π x y ≤ trajectoryExpectation h π x y := by
  induction π with
  | stop => exact hle
  | @cons d ds C π ih =>
    intro x y
    exact pairingExpectation_mono (C x y) fun a b => ih (d.factualNext x a) (d.counterfactualNext y b)

private theorem pairingExpectation_const {p q : FailureRate} (C : Pairing p q) (r : ℝ) :
    pairingExpectation C (fun _ _ => r) = r := by
  rw [pairingExpectation_factual, Fintype.sum_bool, ← add_mul]
  have h : (failureLaw p true : ℝ) + failureLaw p false = 1 := by
    change (p.1 : ℝ) + ↑(1 - p.1) = 1
    rw [NNReal.coe_sub p.2, NNReal.coe_one]
    ring
  rw [h, one_mul]

private theorem trajectoryExpectation_const (r : ℝ) {ds : List (BinaryInterventionStage σ τ)}
    (π : CoAdaptedPolicy ds) : ∀ x y, trajectoryExpectation (fun _ _ => r) π x y = r := by
  induction π with
  | stop => intro x y; rfl
  | @cons d ds C π ih =>
    intro x y
    change pairingExpectation (C x y)
      (stageContinuation d (trajectoryExpectation (fun _ _ => r) π) x y) = r
    have he : stageContinuation d (trajectoryExpectation (fun _ _ => r) π) x y =
        fun _ _ => r := by
      funext a b
      exact ih (d.factualNext x a) (d.counterfactualNext y b)
    rw [he, pairingExpectation_const]

private theorem pairingExpectation_sub_payoff {p q : FailureRate} (C : Pairing p q)
    (f g : Bool → Bool → ℝ) :
    pairingExpectation C (fun a b => f a b - g a b) = pairingExpectation C f - pairingExpectation C g := by
  simp only [pairingExpectation, mul_sub, Finset.sum_sub_distrib]

theorem trajectoryExpectation_sub_payoff (f g : σ → τ → ℝ)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    trajectoryExpectation (fun x y => f x y - g x y) π =
      fun x y => trajectoryExpectation f π x y - trajectoryExpectation g π x y := by
  induction π with
  | stop => rfl
  | @cons d ds C π ih =>
    funext x y
    change pairingExpectation (C x y)
      (stageContinuation d (trajectoryExpectation (fun x y => f x y - g x y) π) x y) = _
    rw [ih]
    exact pairingExpectation_sub_payoff (C x y) _ _

theorem trajectoryExpectation_mem_Icc (g : σ → τ → ℝ) (hg : ∀ x y, g x y ∈ Icc 0 1)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    ∀ x y, trajectoryExpectation g π x y ∈ Icc 0 1 := by
  induction π with
  | stop => exact hg
  | @cons d ds C π ih =>
    intro x y
    let f := stageContinuation d (trajectoryExpectation g π) x y
    change pairingExpectation (C x y) f ∈ Icc 0 1
    have h₀ := pairingExpectation_mono (C x y) (f := fun _ _ => 0) (g := f)
      fun a b => (ih (d.factualNext x a) (d.counterfactualNext y b)).1
    have h₁ := pairingExpectation_mono (C x y) (f := f) (g := fun _ _ => 1)
      fun a b => (ih (d.factualNext x a) (d.counterfactualNext y b)).2
    rw [pairingExpectation_const] at h₀ h₁
    exact ⟨h₀, h₁⟩

/-- Terminal cost for a factual failure rescued by the intervention. -/
def terminalRescueCost (f : σ → Bool) (g : τ → Bool) (x : σ) (y : τ) : ℝ :=
  if f x && !(g y) then 1 else 0

private theorem terminalRescueCost_mem_Icc (f : σ → Bool) (g : τ → Bool) (x : σ) (y : τ) :
    terminalRescueCost f g x y ∈ Icc 0 1 := by
  unfold terminalRescueCost
  split
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Factual failure mass is the common denominator of all necessity probabilities. -/
def factualFailureMass (f : σ → Bool) (ds : List (BinaryInterventionStage σ τ)) (x : σ) : ℝ :=
  factualExpectation (fun z => if f z then 1 else 0) ds x

/-- Failure mass under the intervention, independent of the pairing. -/
def counterfactualFailureMass (g : τ → Bool) (ds : List (BinaryInterventionStage σ τ)) (y : τ) : ℝ :=
  counterfactualExpectation (fun z => if g z then 1 else 0) ds y

theorem factualFailureMass_eq_trajectoryExpectation (f : σ → Bool)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) (x : σ) (y : τ) :
    trajectoryExpectation (fun z _ => if f z then 1 else 0) π x y = factualFailureMass f ds x := by
  rw [trajectoryExpectation_factual]
  rfl

/-- Every causal policy respects the unrestricted terminal Fréchet bounds. -/
theorem terminalRescue_frechet_bounds (f : σ → Bool) (g : τ → Bool)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) (x : σ) (y : τ) :
    trajectoryExpectation (terminalRescueCost f g) π x y ∈
      Icc (max 0 (factualFailureMass f ds x - counterfactualFailureMass g ds y))
        (min (factualFailureMass f ds x) (1 - counterfactualFailureMass g ds y)) := by
  let f₀ (z : σ) : ℝ := if f z then 1 else 0
  let g₀ (z : τ) : ℝ := if g z then 1 else 0
  have h (z : σ) (w : τ) : f₀ z - g₀ w ≤ terminalRescueCost f g z w ∧
      terminalRescueCost f g z w ≤ f₀ z ∧ terminalRescueCost f g z w ≤ 1 - g₀ w := by
    cases hf : f z <;> cases hg : g w <;> norm_num [f₀, g₀, terminalRescueCost, hf, hg]
  have hlo := trajectoryExpectation_mono (fun z w => (h z w).1) π x y
  rw [trajectoryExpectation_sub_payoff, trajectoryExpectation_factual, trajectoryExpectation_counterfactual] at hlo
  have hhi := trajectoryExpectation_mono (fun z w => (h z w).2.1) π x y
  rw [trajectoryExpectation_factual] at hhi
  have hc := trajectoryExpectation_mono (fun z w => (h z w).2.2) π x y
  rw [trajectoryExpectation_sub_payoff] at hc
  change trajectoryExpectation (terminalRescueCost f g) π x y ≤
    trajectoryExpectation (fun _ _ => 1) π x y - trajectoryExpectation (fun _ w => g₀ w) π x y at hc
  rw [trajectoryExpectation_const, trajectoryExpectation_counterfactual g₀ π] at hc
  exact ⟨max_le (trajectoryExpectation_mem_Icc _ (terminalRescueCost_mem_Icc f g) π x y).1 hlo,
    le_min hhi hc⟩

theorem coAdaptedRescueValue_frechet_bounds (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    coAdaptedValue (terminalRescueCost f g) ds x y ∈
      Icc (max 0 (factualFailureMass f ds x - counterfactualFailureMass g ds y))
        (min (factualFailureMass f ds x) (1 - counterfactualFailureMass g ds y)) := by
  rw [← trajectoryExpectation_optimalCoAdaptedPolicy]
  exact terminalRescue_frechet_bounds f g _ x y

/-- Necessity probability conditional on factual failure. -/
def policyNecessity (f : σ → Bool) (g : τ → Bool) {ds : List (BinaryInterventionStage σ τ)}
    (π : CoAdaptedPolicy ds) (x : σ) (y : τ) : ℝ :=
  trajectoryExpectation (terminalRescueCost f g) π x y / factualFailureMass f ds x

theorem policyNecessity_mem_Icc (f : σ → Bool) (g : τ → Bool)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) (x : σ) (y : τ)
    (hfail : 0 < factualFailureMass f ds x) :
    policyNecessity f g π x y ∈ Icc 0 1 := by
  have h := terminalRescue_frechet_bounds f g π x y
  exact ⟨div_nonneg ((le_max_left _ _).trans h.1) hfail.le,
    (div_le_iff₀ hfail).mpr (by rw [one_mul]; exact h.2.trans (min_le_left _ _))⟩

/-- The optimal co-adapted necessity probability is the backward rescue
value divided by the fixed factual failure mass. -/
theorem coAdaptedNecessity_isLeast (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ)
    (hfail : 0 < factualFailureMass f ds x) :
    IsLeast {r | ∃ π : CoAdaptedPolicy ds, AdmissiblePolicy π ∧ policyNecessity f g π x y = r}
      (coAdaptedValue (terminalRescueCost f g) ds x y / factualFailureMass f ds x) := by
  refine ⟨⟨optimalCoAdaptedPolicy (terminalRescueCost f g) ds,
    admissible_optimalCoAdaptedPolicy _ _, ?_⟩, ?_⟩
  · rw [policyNecessity, trajectoryExpectation_optimalCoAdaptedPolicy]
  · rintro _ ⟨π, hπ, rfl⟩
    exact div_le_div_of_nonneg_right (coAdaptedValue_le_trajectoryExpectation _ π hπ x y) hfail.le

/-- Policy selecting the minimum-disagreement coupling at each step. -/
def sharedThresholdPolicy : (ds : List (BinaryInterventionStage σ τ)) → CoAdaptedPolicy ds
  | [] => .stop
  | d :: ds => .cons (fun x y => sharedPairing (d.factualRate x) (d.counterfactualRate y))
    (sharedThresholdPolicy ds)

theorem admissible_sharedThresholdPolicy (ds : List (BinaryInterventionStage σ τ)) :
    AdmissiblePolicy (sharedThresholdPolicy ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨fun x y => admissible_sharedPairing _ _, ih⟩

/-- A pairing minimizes the disagreement probability at every stage and state pair. -/
def StepwiseMaximalPolicy : {ds : List (BinaryInterventionStage σ τ)} → CoAdaptedPolicy ds → Prop
  | [], .stop => True
  | d :: _, .cons C π => (∀ x y, rescue (C x y) + harm (C x y) =
      |((d.factualRate x).1 : ℝ) - (d.counterfactualRate y).1|) ∧ StepwiseMaximalPolicy π

private theorem stepwiseMaximal_sharedThresholdPolicy (ds : List (BinaryInterventionStage σ τ)) :
    StepwiseMaximalPolicy (sharedThresholdPolicy ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨fun x y => sharedPairing_disagreement _ _, ih⟩

/-- Minimum disagreement at every binary transition fixes the whole
co-adapted policy of conditional pairing laws. -/
theorem stepwiseMaximalPolicy_iff_eq_shared {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    StepwiseMaximalPolicy π ↔ π = sharedThresholdPolicy ds := by
  refine ⟨?_, fun he => he.symm ▸ stepwiseMaximal_sharedThresholdPolicy ds⟩
  induction π with
  | stop => intro _; rfl
  | @cons d ds C π ih =>
    intro h
    have hc : C = fun x y => sharedPairing (d.factualRate x) (d.counterfactualRate y) := by
      funext x y
      obtain ⟨D, _, hD⟩ := existsUnique_minimum_disagreement (d.factualRate x) (d.counterfactualRate y)
      exact (hD (C x y) (h.1 x y)).trans
        ((hD _ (sharedPairing_disagreement (d.factualRate x) (d.counterfactualRate y))).symm)
    change CoAdaptedPolicy.cons C π =
      CoAdaptedPolicy.cons (fun x y => sharedPairing (d.factualRate x) (d.counterfactualRate y))
        (sharedThresholdPolicy ds)
    rw [hc, ih h.2]

/-- A single observation with the intervened branch flipped before decoding. -/
def bitFlipInterventionStage (p q : FailureRate) : BinaryInterventionStage Bool Bool :=
  ⟨fun _ => p, fun _ => q, fun _ a => a, fun _ b => !b⟩

/-- Both runs decode their final bit. Flipping the intervened branch before
decoding makes the shared threshold excess equal the width of the rescue interval. -/
theorem sharedThreshold_terminalRescue_gap (p q : FailureRate) (hpq : p ≠ q) :
    let ds := [bitFlipInterventionStage p q]
    let g := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y)
    trajectoryExpectation g (sharedThresholdPolicy ds) false false - coAdaptedValue g ds false false =
      upperRescueMass p q - lowerRescueMass p q := by
  let f (a b : Bool) := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y) a (!b)
  have hc : rescueContrast f = -1 := by norm_num [f, rescueContrast, terminalRescueCost]
  have hn : ¬(p = q ∨ 0 ≤ rescueContrast f) := by rw [hc]; exact not_or.mpr ⟨hpq, by norm_num⟩
  change pairingExpectation (sharedPairing p q) f - pairingExpectation (continuationOptimalPairing p q f) f = _
  rw [pairingExpectation_sub, continuationOptimalPairing, if_neg hn,
    rescue_sharedPairing, rescue_upperRescuePairing, hc]
  ring

theorem sharedThreshold_strictly_suboptimal_for_terminalRescue (p q : FailureRate)
    (hpq : p ≠ q) (hspan : lowerRescueMass p q < upperRescueMass p q) :
    let ds := [bitFlipInterventionStage p q]
    let g := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y)
    coAdaptedValue g ds false false < trajectoryExpectation g (sharedThresholdPolicy ds) false false := by
  apply sub_pos.mp
  rw [sharedThreshold_terminalRescue_gap p q hpq]
  exact sub_pos.mpr hspan

/-- Equal interior branch rates force agreement before the intervened
flip. The best admissible rescue mass then exceeds the unrestricted
lower bound based on terminal marginals alone. -/
theorem flip_equalRates_strict_terminalFrechet_gap (p : FailureRate)
    (hp₀ : 0 < (p.1 : ℝ)) (hp₁ : (p.1 : ℝ) < 1) :
    let ds := [bitFlipInterventionStage p p]
    let g := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y)
    max 0 (factualFailureMass (fun x => x) ds false - counterfactualFailureMass (fun y => y) ds false) <
      coAdaptedValue g ds false false := by
  let ds := [bitFlipInterventionStage p p]
  let g := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y)
  have hF : factualFailureMass (fun x => x) ds false = (p.1 : ℝ) := by
    simp [ds, factualFailureMass, factualExpectation, bitFlipInterventionStage, failureLaw]
  have hQ : counterfactualFailureMass (fun y => y) ds false = 1 - (p.1 : ℝ) := by
    simp [ds, counterfactualFailureMass, counterfactualExpectation, bitFlipInterventionStage,
      failureLaw, NNReal.coe_sub p.2]
  have hV : coAdaptedValue g ds false false = (p.1 : ℝ) := by
    let f (a b : Bool) := terminalRescueCost (fun x : Bool => x) (fun y : Bool => y) a (!b)
    change pairingExpectation (continuationOptimalPairing p p f) f = _
    rw [continuationOptimalPairing, if_pos (Or.inl rfl)]
    have hz := (admissiblePairing_iff_equal_outcomes (sharedPairing p p)).mp
      (admissible_sharedPairing p p) rfl true false (by intro h; cases h)
    have hr := (sharedPairing p p).row true
    rw [Fintype.sum_bool, hz, add_zero] at hr
    change (sharedPairing p p).plan true true = p.1 at hr
    simp [pairingExpectation, f, terminalRescueCost, hr]
  change max 0 (factualFailureMass (fun x => x) ds false - counterfactualFailureMass (fun y => y) ds false)
    < coAdaptedValue g ds false false
  rw [hF, hQ, hV]
  exact max_lt hp₀ (by linarith only [hp₁])

#print axioms coAdaptedValue_isLeast
#print axioms trajectoryExpectation_factual
#print axioms trajectoryExpectation_counterfactual
#print axioms trajectoryExpectation_mem_Icc
#print axioms terminalRescue_frechet_bounds
#print axioms coAdaptedRescueValue_frechet_bounds
#print axioms policyNecessity_mem_Icc
#print axioms coAdaptedNecessity_isLeast
#print axioms stepwiseMaximalPolicy_iff_eq_shared
#print axioms sharedThreshold_terminalRescue_gap
#print axioms sharedThreshold_strictly_suboptimal_for_terminalRescue
#print axioms flip_equalRates_strict_terminalFrechet_gap

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
