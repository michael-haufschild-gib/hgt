import GaloisForLFunctions.HilbertMetric.Probability.Interventions.CoAdaptedBellman

/-!
# Cost of requiring the diagonal coupling at equal rates

The unrestricted Bellman value gives a nonnegative local loss for each
pairing. Total excess is the expected sum of these losses. Its vanishing
can be checked along the positive-probability branches of an admissible policy.
-/

open Set
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions

noncomputable section

variable {σ τ : Type*}

/-- With either endpoint available, the sign of the contrast chooses the minimizing one. -/
def unrestrictedPairing (p q : FailureRate) (f : Bool → Bool → ℝ) : Pairing p q :=
  if 0 ≤ rescueContrast f then sharedPairing p q else upperRescuePairing p q

theorem unrestrictedPairing_le {p q : FailureRate} (f : Bool → Bool → ℝ) (C : Pairing p q) :
    pairingExpectation (unrestrictedPairing p q f) f ≤ pairingExpectation C f := by
  apply sub_nonneg.mp
  rw [pairingExpectation_sub]
  by_cases hs : 0 ≤ rescueContrast f
  · rw [unrestrictedPairing, if_pos hs, rescue_sharedPairing]
    exact mul_nonneg (sub_nonneg.mpr (rescue_mem_Icc C).1) hs
  · rw [unrestrictedPairing, if_neg hs, rescue_upperRescuePairing]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (rescue_mem_Icc C).2) (le_of_not_ge hs)

/-- Local cost of the diagonal requirement for the given continuation. -/
def diagonalCharge (p q : FailureRate) (f : Bool → Bool → ℝ) : ℝ :=
  if p = q then (upperRescueMass p q - lowerRescueMass p q) * max 0 (-rescueContrast f) else 0

/-- A negative contrast charges the available width only at equal rates. -/
theorem diagonalCharge_eq_sub (p q : FailureRate) (f : Bool → Bool → ℝ) :
    diagonalCharge p q f = pairingExpectation (continuationOptimalPairing p q f) f -
      pairingExpectation (unrestrictedPairing p q f) f := by
  by_cases he : p = q
  · rw [diagonalCharge, if_pos he, continuationOptimalPairing, if_pos (Or.inl he)]
    by_cases hs : 0 ≤ rescueContrast f
    · rw [unrestrictedPairing, if_pos hs, max_eq_left (neg_nonpos.mpr hs), mul_zero, sub_self]
    · rw [unrestrictedPairing, if_neg hs, pairingExpectation_sub, rescue_sharedPairing,
        rescue_upperRescuePairing, max_eq_right (neg_nonneg.mpr (le_of_not_ge hs))]
      ring
  · by_cases hs : 0 ≤ rescueContrast f
    · rw [diagonalCharge, if_neg he, continuationOptimalPairing, if_pos (Or.inr hs),
        unrestrictedPairing, if_pos hs, sub_self]
    · rw [diagonalCharge, if_neg he, continuationOptimalPairing, if_neg (not_or.mpr ⟨he, hs⟩),
        unrestrictedPairing, if_neg hs, sub_self]

/-- Exact local criterion for when the diagonal requirement raises the minimum. -/
theorem diagonalCharge_pos_iff (p q : FailureRate) (f : Bool → Bool → ℝ) :
    0 < diagonalCharge p q f ↔
      p = q ∧ lowerRescueMass p q < upperRescueMass p q ∧ rescueContrast f < 0 := by
  by_cases he : p = q
  · rw [diagonalCharge, if_pos he, and_iff_right he]
    let w := upperRescueMass p q - lowerRescueMass p q
    let c := -rescueContrast f
    change 0 < w * max 0 c ↔ lowerRescueMass p q < upperRescueMass p q ∧ rescueContrast f < 0
    constructor
    · intro h
      have hw : 0 < w := lt_of_le_of_ne (sub_nonneg.mpr (lowerRescueMass_le_upper p q)) (by
        intro hz
        rw [← hz, zero_mul] at h
        exact lt_irrefl _ h)
      have hc : 0 < c := by
        by_contra! hc
        rw [max_eq_left hc, mul_zero] at h
        exact lt_irrefl _ h
      exact ⟨sub_pos.mp hw, neg_pos.mp hc⟩
    · intro h
      exact mul_pos (sub_pos.mpr h.1) ((neg_pos.mpr h.2).trans_le (le_max_right _ _))
  · rw [diagonalCharge, if_neg he]
    simp only [lt_irrefl, he, false_and]

/-- Backward value over all co-adapted pairings of the prescribed marginals. -/
def unrestrictedValue (g : σ → τ → ℝ) : List (BinaryInterventionStage σ τ) → σ → τ → ℝ
  | [] => g
  | d :: ds => fun x y =>
    let f := stageContinuation d (unrestrictedValue g ds) x y
    pairingExpectation (unrestrictedPairing (d.factualRate x) (d.counterfactualRate y) f) f

/-- Pointwise endpoint choices realize the unrestricted value. -/
def unrestrictedOptimalPolicy (g : σ → τ → ℝ) : (ds : List (BinaryInterventionStage σ τ)) → CoAdaptedPolicy ds
  | [] => .stop
  | d :: ds => .cons (fun x y => unrestrictedPairing (d.factualRate x) (d.counterfactualRate y)
      (stageContinuation d (unrestrictedValue g ds) x y)) (unrestrictedOptimalPolicy g ds)

theorem trajectoryExpectation_unrestrictedOptimalPolicy (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) :
    trajectoryExpectation g (unrestrictedOptimalPolicy g ds) = unrestrictedValue g ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    funext x y
    let f := stageContinuation d (unrestrictedValue g ds) x y
    change pairingExpectation (unrestrictedPairing (d.factualRate x) (d.counterfactualRate y) f)
      (stageContinuation d (trajectoryExpectation g (unrestrictedOptimalPolicy g ds)) x y) = _
    rw [ih]
    rfl

theorem unrestrictedValue_le_trajectoryExpectation (g : σ → τ → ℝ)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) :
    ∀ x y, unrestrictedValue g ds x y ≤ trajectoryExpectation g π x y := by
  induction π with
  | stop => intro x y; exact le_rfl
  | @cons d ds C π ih =>
    intro x y
    let f := stageContinuation d (unrestrictedValue g ds) x y
    change pairingExpectation (unrestrictedPairing (d.factualRate x) (d.counterfactualRate y) f) f ≤
      pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation g π) x y)
    exact (unrestrictedPairing_le f (C x y)).trans
      (pairingExpectation_mono (C x y) fun a b => ih (d.factualNext x a) (d.counterfactualNext y b))

theorem unrestrictedValue_isLeast (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    IsLeast {z | ∃ π : CoAdaptedPolicy ds, trajectoryExpectation g π x y = z}
      (unrestrictedValue g ds x y) := by
  refine ⟨⟨unrestrictedOptimalPolicy g ds, ?_⟩, ?_⟩
  · rw [trajectoryExpectation_unrestrictedOptimalPolicy]
  · rintro _ ⟨π, rfl⟩
    exact unrestrictedValue_le_trajectoryExpectation g π x y

theorem unrestrictedValue_le_coAdaptedValue (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    unrestrictedValue g ds x y ≤ coAdaptedValue g ds x y := by
  rw [← trajectoryExpectation_optimalCoAdaptedPolicy]
  exact unrestrictedValue_le_trajectoryExpectation g (optimalCoAdaptedPolicy g ds) x y

/-- The local loss compares a prescribed pairing with an unrestricted optimal
pairing using the same unrestricted continuation values. -/
def pairingLoss (g : σ → τ → ℝ) (d : BinaryInterventionStage σ τ)
    (ds : List (BinaryInterventionStage σ τ)) (C : StagePairing d) (x : σ) (y : τ) : ℝ :=
  pairingExpectation (C x y) (stageContinuation d (unrestrictedValue g ds) x y) -
    unrestrictedValue g (d :: ds) x y

theorem pairingLoss_nonneg (g : σ → τ → ℝ) (d : BinaryInterventionStage σ τ)
    (ds : List (BinaryInterventionStage σ τ)) (C : StagePairing d) (x : σ) (y : τ) :
    0 ≤ pairingLoss g d ds C x y :=
  sub_nonneg.mpr (unrestrictedPairing_le (stageContinuation d (unrestrictedValue g ds) x y) (C x y))

/-- A local loss vanishes when the continuation is flat in rescue mass or
the pairing is the minimizing endpoint. -/
theorem pairingLoss_eq_zero_iff (g : σ → τ → ℝ) (d : BinaryInterventionStage σ τ)
    (ds : List (BinaryInterventionStage σ τ)) (C : StagePairing d) (x : σ) (y : τ) :
    let f := stageContinuation d (unrestrictedValue g ds) x y
    pairingLoss g d ds C x y = 0 ↔
      rescueContrast f = 0 ∨ C x y = unrestrictedPairing (d.factualRate x) (d.counterfactualRate y) f := by
  let f := stageContinuation d (unrestrictedValue g ds) x y
  let D := unrestrictedPairing (d.factualRate x) (d.counterfactualRate y) f
  change pairingExpectation (C x y) f - pairingExpectation D f = 0 ↔
    rescueContrast f = 0 ∨ C x y = D
  rw [pairingExpectation_sub, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inr (pairing_ext h)
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (congrArg rescue h)

private theorem pairingExpectation_sub_continuation {p q : FailureRate}
    (C : Pairing p q) (f h : Bool → Bool → ℝ) :
    pairingExpectation C (fun a b => f a b - h a b) = pairingExpectation C f - pairingExpectation C h := by
  simp only [pairingExpectation, mul_sub, Finset.sum_sub_distrib]

/-- Expected cumulative losses under a fixed policy. -/
def policyLoss (g : σ → τ → ℝ) :
    {ds : List (BinaryInterventionStage σ τ)} → CoAdaptedPolicy ds → σ → τ → ℝ
  | [], .stop => fun _ _ => 0
  | d :: ds, .cons C π => fun x y =>
    pairingLoss g d ds C x y + pairingExpectation (C x y) (stageContinuation d (policyLoss g π) x y)

/-- A policy's excess over the unrestricted optimum is its expected cumulative loss. -/
theorem trajectoryExpectation_sub_unrestrictedValue (g : σ → τ → ℝ)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) (x : σ) (y : τ) :
    trajectoryExpectation g π x y - unrestrictedValue g ds x y = policyLoss g π x y := by
  induction π generalizing x y with
  | stop => exact sub_self _
  | @cons d ds C π ih =>
    have htail : policyLoss g π = fun z w => trajectoryExpectation g π z w - unrestrictedValue g ds z w :=
      funext fun z => funext fun w => (ih z w).symm
    change pairingExpectation (C x y) (stageContinuation d (trajectoryExpectation g π) x y) -
      unrestrictedValue g (d :: ds) x y = pairingLoss g d ds C x y +
        pairingExpectation (C x y) (stageContinuation d (policyLoss g π) x y)
    rw [htail, pairingLoss]
    change _ = _ + pairingExpectation (C x y) (fun a b =>
      stageContinuation d (trajectoryExpectation g π) x y a b -
        stageContinuation d (unrestrictedValue g ds) x y a b)
    rw [pairingExpectation_sub_continuation]
    ring

/-- A policy loses nothing if every pairing is optimal for the unrestricted
continuation at the states visited with positive probability. -/
def ZeroLossOnSupport (g : σ → τ → ℝ) :
    {ds : List (BinaryInterventionStage σ τ)} → CoAdaptedPolicy ds → σ → τ → Prop
  | [], .stop => fun _ _ => True
  | d :: ds, .cons C π => fun x y =>
    pairingLoss g d ds C x y = 0 ∧
      ∀ a b, 0 < (C x y).plan a b → ZeroLossOnSupport g π (d.factualNext x a) (d.counterfactualNext y b)

private theorem pairingExpectation_eq_zero_iff {p q : FailureRate}
    (C : Pairing p q) (f : Bool → Bool → ℝ) (hf : ∀ a b, 0 ≤ f a b) :
    pairingExpectation C f = 0 ↔ ∀ a b, 0 < C.plan a b → f a b = 0 := by
  have hterm (a b : Bool) : 0 ≤ (C.plan a b : ℝ) * f a b := mul_nonneg (C.plan a b).2 (hf a b)
  constructor
  · intro h a b hw
    have hb : (C.plan a b : ℝ) * f a b ≤ ∑ j, (C.plan a j : ℝ) * f a j :=
      Finset.single_le_sum (fun j _ => hterm a j) (Finset.mem_univ b)
    have ha : (∑ j, (C.plan a j : ℝ) * f a j) ≤ pairingExpectation C f :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hterm i j) (Finset.mem_univ a)
    have hz := le_antisymm ((hb.trans ha).trans_eq h) (hterm a b)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (show 0 < (C.plan a b : ℝ) from hw))
  · intro h
    unfold pairingExpectation
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases w : 0 < C.plan a b
    · rw [h a b w, mul_zero]
    · have hz := le_antisymm (le_of_not_gt w) zero_le
      rw [hz, NNReal.coe_zero, zero_mul]

theorem policyLoss_eq_zero_iff (g : σ → τ → ℝ)
    {ds : List (BinaryInterventionStage σ τ)} (π : CoAdaptedPolicy ds) (x : σ) (y : τ) :
    policyLoss g π x y = 0 ↔ ZeroLossOnSupport g π x y := by
  induction π generalizing x y with
  | stop => simp only [policyLoss, ZeroLossOnSupport]
  | @cons d ds C π ih =>
    let f := stageContinuation d (policyLoss g π) x y
    have hf (a b : Bool) : 0 ≤ f a b := by
      change 0 ≤ policyLoss g π (d.factualNext x a) (d.counterfactualNext y b)
      rw [← trajectoryExpectation_sub_unrestrictedValue]
      exact sub_nonneg.mpr (unrestrictedValue_le_trajectoryExpectation g π _ _)
    have he : 0 ≤ pairingExpectation (C x y) f :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg ((C x y).plan a b).2 (hf a b)
    have hl := pairingLoss_nonneg g d ds C x y
    change pairingLoss g d ds C x y + pairingExpectation (C x y) f = 0 ↔
      pairingLoss g d ds C x y = 0 ∧ ∀ a b, 0 < (C x y).plan a b → _
    constructor
    · intro h
      have h₁ : pairingLoss g d ds C x y = 0 := le_antisymm (by linarith only [h, he]) hl
      have h₂ : pairingExpectation (C x y) f = 0 := le_antisymm (by linarith only [h, hl]) he
      exact ⟨h₁, fun a b hw => (ih _ _).mp ((pairingExpectation_eq_zero_iff (C x y) f hf).mp h₂ a b hw)⟩
    · rintro ⟨h₁, h₂⟩
      have h₂' := (pairingExpectation_eq_zero_iff (C x y) f hf).mpr fun a b hw => (ih _ _).mpr (h₂ a b hw)
      rw [h₁, h₂', add_zero]

/-- The exact global equality criterion involves only one admissible policy
and its reachable states. -/
theorem coAdaptedValue_eq_unrestrictedValue_iff (g : σ → τ → ℝ)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    coAdaptedValue g ds x y = unrestrictedValue g ds x y ↔
      ∃ π : CoAdaptedPolicy ds, AdmissiblePolicy π ∧ ZeroLossOnSupport g π x y := by
  constructor
  · intro h
    refine ⟨optimalCoAdaptedPolicy g ds, admissible_optimalCoAdaptedPolicy g ds, (policyLoss_eq_zero_iff g _ x y).mp ?_⟩
    rw [← trajectoryExpectation_sub_unrestrictedValue, trajectoryExpectation_optimalCoAdaptedPolicy, h, sub_self]
  · rintro ⟨π, hπ, hzero⟩
    have he := (policyLoss_eq_zero_iff g π x y).mpr hzero
    rw [← trajectoryExpectation_sub_unrestrictedValue, sub_eq_zero] at he
    exact le_antisymm ((coAdaptedValue_le_trajectoryExpectation g π hπ x y).trans_eq he)
      (unrestrictedValue_le_coAdaptedValue g ds x y)

/-- Minimize each admissible step against the unrestricted continuation. -/
def diagonalGreedyPolicy (g : σ → τ → ℝ) : (ds : List (BinaryInterventionStage σ τ)) → CoAdaptedPolicy ds
  | [] => .stop
  | d :: ds => .cons (fun x y => continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y)
      (stageContinuation d (unrestrictedValue g ds) x y)) (diagonalGreedyPolicy g ds)

theorem admissible_diagonalGreedyPolicy (g : σ → τ → ℝ) (ds : List (BinaryInterventionStage σ τ)) :
    AdmissiblePolicy (diagonalGreedyPolicy g ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨fun x y => admissible_continuationOptimalPairing _ _ _, ih⟩

/-- Under this policy, each local loss is exactly the charge for requiring
the diagonal at equal rates. -/
theorem policyLoss_diagonalGreedyPolicy_cons (g : σ → τ → ℝ)
    (d : BinaryInterventionStage σ τ) (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    let f := stageContinuation d (unrestrictedValue g ds) x y
    let C := continuationOptimalPairing (d.factualRate x) (d.counterfactualRate y) f
    policyLoss g (diagonalGreedyPolicy g (d :: ds)) x y =
      diagonalCharge (d.factualRate x) (d.counterfactualRate y) f +
        pairingExpectation C (stageContinuation d (policyLoss g (diagonalGreedyPolicy g ds)) x y) := by
  dsimp only
  rw [diagonalCharge_eq_sub]
  rfl

/-- The first-step charge is unavoidable. Expected cumulative charges of
the greedy admissible policy give an upper bound. -/
theorem coAdaptedValue_sub_unrestrictedValue_bounds (g : σ → τ → ℝ)
    (d : BinaryInterventionStage σ τ) (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    coAdaptedValue g (d :: ds) x y - unrestrictedValue g (d :: ds) x y ∈
      Icc (diagonalCharge (d.factualRate x) (d.counterfactualRate y)
        (stageContinuation d (unrestrictedValue g ds) x y))
        (policyLoss g (diagonalGreedyPolicy g (d :: ds)) x y) := by
  constructor
  · rw [diagonalCharge_eq_sub]
    apply sub_le_sub_right
    let f := stageContinuation d (unrestrictedValue g ds) x y
    let h := stageContinuation d (coAdaptedValue g ds) x y
    let p := d.factualRate x
    let q := d.counterfactualRate y
    change pairingExpectation (continuationOptimalPairing p q f) f ≤
      pairingExpectation (continuationOptimalPairing p q h) h
    exact (continuationOptimalPairing_le f _ (admissible_continuationOptimalPairing p q h)).trans
      (pairingExpectation_mono _ fun a b => unrestrictedValue_le_coAdaptedValue g ds
        (d.factualNext x a) (d.counterfactualNext y b))
  · rw [← trajectoryExpectation_sub_unrestrictedValue]
    exact sub_le_sub_right (coAdaptedValue_le_trajectoryExpectation g _
      (admissible_diagonalGreedyPolicy g (d :: ds)) x y) _

/-- For a single flipped intervened bit with equal branch rates, the
diagonal requirement costs exactly the smaller branch probability. -/
theorem bitFlip_diagonal_rescue_gap (p : FailureRate) :
    let ds := [bitFlipInterventionStage p p]
    let g := terminalRescueCost id id
    coAdaptedValue g ds false false - unrestrictedValue g ds false false = min (p.1 : ℝ) (1 - p.1) := by
  let f (a b : Bool) := terminalRescueCost id id a (!b)
  have hc : rescueContrast f = -1 := by norm_num [f, rescueContrast, terminalRescueCost]
  change pairingExpectation (continuationOptimalPairing p p f) f -
    pairingExpectation (unrestrictedPairing p p f) f = _
  rw [← diagonalCharge_eq_sub, diagonalCharge, if_pos rfl, hc, lowerRescueMass, upperRescueMass, sub_self, max_self]
  simp

/-- The diagonal premium is bounded by each of the four terminal
failure and success probabilities. -/
theorem diagonal_rescue_gap_le_marginals (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    let P := factualFailureMass f ds x
    let Q := counterfactualFailureMass g ds y
    coAdaptedValue (terminalRescueCost f g) ds x y - unrestrictedValue (terminalRescueCost f g) ds x y ≤
      min (min P (1 - P)) (min Q (1 - Q)) := by
  let P := factualFailureMass f ds x
  let Q := counterfactualFailureMass g ds y
  have hhi := (coAdaptedRescueValue_frechet_bounds f g ds x y).2
  have hlo := (terminalRescue_frechet_bounds f g (unrestrictedOptimalPolicy (terminalRescueCost f g) ds) x y).1
  rw [trajectoryExpectation_unrestrictedOptimalPolicy] at hlo
  have hwidth : min P (1 - Q) - max 0 (P - Q) ≤ min (min P (1 - P)) (min Q (1 - Q)) := by
    have h₀ := sub_le_self (min P (1 - Q)) (le_max_left 0 (P - Q))
    have h₁ := sub_le_sub (min_le_left P (1 - Q)) (le_max_right 0 (P - Q))
    have h₂ := sub_le_sub (min_le_right P (1 - Q)) (le_max_right 0 (P - Q))
    exact le_min (le_min (h₀.trans (min_le_left _ _)) (by linarith only [h₂]))
      (le_min (by linarith only [h₁]) (h₀.trans (min_le_right _ _)))
  exact (sub_le_sub hhi hlo).trans hwidth

/-- The diagonal rule can raise a rescue probability by at most one half,
uniformly over horizons, decoders, and initial states. -/
theorem diagonal_rescue_gap_le_half (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    coAdaptedValue (terminalRescueCost f g) ds x y - unrestrictedValue (terminalRescueCost f g) ds x y ≤ 1 / 2 := by
  let P := factualFailureMass f ds x
  have h := diagonal_rescue_gap_le_marginals f g ds x y
  apply h.trans ((min_le_left _ _).trans ?_)
  by_cases hp : P ≤ 1 / 2
  · exact (min_le_left _ _).trans hp
  · refine (min_le_right _ _).trans ?_
    linarith only [lt_of_not_ge hp]

/-- Saturation requires balanced terminal marginals and both extreme
rescue values. -/
theorem diagonal_rescue_gap_eq_half_iff (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    let P := factualFailureMass f ds x
    let Q := counterfactualFailureMass g ds y
    let R := coAdaptedValue (terminalRescueCost f g) ds x y
    let U := unrestrictedValue (terminalRescueCost f g) ds x y
    R - U = 1 / 2 ↔ P = 1 / 2 ∧ Q = 1 / 2 ∧ R = 1 / 2 ∧ U = 0 := by
  let P := factualFailureMass f ds x
  let Q := counterfactualFailureMass g ds y
  let R := coAdaptedValue (terminalRescueCost f g) ds x y
  let U := unrestrictedValue (terminalRescueCost f g) ds x y
  change R - U = 1 / 2 ↔ P = 1 / 2 ∧ Q = 1 / 2 ∧ R = 1 / 2 ∧ U = 0
  constructor
  · intro h
    have hb : R - U ≤ min (min P (1 - P)) (min Q (1 - Q)) := diagonal_rescue_gap_le_marginals f g ds x y
    rw [h] at hb
    have hp := hb.trans (min_le_left _ _)
    have hq := hb.trans (min_le_right _ _)
    have hp' : P = 1 / 2 := by
      linarith only [hp.trans (min_le_left P (1 - P)), hp.trans (min_le_right P (1 - P))]
    have hq' : Q = 1 / 2 := by
      linarith only [hq.trans (min_le_left Q (1 - Q)), hq.trans (min_le_right Q (1 - Q))]
    have hr : R ≤ P := (coAdaptedRescueValue_frechet_bounds f g ds x y).2.trans (min_le_left _ _)
    have hu := (terminalRescue_frechet_bounds f g (unrestrictedOptimalPolicy (terminalRescueCost f g) ds) x y).1
    rw [trajectoryExpectation_unrestrictedOptimalPolicy] at hu
    have hu₀ : 0 ≤ U := (le_max_left _ _).trans hu
    exact ⟨hp', hq', by linarith only [h, hr, hp', hu₀], by linarith only [h, hr, hp', hu₀]⟩
  · rintro ⟨_, _, hr, hu⟩
    rw [hr, hu, sub_zero]

/-- A fair binary flip attains the uniform half bound. -/
theorem exists_diagonal_rescue_gap_eq_half :
    ∃ p : FailureRate, let ds := [bitFlipInterventionStage p p]; let g := terminalRescueCost id id
      coAdaptedValue g ds false false - unrestrictedValue g ds false false = 1 / 2 := by
  let p : FailureRate := ⟨1 / 2, by norm_num⟩
  refine ⟨p, (bitFlip_diagonal_rescue_gap p).trans ?_⟩
  have hp : (p.1 : ℝ) = 1 / 2 := by
    change (((1 / 2 : ℝ≥0) : ℝ)) = 1 / 2
    push_cast
    rfl
  rw [hp]
  norm_num

/-- Normalizing by factual failures converts the rescue gap to a gap in
probability of necessity. It is bounded by the normalized marginal radius. -/
theorem diagonal_necessity_gap_bounds (f : σ → Bool) (g : τ → Bool)
    (ds : List (BinaryInterventionStage σ τ)) (x : σ) (y : τ) :
    let P := factualFailureMass f ds x
    let Q := counterfactualFailureMass g ds y
    coAdaptedValue (terminalRescueCost f g) ds x y / P - unrestrictedValue (terminalRescueCost f g) ds x y / P ∈
      Icc 0 (min 1 (min (min P (1 - P)) (min Q (1 - Q)) / P)) := by
  let P := factualFailureMass f ds x
  let Q := counterfactualFailureMass g ds y
  let M := min (min P (1 - P)) (min Q (1 - Q))
  let R := coAdaptedValue (terminalRescueCost f g) ds x y
  let U := unrestrictedValue (terminalRescueCost f g) ds x y
  change R / P - U / P ∈ Icc 0 (min 1 (M / P))
  rw [← sub_div]
  have hterminal := coAdaptedRescueValue_frechet_bounds f g ds x y
  have hp : 0 ≤ P := ((le_max_left _ _).trans (hterminal.1.trans hterminal.2)).trans (min_le_left _ _)
  have hRU : U ≤ R := unrestrictedValue_le_coAdaptedValue (terminalRescueCost f g) ds x y
  have hM : R - U ≤ M := diagonal_rescue_gap_le_marginals f g ds x y
  refine ⟨div_nonneg (sub_nonneg.mpr hRU) hp, le_min ?_ (div_le_div_of_nonneg_right hM hp)⟩
  by_cases hz : P = 0
  · rw [hz, div_zero]
    norm_num
  · apply (div_le_iff₀ (lt_of_le_of_ne hp (Ne.symm hz))).mpr
    rw [one_mul]
    exact hM.trans ((min_le_left _ _).trans (min_le_left _ _))

/-- The fair flip changes the optimal probability of necessity by one. -/
theorem exists_diagonal_necessity_gap_eq_one :
    ∃ p : FailureRate, let ds := [bitFlipInterventionStage p p]; let g := terminalRescueCost id id
      let P := factualFailureMass id ds false
      coAdaptedValue g ds false false / P - unrestrictedValue g ds false false / P = 1 := by
  obtain ⟨p, h⟩ := exists_diagonal_rescue_gap_eq_half
  refine ⟨p, ?_⟩
  have hp := ((diagonal_rescue_gap_eq_half_iff id id [bitFlipInterventionStage p p] false false).mp h).1
  dsimp only at h hp ⊢
  rw [← sub_div, h, hp]
  norm_num

#print axioms diagonalCharge_eq_sub
#print axioms diagonalCharge_pos_iff
#print axioms unrestrictedValue_isLeast
#print axioms pairingLoss_eq_zero_iff
#print axioms trajectoryExpectation_sub_unrestrictedValue
#print axioms coAdaptedValue_eq_unrestrictedValue_iff
#print axioms coAdaptedValue_sub_unrestrictedValue_bounds
#print axioms diagonal_rescue_gap_le_half
#print axioms diagonal_rescue_gap_eq_half_iff
#print axioms exists_diagonal_rescue_gap_eq_half
#print axioms diagonal_necessity_gap_bounds
#print axioms exists_diagonal_necessity_gap_eq_one

end

end GaloisForLFunctions.HilbertMetric.Probability.BernoulliInterventions
