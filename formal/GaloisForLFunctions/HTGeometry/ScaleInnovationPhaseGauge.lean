import GaloisForLFunctions.HTGeometry.ScaleInnovationHistoryBundle

/-!
# Scale innovation phase gauge

An affine anchor and a scale current reconstruct one unique formation history.  The positive
quadratic action of that history factors through the full pointwise sign action on the current,
although the recovery kernel itself remains faithful.  One anchored phase and the adjacent
phase holonomies reconstruct the whole gauge.  Thus positive formation is an exact local-phase
quotient, while orientation is connection data discarded by that quotient.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Potential obtained by integrating a scale current from one affine anchor. -/
def scaleInnovationPotential (anchor : ℝ) (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  anchor + scaleCurrentPrimitive r N

/-- Unique anchored history belonging to an anchor and a scale current. -/
def scaleInnovationHistory (anchor : ℝ) (r : ℕ → ℝ) : ℕ → ℝ :=
  scalePotentialInnovationHistory (scaleInnovationPotential anchor r)

/-- Positive formation action of a scale current. -/
def scaleInnovationAction (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 2 N,
    ((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ) * (r k) ^ (2 : ℕ)

/-- Pointwise phase-gauge action on the scale current. -/
def scaleInnovationGaugeCurrent (epsilon r : ℕ → ℝ) (N : ℕ) : ℝ :=
  epsilon N * r N

/-- The gauge which reflects exactly one scale. -/
def scaleInnovationSingleFlip (m N : ℕ) : ℝ :=
  if N = m then -1 else 1

/-- Adjacent parallel-transport datum of a scale phase gauge. -/
def scaleInnovationGaugeHolonomy (epsilon : ℕ → ℝ) (N : ℕ) : ℝ :=
  epsilon (N + 1) * epsilon N

/-- The recovered history has the integrated current as its potential. -/
theorem scaleInnovationHistory_potential
    (anchor : ℝ) (r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential (scaleInnovationHistory anchor r) N =
      scaleInnovationPotential anchor r N := by
  exact anchoredCesaroPotential_scalePotentialInnovationHistory _ hN

/-- The recovered history takes the prescribed affine anchor at scale two. -/
theorem scaleInnovationHistory_two (anchor : ℝ) (r : ℕ → ℝ) :
    scaleInnovationHistory anchor r 2 = anchor := by
  rw [scaleInnovationHistory, scalePotentialInnovationHistory_two,
    scaleInnovationPotential, scaleCurrentPrimitive_two]
  ring

/-- The high-pass projection of the recovered history is exactly the prescribed current. -/
theorem scaleInnovationHistory_current
    (anchor : ℝ) (r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass (scaleInnovationHistory anchor r) N = r N := by
  rw [scaleInnovationHistory,
    anchoredCesaroHighPass_scalePotentialInnovationHistory _ hN,
    scaleInnovationPotential, scaleInnovationPotential]
  have hp := scaleCurrentPrimitive_succ_sub r hN
  have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden] at hp ⊢
  linarith

/-- Anchor plus all innovations jointly reconstruct every original history tail. -/
theorem scaleInnovationHistory_reconstructs
    (a : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    scaleInnovationHistory (a 2) (anchoredCesaroHighPass a) n = a n := by
  have hcurrent : ∀ N, 2 ≤ N →
      anchoredCesaroHighPass
          (scaleInnovationHistory (a 2) (anchoredCesaroHighPass a)) N =
        anchoredCesaroHighPass a N := by
    intro N hN
    exact scaleInnovationHistory_current _ _ hN
  have htail :=
    (anchoredCesaroHighPass_eq_iff_tail_constantGauge
      (scaleInnovationHistory (a 2) (anchoredCesaroHighPass a)) a).mp hcurrent n hn
  rw [scaleInnovationHistory_two] at htail
  linarith

/-- The current action gains exactly one weighted innovation square at each scale. -/
theorem scaleInnovationAction_succ_sub
    (r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    scaleInnovationAction r (N + 1) - scaleInnovationAction r N =
      ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) * (r N) ^ (2 : ℕ) := by
  unfold scaleInnovationAction
  rw [Finset.sum_Ico_succ_top hN]
  ring

/-- The positive current action is exactly variance of its recovered history. -/
theorem scaleInnovationHistory_variance_eq_action
    (anchor : ℝ) (r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance (scaleInnovationHistory anchor r) N =
      scaleInnovationAction r N := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [anchoredCesaroVariance_two]
      unfold scaleInnovationAction
      norm_num
  | succ N hN ih =>
      have hv := anchoredCesaroVariance_succ_sub
        (scaleInnovationHistory anchor r) hN
      have ha := scaleInnovationAction_succ_sub r hN
      rw [scaleInnovationHistory_current anchor r hN] at hv
      linarith

/-- Recovery is equivariant under an arbitrary pointwise scale-phase gauge. -/
theorem scaleInnovationGaugeCurrent_recovery
    (anchor : ℝ) (epsilon r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass
        (scaleInnovationHistory anchor (scaleInnovationGaugeCurrent epsilon r)) N =
      epsilon N * r N := by
  exact scaleInnovationHistory_current _ _ hN

/-- Positive action is invariant under every independent scale reflection. -/
theorem scaleInnovationAction_gauge_invariant
    (epsilon r : ℕ → ℝ) (hphase : ∀ k, (epsilon k) ^ (2 : ℕ) = 1) (N : ℕ) :
    scaleInnovationAction (scaleInnovationGaugeCurrent epsilon r) N =
      scaleInnovationAction r N := by
  unfold scaleInnovationAction
  apply Finset.sum_congr rfl
  intro k hk
  rw [scaleInnovationGaugeCurrent]
  rw [mul_pow, hphase]
  ring

/-- Recovered-history variance descends through the full local phase quotient. -/
theorem scaleInnovationHistory_variance_gauge_invariant
    (anchor : ℝ) (epsilon r : ℕ → ℝ)
    (hphase : ∀ k, (epsilon k) ^ (2 : ℕ) = 1) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance
        (scaleInnovationHistory anchor (scaleInnovationGaugeCurrent epsilon r)) N =
      anchoredCesaroVariance (scaleInnovationHistory anchor r) N := by
  rw [scaleInnovationHistory_variance_eq_action _ _ hN,
    scaleInnovationHistory_variance_eq_action _ _ hN,
    scaleInnovationAction_gauge_invariant epsilon r hphase]

/-- A one-site reflection is an admissible pointwise phase gauge. -/
theorem scaleInnovationSingleFlip_sq (m N : ℕ) :
    (scaleInnovationSingleFlip m N) ^ (2 : ℕ) = 1 := by
  simp [scaleInnovationSingleFlip]

/-- A one-site reflection changes recovered history whenever that innovation is nonzero. -/
theorem scaleInnovationSingleFlip_history_ne
    (anchor : ℝ) (r : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (hr : r m ≠ 0) :
    scaleInnovationHistory anchor
        (scaleInnovationGaugeCurrent (scaleInnovationSingleFlip m) r) ≠
      scaleInnovationHistory anchor r := by
  intro hhistory
  have hcurrent := congrArg
    (fun a => anchoredCesaroHighPass a m) hhistory
  rw [scaleInnovationGaugeCurrent_recovery _ _ _ hm,
    scaleInnovationHistory_current _ _ hm] at hcurrent
  simp [scaleInnovationSingleFlip] at hcurrent
  exact hr (by linarith)

/-- One anchored phase and all intervening adjacent holonomies reconstruct the endpoint phase. -/
theorem scaleInnovationGauge_eq_of_holonomy
    (epsilon delta : ℕ → ℝ) {K n : ℕ} (hKn : K ≤ n)
    (hbase : epsilon K = delta K)
    (hphase : ∀ j, K ≤ j → (epsilon j) ^ (2 : ℕ) = 1)
    (hholonomy : ∀ j, K ≤ j → j < n →
      scaleInnovationGaugeHolonomy epsilon j =
        scaleInnovationGaugeHolonomy delta j) :
    epsilon n = delta n := by
  induction n, hKn using Nat.le_induction with
  | base => exact hbase
  | succ n hKn ih =>
      have ih' : epsilon n = delta n :=
        ih (fun j hjK hjn => hholonomy j hjK (by omega))
      have hh := hholonomy n hKn (by omega)
      have heps : epsilon n ≠ 0 := by
        intro hz
        have := hphase n hKn
        rw [hz] at this
        norm_num at this
      rw [scaleInnovationGaugeHolonomy,
        scaleInnovationGaugeHolonomy, ← ih'] at hh
      exact mul_right_cancel₀ heps hh

/-- Constant local reflection: the functional-equation sign inside the full pointwise gauge. -/
def scaleInnovationConstantReflection : ℕ → ℝ := fun _ => -1

/-- Global reflection of every phase in a local gauge. -/
def scaleInnovationGaugeGlobalReflect (epsilon : ℕ → ℝ) (N : ℕ) : ℝ :=
  -epsilon N

@[simp]
theorem scaleInnovationConstantReflection_sq (N : ℕ) :
    (scaleInnovationConstantReflection N) ^ (2 : ℕ) = 1 := by
  simp [scaleInnovationConstantReflection]

/-- Functional-equation reflection is exactly the constant `-1` subgroup action on currents. -/
theorem scaleInnovationConstantReflection_current (r : ℕ → ℝ) :
    scaleInnovationGaugeCurrent scaleInnovationConstantReflection r = fun N => -r N := by
  funext N
  simp [scaleInnovationGaugeCurrent, scaleInnovationConstantReflection]

/-- Global reflection preserves admissibility of every pointwise sign gauge. -/
theorem scaleInnovationGaugeGlobalReflect_sq
    (epsilon : ℕ → ℝ) (hphase : ∀ N, (epsilon N) ^ (2 : ℕ) = 1) (N : ℕ) :
    (scaleInnovationGaugeGlobalReflect epsilon N) ^ (2 : ℕ) = 1 := by
  simp [scaleInnovationGaugeGlobalReflect, hphase]

/-- Global functional-equation reflection changes every local phase sign but fixes all adjacent
parallel-transport holonomies. -/
theorem scaleInnovationGaugeHolonomy_globalReflect
    (epsilon : ℕ → ℝ) (N : ℕ) :
    scaleInnovationGaugeHolonomy (scaleInnovationGaugeGlobalReflect epsilon) N =
      scaleInnovationGaugeHolonomy epsilon N := by
  simp [scaleInnovationGaugeHolonomy, scaleInnovationGaugeGlobalReflect]

/-- One anchor phase and the complete adjacent holonomy connection determine a sign gauge. -/
theorem scaleInnovationGauge_ext_of_base_holonomy
    (epsilon delta : ℕ → ℝ)
    (hbase : epsilon 0 = delta 0)
    (hphase : ∀ j, (epsilon j) ^ (2 : ℕ) = 1)
    (hholonomy : ∀ j,
      scaleInnovationGaugeHolonomy epsilon j =
        scaleInnovationGaugeHolonomy delta j) :
    epsilon = delta := by
  funext n
  exact scaleInnovationGauge_eq_of_holonomy epsilon delta (Nat.zero_le n) hbase
    (fun j _ => hphase j) (fun j _ _ => hholonomy j)

/-- Zero-argument certificate for anchored reconstruction, positive local-gauge quotient, strict
one-site nonfaithfulness, and orientation connection. -/
theorem scaleInnovationPhaseGauge_certificate :
    (∀ (anchor : ℝ) (r : ℕ → ℝ) (N : ℕ), 2 ≤ N →
      anchoredCesaroPotential (scaleInnovationHistory anchor r) N =
        scaleInnovationPotential anchor r N ∧
      anchoredCesaroHighPass (scaleInnovationHistory anchor r) N = r N) ∧
    (∀ (a : ℕ → ℝ) (n : ℕ), 2 ≤ n →
      scaleInnovationHistory (a 2) (anchoredCesaroHighPass a) n = a n) ∧
    (∀ (anchor : ℝ) (r : ℕ → ℝ) (N : ℕ), 2 ≤ N →
      anchoredCesaroVariance (scaleInnovationHistory anchor r) N =
        scaleInnovationAction r N ∧
      scaleInnovationAction r (N + 1) - scaleInnovationAction r N =
        ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) * (r N) ^ (2 : ℕ)) ∧
    (∀ (anchor : ℝ) (epsilon r : ℕ → ℝ) (N : ℕ),
      (∀ k, (epsilon k) ^ (2 : ℕ) = 1) → 2 ≤ N →
      anchoredCesaroHighPass
          (scaleInnovationHistory anchor (scaleInnovationGaugeCurrent epsilon r)) N =
        epsilon N * r N ∧
      anchoredCesaroVariance
          (scaleInnovationHistory anchor (scaleInnovationGaugeCurrent epsilon r)) N =
        anchoredCesaroVariance (scaleInnovationHistory anchor r) N) ∧
    (∀ (anchor : ℝ) (r : ℕ → ℝ) (m : ℕ), 2 ≤ m → r m ≠ 0 →
      scaleInnovationHistory anchor
          (scaleInnovationGaugeCurrent (scaleInnovationSingleFlip m) r) ≠
        scaleInnovationHistory anchor r) ∧
    (∀ (epsilon delta : ℕ → ℝ),
      epsilon 0 = delta 0 →
      (∀ j, (epsilon j) ^ (2 : ℕ) = 1) →
      (∀ j, scaleInnovationGaugeHolonomy epsilon j =
        scaleInnovationGaugeHolonomy delta j) →
      epsilon = delta) ∧
    (∀ r : ℕ → ℝ,
      scaleInnovationGaugeCurrent scaleInnovationConstantReflection r =
        fun N => -r N) ∧
    (∀ (epsilon : ℕ → ℝ) (N : ℕ),
      scaleInnovationGaugeHolonomy (scaleInnovationGaugeGlobalReflect epsilon) N =
        scaleInnovationGaugeHolonomy epsilon N) := by
  exact ⟨fun anchor r N hN =>
      ⟨scaleInnovationHistory_potential anchor r hN,
        scaleInnovationHistory_current anchor r hN⟩,
    scaleInnovationHistory_reconstructs,
    fun anchor r N hN =>
      ⟨scaleInnovationHistory_variance_eq_action anchor r hN,
        scaleInnovationAction_succ_sub r hN⟩,
    fun anchor epsilon r N hphase hN =>
      ⟨scaleInnovationGaugeCurrent_recovery anchor epsilon r hN,
        scaleInnovationHistory_variance_gauge_invariant anchor epsilon r hphase hN⟩,
    fun anchor r m hm hr => scaleInnovationSingleFlip_history_ne anchor r hm hr,
    scaleInnovationGauge_ext_of_base_holonomy,
    scaleInnovationConstantReflection_current,
    scaleInnovationGaugeHolonomy_globalReflect⟩

end

end GaloisForLFunctions.HTGeometry
