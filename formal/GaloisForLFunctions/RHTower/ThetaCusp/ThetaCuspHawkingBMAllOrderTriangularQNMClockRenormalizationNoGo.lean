import GaloisForLFunctions.HTGeometry.TriangularSolveContinuity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedCasimirModewiseQNMClockRenormalizationNoGo

/-!
# HB all-order triangular QNM clock-renormalization no-go

The actual mixed-Casimir-corrected doubled-grade Einstein--Teukolsky source is the leading forcing
in a general formal QNM perturbation hierarchy.  At order `k`, allow an arbitrary nonlinear
remainder depending only on strictly earlier frequency shifts.  The normalized derivative of the
simple Birmingham--Mokhtari Jost zero is the common nonzero diagonal.

Strong recursion then gives a unique correction tower on every Xi fibre, at every formal order.
Its leading term is exactly the physical counterterm already forced by the reduced chiral source.
Consequently every tilted fibre has a fully solvable hierarchy with a nonzero leading shift and an
extinguished returned Evans determinant.  Under the minimal source-reduced condition, the entire
correction tower is zero exactly on the critical wall and globally exactly under RH.

Thus arbitrary finite truncations and the full formal all-order triangular QNM-solvability class
are nonselective HB producers.  Any survivor must independently forbid frequency renormalization or
leave the simple-pole/history-local class through a genuinely non-triangular resonance collision.

`[NEW] [HB] [ALL-ORDER QNM] [TRIANGULAR CLASSIFICATION] [PRODUCER NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- At order `k`, the nonlinear remainder depends only on lower-order clock shifts. -/
def D4BMMixedCasimirQNMHistoryLocal
    (L : ℕ → (ℕ → ℂ) → ℂ) : Prop :=
  ∀ (k : ℕ) (v v' : ℕ → ℂ),
    (∀ j, j < k → v j = v' j) → L k v = L k v'

/-- Zeroth-order remainder is the literal corrected Einstein--Teukolsky source. -/
def D4BMMixedCasimirQNMLiteralSeeded
    (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ) : Prop :=
  ∀ v, L 0 v = d4BMMixedCasimirReducedSecondOrderChiralSource q

/-- A dark literal source leaves no higher forcing on the zero correction history. -/
def D4BMMixedCasimirQNMSourceReduced
    (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ) : Prop :=
  d4BMMixedCasimirReducedSecondOrderChiralSource q = 0 →
    ∀ k, L k 0 = 0

/-- Canonical all-order modewise QNM clock correction, obtained by triangular recursion. -/
def d4BMMixedCasimirAllOrderQNMClockTower
    (n : ℕ) (_q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ) : ℕ → ℂ :=
  GaloisForLFunctions.HTGeometry.triangularSolve
    (teukolskyNormalizedJostOmegaDerivative n) L 0

theorem d4BMMixedCasimirAllOrderQNMClockTower_eq
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ) (k : ℕ) :
    d4BMMixedCasimirAllOrderQNMClockTower n q L k =
      (0 - L k (fun j => if _ : j < k then
          d4BMMixedCasimirAllOrderQNMClockTower n q L j else 0)) /
        teukolskyNormalizedJostOmegaDerivative n := by
  exact GaloisForLFunctions.HTGeometry.triangularSolve_eq
    (teukolskyNormalizedJostOmegaDerivative n) L 0 k

theorem d4BMMixedCasimirAllOrderQNMClockTower_spec
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : D4BMMixedCasimirQNMHistoryLocal L) (k : ℕ) :
    teukolskyNormalizedJostOmegaDerivative n *
          d4BMMixedCasimirAllOrderQNMClockTower n q L k +
        L k (d4BMMixedCasimirAllOrderQNMClockTower n q L) = 0 := by
  exact GaloisForLFunctions.HTGeometry.triangularSolve_spec
    (teukolskyNormalizedJostOmegaDerivative_ne_zero n) L hL 0 k

theorem d4BMMixedCasimirAllOrderQNMClockTower_unique
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : D4BMMixedCasimirQNMHistoryLocal L) (delta : ℕ → ℂ) :
    (∀ k,
      teukolskyNormalizedJostOmegaDerivative n * delta k + L k delta = 0) ↔
      delta = d4BMMixedCasimirAllOrderQNMClockTower n q L := by
  constructor
  · intro h
    funext k
    exact GaloisForLFunctions.HTGeometry.triangularSolve_unique
      (teukolskyNormalizedJostOmegaDerivative_ne_zero n) L hL 0 delta h k
  · rintro rfl
    exact d4BMMixedCasimirAllOrderQNMClockTower_spec n q L hL

/-- Every history-local hierarchy has exactly one all-order solution on every Xi fibre. -/
theorem existsUnique_d4BMMixedCasimirAllOrderQNMClockTower
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : D4BMMixedCasimirQNMHistoryLocal L) :
    ∃! delta : ℕ → ℂ, ∀ k,
      teukolskyNormalizedJostOmegaDerivative n * delta k + L k delta = 0 := by
  refine ⟨d4BMMixedCasimirAllOrderQNMClockTower n q L,
    d4BMMixedCasimirAllOrderQNMClockTower_spec n q L hL, ?_⟩
  intro delta hdelta
  exact (d4BMMixedCasimirAllOrderQNMClockTower_unique n q L hL delta).mp hdelta

/-- The tower's leading shift is the unique physical BM source counterterm. -/
theorem d4BMMixedCasimirAllOrderQNMClockTower_zero_eq_counterterm
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hseed : D4BMMixedCasimirQNMLiteralSeeded q L) :
    d4BMMixedCasimirAllOrderQNMClockTower n q L 0 =
      d4BMMixedCasimirModewiseQNMClockCounterterm n q := by
  rw [d4BMMixedCasimirAllOrderQNMClockTower_eq, hseed]
  simp [d4BMMixedCasimirModewiseQNMClockCounterterm]

/-- The full source-reduced correction tower is zero exactly on the critical wall. -/
theorem forall_d4BMMixedCasimirAllOrderQNMClockTower_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (_hL : D4BMMixedCasimirQNMHistoryLocal L)
    (hseed : D4BMMixedCasimirQNMLiteralSeeded q L)
    (hdark : D4BMMixedCasimirQNMSourceReduced q L) :
    (∀ k, d4BMMixedCasimirAllOrderQNMClockTower n q L k = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    rw [d4BMMixedCasimirAllOrderQNMClockTower_zero_eq_counterterm n q L hseed,
      d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff] at h0
    exact h0
  · intro hwall
    have hsource : d4BMMixedCasimirReducedSecondOrderChiralSource q = 0 :=
      (d4BMMixedCasimirReducedSecondOrderChiralSource_eq_zero_iff q).mpr hwall
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        rw [d4BMMixedCasimirAllOrderQNMClockTower_eq]
        have hhistory :
            (fun j => if _ : j < k then
                d4BMMixedCasimirAllOrderQNMClockTower n q L j else 0) = 0 := by
          funext j
          by_cases hj : j < k
          · rw [dif_pos hj, ih j hj]
            rfl
          · rw [dif_neg hj]
            rfl
        rw [hhistory, hdark hsource k]
        simp

/-- Global all-order standard-clock rigidity is exactly RH. -/
theorem forall_d4BMMixedCasimirAllOrderQNMClockTower_allXi_eq_zero_iff_rh
    (n : ℕ) (L : XiZeroCopy → ℕ → (ℕ → ℂ) → ℂ)
    (hL : ∀ q, D4BMMixedCasimirQNMHistoryLocal (L q))
    (hseed : ∀ q, D4BMMixedCasimirQNMLiteralSeeded q (L q))
    (hdark : ∀ q, D4BMMixedCasimirQNMSourceReduced q (L q)) :
    (∀ q k, d4BMMixedCasimirAllOrderQNMClockTower n q (L q) k = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff_rh n).mp
    intro q
    rw [← d4BMMixedCasimirAllOrderQNMClockTower_zero_eq_counterterm n q (L q) (hseed q)]
    exact h q 0
  · intro hRH q k
    apply (forall_d4BMMixedCasimirAllOrderQNMClockTower_eq_zero_iff
      n q (L q) (hL q) (hseed q) (hdark q)).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Tilted fibres have a nonzero leading correction while every formal hierarchy equation holds. -/
theorem d4BMMixedCasimirAllOrderQNMClockTower_offLine_brightSolvability
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hL : D4BMMixedCasimirQNMHistoryLocal L)
    (hseed : D4BMMixedCasimirQNMLiteralSeeded q L)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMMixedCasimirAllOrderQNMClockTower n q L 0 ≠ 0 ∧
      ∀ k,
        teukolskyNormalizedJostOmegaDerivative n *
              d4BMMixedCasimirAllOrderQNMClockTower n q L k +
            L k (d4BMMixedCasimirAllOrderQNMClockTower n q L) = 0 := by
  constructor
  · rw [d4BMMixedCasimirAllOrderQNMClockTower_zero_eq_counterterm n q L hseed]
    exact (d4BMMixedCasimirModewiseQNMClockCounterterm_eq_zero_iff n q).not.mpr hoff
  · exact d4BMMixedCasimirAllOrderQNMClockTower_spec n q L hL

/-- Leading returned cross source corrected by the all-order tower's zeroth coefficient. -/
def d4BMMixedCasimirAllOrderClockRenormalizedCrossSource
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ) (z : ℂ) : ℂ :=
  d4ThetaReducedSecondOrderChiralTeukolskyCrossSource
      d4BMMixedCasimirCorrectedActualScalarSeed 0 0 q z +
    d4BMMixedCasimirAllOrderQNMClockTower n q L 0 *
      teukolskyNormalizedJostOmegaDerivative n

theorem d4BMMixedCasimirAllOrderClockRenormalizedCrossSource_xi_eq_zero
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hseed : D4BMMixedCasimirQNMLiteralSeeded q L) :
    d4BMMixedCasimirAllOrderClockRenormalizedCrossSource n q L
        (xiSpectralPoint q) = 0 := by
  rw [d4BMMixedCasimirAllOrderClockRenormalizedCrossSource,
    d4BMMixedCasimirAllOrderQNMClockTower_zero_eq_counterterm n q L hseed]
  exact d4BMMixedCasimirModewiseClockRenormalizedCrossSource_xi_eq_zero n q

def d4BMMixedCasimirAllOrderClockRenormalizedReturnedJost
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (horizonPhase : ℂ → ℂ) (omega : ℂ) : ℂ → ℂ :=
  teukolskyReturnedJostWithHorizonPhase omega horizonPhase
    (d4BMMixedCasimirAllOrderClockRenormalizedCrossSource n q L)

/-- Every all-order tower extinguishes the exact leading Evans return on its Xi QNM. -/
theorem d4BMMixedCasimirAllOrderClockRenormalizedReturnDeterminant_qnmPlus_eq_zero
    (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
    (hseed : D4BMMixedCasimirQNMLiteralSeeded q L)
    (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (d4BMMixedCasimirAllOrderClockRenormalizedReturnedJost
          n q L horizonPhase
            (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
        (xiSpectralPoint q) = 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus,
    d4BMMixedCasimirAllOrderClockRenormalizedReturnedJost,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus,
    d4BMMixedCasimirAllOrderClockRenormalizedCrossSource_xi_eq_zero n q L hseed,
    zero_mul]

/-- Closed class-level certificate for all-order triangular QNM-solvability nonselection. -/
def D4BMMixedCasimirAllOrderTriangularQNMClockRenormalizationNoGo : Prop :=
  (∀ (n : ℕ) (_q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ),
    D4BMMixedCasimirQNMHistoryLocal L →
      ∃! delta : ℕ → ℂ, ∀ k,
        teukolskyNormalizedJostOmegaDerivative n * delta k + L k delta = 0) ∧
  (∀ (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ),
    D4BMMixedCasimirQNMHistoryLocal L →
    D4BMMixedCasimirQNMLiteralSeeded q L →
    D4BMMixedCasimirQNMSourceReduced q L →
      ((∀ k, d4BMMixedCasimirAllOrderQNMClockTower n q L k = 0) ↔
        (q.1 : ℂ).re = 1 / 2)) ∧
  (∀ (n : ℕ) (L : XiZeroCopy → ℕ → (ℕ → ℂ) → ℂ),
    (∀ q, D4BMMixedCasimirQNMHistoryLocal (L q)) →
    (∀ q, D4BMMixedCasimirQNMLiteralSeeded q (L q)) →
    (∀ q, D4BMMixedCasimirQNMSourceReduced q (L q)) →
      ((∀ q k, d4BMMixedCasimirAllOrderQNMClockTower n q (L q) k = 0) ↔
        RiemannHypothesis)) ∧
  (∀ (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ),
    D4BMMixedCasimirQNMHistoryLocal L →
    D4BMMixedCasimirQNMLiteralSeeded q L →
    (q.1 : ℂ).re ≠ 1 / 2 →
      d4BMMixedCasimirAllOrderQNMClockTower n q L 0 ≠ 0 ∧
        ∀ k,
          teukolskyNormalizedJostOmegaDerivative n *
                d4BMMixedCasimirAllOrderQNMClockTower n q L k +
              L k (d4BMMixedCasimirAllOrderQNMClockTower n q L) = 0) ∧
  (∀ (n : ℕ) (q : XiZeroCopy) (L : ℕ → (ℕ → ℂ) → ℂ)
      (horizonPhase : ℂ → ℂ),
    D4BMMixedCasimirQNMLiteralSeeded q L →
      teukolskyReturnDeterminant
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          (d4BMMixedCasimirAllOrderClockRenormalizedReturnedJost
            n q L horizonPhase
              (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)))
          (xiSpectralPoint q) = 0)

/-- Premise-free Lean route kill for the full history-local formal perturbation class. -/
theorem d4BMMixedCasimirAllOrderTriangularQNMClockRenormalization_noGo :
    D4BMMixedCasimirAllOrderTriangularQNMClockRenormalizationNoGo := by
  exact ⟨
    fun n q L hL => existsUnique_d4BMMixedCasimirAllOrderQNMClockTower n q L hL,
    fun n q L hL hseed hdark =>
      forall_d4BMMixedCasimirAllOrderQNMClockTower_eq_zero_iff
        n q L hL hseed hdark,
    fun n L hL hseed hdark =>
      forall_d4BMMixedCasimirAllOrderQNMClockTower_allXi_eq_zero_iff_rh
        n L hL hseed hdark,
    fun n q L hL hseed hoff =>
      d4BMMixedCasimirAllOrderQNMClockTower_offLine_brightSolvability
        n q L hL hseed hoff,
    fun n q L horizonPhase hseed =>
      d4BMMixedCasimirAllOrderClockRenormalizedReturnDeterminant_qnmPlus_eq_zero
        n q L hseed horizonPhase⟩

end

end RHTower
