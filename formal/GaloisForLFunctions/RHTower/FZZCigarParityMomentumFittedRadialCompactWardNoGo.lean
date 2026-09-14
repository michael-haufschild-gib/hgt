import GaloisForLFunctions.RHTower.FZZCigarMarkedRadialReplicaResponse
import GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedSourceContact

/-!
# Momentum-fitted radial/compact FZZ Ward cancellation no-go

The literal radial replica insertion has an exact mixed momentum response.  The independently
marked opposite-winding source has an exact compact annular mixed response.  Their sum is the
minimal factorized integrated mixed Ward candidate retaining both radial backreaction and
cross-charge position dependence.

At every physical cigar level, the opposite-winding contact coefficient is strictly negative.
Consequently, for every radial momentum there is exactly one annular log-separation at which the
two literal responses cancel.  Existential Ward cancellation with momentum-fitted source geometry
is therefore universal and cannot select zero momentum.

This kills the FZZ-P chain

`momentum-fitted radial/compact cancellation -> zero radial momentum -> torus passivity ->
Mellin completeness -> RH`.

The sharp positive survivor is the unique cancelling separation.  Any viable integrated Ward
producer must fix compact separation (and phase frame) independently of the target momentum.

`[NEW] [SOURCE-EXACT FACTORS] [CROSS-CHARGE] [UNIQUE CANCELLATION] [SHARP NO-GO]
[POSITIVE SURVIVOR] [LEAN-PROVED]`
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Compact opposite-winding mixed response of the independently marked annular source. -/
def fzzOppositeWindingCompactMixedResponse
    (levelLog separation : ℝ) : ℝ :=
  deriv (fun e => deriv (fun d =>
    Real.log (fzzTwoMarkedAnnularIntegral levelLog separation d e) -
      Real.log (fzzTwoMarkedAnnularIntegral levelLog 0 d e)) 0) 0

/-- Exact cross-charge compact response, including physical finite-level contact weight. -/
theorem fzzOppositeWindingCompactMixedResponse_eq
    (levelLog separation : ℝ) :
    fzzOppositeWindingCompactMixedResponse levelLog separation =
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel levelLog) (-1) * separation := by
  exact fzzTwoMarkedAnnularIntegral_mixedLogRatio levelLog separation 0 0

/-- Opposite-winding two-mark contact is nonzero with fixed negative orientation at every
physical cigar level. -/
theorem fzzTwoMarkedOppositeContact_neg (levelLog : ℝ) :
    fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel levelLog) (-1) < 0 := by
  have hk : 2 < fzzTwoMarkedPhysicalLevel levelLog :=
    fzzTwoMarkedPhysicalLevel_gt_two levelLog
  have hk0 : 0 < fzzTwoMarkedPhysicalLevel levelLog := lt_trans (by norm_num) hk
  have hd : 0 < fzzTwoMarkedPhysicalLevel levelLog - 2 := sub_pos.mpr hk
  unfold fzzTwoMarkedContact
  have hleft : fzzTwoMarkedPhysicalLevel levelLog * (-1) / 2 < 0 := by
    nlinarith
  have hright : 0 < fzzTwoMarkedPhysicalLevel levelLog ^ 2 /
      (2 * (fzzTwoMarkedPhysicalLevel levelLog - 2)) := by
    positivity
  linarith

/-- Minimal literal mixed Ward defect: radial replica--momentum response plus compact
opposite-winding two-mark response. -/
def fzzRadialCompactMixedWardDefect
    (radialCoupling radialScale levelLog momentum separation : ℝ) : ℝ :=
  (deriv (fzzMarkedRadialReplicaPairedResponse radialCoupling radialScale) momentum).re +
    fzzOppositeWindingCompactMixedResponse levelLog separation

theorem fzzRadialCompactMixedWardDefect_eq
    (radialCoupling radialScale levelLog momentum separation : ℝ) :
    fzzRadialCompactMixedWardDefect
        radialCoupling radialScale levelLog momentum separation =
      (deriv (fzzMarkedRadialReplicaPairedResponse
        radialCoupling radialScale) momentum).re +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel levelLog) (-1) * separation := by
  rw [fzzRadialCompactMixedWardDefect,
    fzzOppositeWindingCompactMixedResponse_eq]

/-- Unique compact log-separation cancelling the literal radial mixed response. -/
def fzzRadialCompactWardCancellingSeparation
    (radialCoupling radialScale levelLog momentum : ℝ) : ℝ :=
  -(deriv (fzzMarkedRadialReplicaPairedResponse
      radialCoupling radialScale) momentum).re /
    fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel levelLog) (-1)

/-- Exact positive survivor: Ward cancellation is equivalent to one source-geometry value. -/
theorem fzzRadialCompactMixedWardDefect_eq_zero_iff
    (radialCoupling radialScale levelLog momentum separation : ℝ) :
    fzzRadialCompactMixedWardDefect
        radialCoupling radialScale levelLog momentum separation = 0 ↔
      separation = fzzRadialCompactWardCancellingSeparation
        radialCoupling radialScale levelLog momentum := by
  rw [fzzRadialCompactMixedWardDefect_eq]
  unfold fzzRadialCompactWardCancellingSeparation
  have hc : fzzTwoMarkedContact
      (fzzTwoMarkedPhysicalLevel levelLog) (-1) ≠ 0 :=
    ne_of_lt (fzzTwoMarkedOppositeContact_neg levelLog)
  constructor
  · intro h
    apply (eq_div_iff hc).2
    calc
      separation * fzzTwoMarkedContact
          (fzzTwoMarkedPhysicalLevel levelLog) (-1) =
          fzzTwoMarkedContact
            (fzzTwoMarkedPhysicalLevel levelLog) (-1) * separation := by ring
      _ = -(deriv (fzzMarkedRadialReplicaPairedResponse
            radialCoupling radialScale) momentum).re := by linarith
  · intro h
    rw [h]
    field_simp [hc]
    ring

/-- Every momentum has exactly one compact separation producing mixed Ward cancellation. -/
theorem existsUnique_fzzRadialCompactMixedWardDefect_eq_zero
    (radialCoupling radialScale levelLog momentum : ℝ) :
    ∃! separation : ℝ,
      fzzRadialCompactMixedWardDefect
        radialCoupling radialScale levelLog momentum separation = 0 := by
  refine ⟨fzzRadialCompactWardCancellingSeparation
    radialCoupling radialScale levelLog momentum, ?_, ?_⟩
  · exact (fzzRadialCompactMixedWardDefect_eq_zero_iff
      radialCoupling radialScale levelLog momentum _).2 rfl
  · intro separation hseparation
    exact (fzzRadialCompactMixedWardDefect_eq_zero_iff
      radialCoupling radialScale levelLog momentum separation).1 hseparation

/-- At zero momentum, a source-fixed compact response cancels the radial receiver only at zero
relative separation. -/
theorem fzzRadialCompactMixedWardDefect_zeroMomentum_eq_zero_iff
    (radialCoupling radialScale levelLog separation : ℝ) :
    fzzRadialCompactMixedWardDefect
        radialCoupling radialScale levelLog 0 separation = 0 ↔ separation = 0 := by
  have hradial : deriv
      (fzzMarkedRadialReplicaPairedResponse radialCoupling radialScale) 0 = 0 :=
    (fzzMarkedRadialReplicaPairedMixedResponse_zero_iff
      radialCoupling radialScale 0).2 rfl
  rw [fzzRadialCompactMixedWardDefect_eq, hradial, Complex.zero_re, zero_add]
  have hc : fzzTwoMarkedContact
      (fzzTwoMarkedPhysicalLevel levelLog) (-1) ≠ 0 :=
    ne_of_lt (fzzTwoMarkedOppositeContact_neg levelLog)
  simp only [mul_eq_zero, hc, false_or]

/-- Closed route class: allowing compact source geometry to depend on momentum makes existence of
an integrated radial/compact Ward cancellation true at every momentum, so it cannot select the
zero-momentum wall required by FZZ-P. -/
def FZZMomentumFittedRadialCompactWardRouteKilled : Prop :=
  (∀ radialCoupling radialScale levelLog momentum : ℝ,
      ∃! separation : ℝ,
        fzzRadialCompactMixedWardDefect
          radialCoupling radialScale levelLog momentum separation = 0) ∧
    ∀ radialCoupling radialScale levelLog : ℝ,
      ¬ ∀ momentum : ℝ,
        (∃ separation : ℝ,
          fzzRadialCompactMixedWardDefect
            radialCoupling radialScale levelLog momentum separation = 0) ↔
          momentum = 0

/-- **FZZ-P route kill.** Momentum-fitted compact geometry makes mixed Ward cancellation
universal, not critical-wall selective. -/
theorem fzzMomentumFittedRadialCompactWardRouteKilled :
    FZZMomentumFittedRadialCompactWardRouteKilled := by
  constructor
  · exact existsUnique_fzzRadialCompactMixedWardDefect_eq_zero
  · intro radialCoupling radialScale levelLog hselector
    have hexists : ∃ separation : ℝ,
        fzzRadialCompactMixedWardDefect
          radialCoupling radialScale levelLog 1 separation = 0 :=
      (existsUnique_fzzRadialCompactMixedWardDefect_eq_zero
        radialCoupling radialScale levelLog 1).exists
    have hone : (1 : ℝ) = 0 := (hselector 1).1 hexists
    norm_num at hone

end

end GaloisForLFunctions.RHTower
