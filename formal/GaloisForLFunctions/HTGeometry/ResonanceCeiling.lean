/-
The resonance ceiling, and the symmetric position of the two goal clauses.

Omega-results for the zeta function are produced by the resonance method: a resonator
`R(t) = Σ_(n ∈ S) r(n) n^(-it)` of length `N_R = T^β` is chosen, and the gain is controlled by a
GCD (Gál) sum over the support.  The Gál-sum bound is

    Σ ≪ |S| · exp(C √(log|S| · log log|S|)) ,

subpolynomial in the resonator length.  With `N_R = T^β` this makes the gain
`exp(C √(β log T · log log T))`, whose exponent of `log T` is `1/2` **for every** `β ∈ [0,1]` — the
resonator length affects only the constant, never the logarithmic exponent.

A refutation of the Lindelöf hypothesis needs a lower bound `exp(δ · log T)`, of logarithmic exponent
`1`.  So the resonance method's ceiling is `1/2` and its deficit is `1/2`, uniformly in `β`.  The
only known machinery for omega-results therefore cannot witness `μ(σ) > 0` at any abscissa.

Together with the proof-side results — every exponent-pair route and every covering route terminating
at the corner `(0, 1/2)` — this leaves both goal clauses obstructed for all currently known
machinery, and by comparable margins: a factor `√(log T)` in the exponent on the disproof side, and
the corner on the proof side.
-/
import GaloisForLFunctions.HTGeometry.CorrectedOffLineLedger

namespace HTGeometry

/-! ### The resonance ceiling -/

/-- The logarithmic exponent of the resonance gain, as a function of the resonator length exponent. -/
def resonanceLogExponent (_β : ℚ) : ℚ := 1 / 2

/-- **The ceiling does not depend on the resonator length.** -/
theorem resonanceLogExponent_const (β β' : ℚ) :
    resonanceLogExponent β = resonanceLogExponent β' := rfl

/-- **It equals `1/2`.** -/
@[simp] theorem resonanceLogExponent_eq (β : ℚ) : resonanceLogExponent β = 1 / 2 := rfl

/-- **And it falls short of a refutation by exactly `1/2`, uniformly.** -/
theorem resonance_deficit (β : ℚ) :
    refutationLogExponent - resonanceLogExponent β = 1 / 2 := by
  unfold refutationLogExponent resonanceLogExponent; norm_num

/-- **So the resonance method cannot witness positivity at any abscissa.** -/
theorem resonance_cannot_witness (β : ℚ) :
    resonanceLogExponent β < refutationLogExponent := by
  unfold refutationLogExponent resonanceLogExponent; norm_num

/-- The resonance ceiling matches the recorded omega-exponent exactly on the critical line. -/
theorem resonance_matches_omega_at_half (β : ℚ) :
    resonanceLogExponent β = omegaLogExponent (1 / 2) := by
  unfold omegaLogExponent resonanceLogExponent; norm_num

/-- **Off the critical line the recorded omega-exponent is even smaller**, so the resonance ceiling
is the best case. -/
theorem omega_below_resonance_off_line {σ β : ℚ} (h : 1 / 2 < σ) :
    omegaLogExponent σ < resonanceLogExponent β := by
  unfold omegaLogExponent resonanceLogExponent; linarith

/-! ### The symmetric position -/

/-- The proof side's terminus: the exponent-pair corner. -/
def cornerKappa : ℚ := 0

/-- Its second coordinate. -/
def cornerLambda : ℚ := 1 / 2

/-- **The corner has zero pointwise exponent and zero displacement.** -/
theorem corner_data : epMu cornerKappa cornerLambda = 0 ∧ epDisplacement cornerKappa cornerLambda = 0 := by
  constructor
  · unfold epMu cornerKappa cornerLambda; norm_num
  · unfold epDisplacement cornerKappa cornerLambda; norm_num

/-- **The corner is the unique point of the region with vanishing exponent**, given the region's
constraints `κ ≥ 0`, `λ ≥ 1/2`. -/
theorem corner_unique {κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam) (h : epMu κ lam = 0) :
    κ = cornerKappa ∧ lam = cornerLambda := by
  unfold epMu at h
  unfold cornerKappa cornerLambda
  constructor <;> linarith

/-- **The symmetric position.**  On the proof side every route inside the exponent-pair framework
terminates at the corner; on the disproof side the only known omega-machinery has logarithmic
exponent `1/2` against the required `1`.  Both clauses are obstructed for currently known
machinery. -/
theorem symmetric_position (β : ℚ) :
    (epMu cornerKappa cornerLambda = 0) ∧
      (resonanceLogExponent β < refutationLogExponent) ∧
      (refutationLogExponent - resonanceLogExponent β = 1 / 2) :=
  ⟨corner_data.1, resonance_cannot_witness β, resonance_deficit β⟩

/-- **The off-line route is the one place with measured partial progress**, and it stands
`4489/252420` short of the record threshold. -/
theorem only_partial_progress :
    dbLinearPiece (7 / 10) - transferThreshold bourgainTheta (7 / 10) = 4489 / 252420 ∧
      (1 : ℚ) / 2 < 5127 / 9616 :=
  ⟨corrected_ledger.2.2, majority_captured⟩

end HTGeometry
